-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4461
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:41:41.73815+00:00
-- url     : https://prove2.me/submissions/7ea7d39f-e338-4069-8970-658c7090604b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 802158273 ≤ n < 802338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 802159523 1250 802158273 802158293
    0xf0e06060c0f0f0f060c0405091308161a28021b01020f04030c090608070312020c10030c09060519050304030c050a0b10080114010510020307020315040302011b050a030b0607 76
    0x70303c40c081e500c50740060202038420403440c2d40022481342c216203003038202000b007070200703e004022148010390311802000300700405045070301d04070b48804244d0003a401403922405070940302840300309000740840030501b141d1350400c15044040303400c06010910740e0b02020103006034110058a8806200f0761820070b007585d00a0000700176009180c02640e81e158151710305100c2c880d42c01e80000702030302d14219080c4000c1e200082c0040c1642d403c029043c942d4a41d41c0400ca16041c041d00005030003155040c03604a17000c0c1c05400c180300312019501c074054001d84901d0200c0e028081c6140321022081e5520544400314000c0005641041c024030b4000540032894030b446141100b40d0804a07490040640bc0188002054943c03102414203c0028896080314440c8042c041c40d040c001c141c4100c13105000005018001c00444140960107010348071001540142d80c0c031000405c0760281c02650a1040b401d41d201c00070342e81c81420440980340c140c204a900340c0c089000300b0128000e90b0f0004010000440422803c442d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 802160773 1250 802159523 802159543
    0x230f0f03010b0a0e07110a0c0b030406020706021204030e010528020a0507030c080c0d0201020606150d0608070e07020f0a1509140102030405010e0715080a181b0f0e06060c0f 76
    0x683c0980302d0401d040000d11040b08210020110740004c41c11400060908020b0323006c0b143d194260b40e84946513400c150001f80301d0314000804944c800141c1d01d0000d040785e5481d0344500d000303899000d9a10b17181e07401036174544954243c80315010709252020520048641100c40e25444a1046440d641102d540d0a40741c5412034006039400380303401c1070800643d4020800c9030441002602c00c04408191503002030360b644c10150030240316161a640f9004611610410343e440c1044940050003140e03947d074655612840b8034001e95421000c0180041c26407400060071400d5400941c0083c2420059a1038007529102c03012449040182c46103180c03400f09516090a54038403030321000059032410940340280c21512905400a91a008030400308175010700b001e2621460400790810100903070347c1e410100c005010041b440043c480710303034000c0c0c42485052800803594a000001800d5919241c080398000d9205601c1800c000b06850000a40c0c0740c1007243c09481103001c00411901c0001d8550a0f0600b4002d03109 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 802162023 1250 802160773 802160789
    0x7050709022a070b0a0509130f0905010b090103050c010c060902040c110d020d0e10170109021308010608070302060d09020d110a060503010e0a020a230301230f0f03010b0a 75
    0x440c0c1c42e18000502000c0702001511070001d03c0440d1505854024038000c04c0c0c0018144240442d2004050326841c0c0d21102d8140150001c101c08410b802c030741c00050400e008141c400750710b4004e2040d2036062903a0068140da402000800e4480400c40c011961400066422100c02d9250b01500c001605c80b40100b80750850702d9240d0400a240b10b8038110301e410315014610003107520400d00240c10a4101c0d001b400511000d44580d10144036880702940e4601c0c03c2c04a80041a499400004038011550302900f01c2c6a02c801580d06d500c4c3d6906222401da078200d0103070322610b41118904000500c4c0c680c0003403080441d100000305030300149800055100d07040e0201680c4030600c460000030513103481c940c10000303003803d4240075040d5414070810403030b2840010689440990b000480580c4140100c0c0d145070104245220360441ca1003804803108541c20031320a01039407601207001110191380d50b50303028140036409041448180501c0c800c1045184132100282c0d0155a41c10100989072200780708800900752403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 802163273 1250 802162023 802162057
    0x7030807120e0607020906011b0803042001091503051e091b030d0e120a0b15014e0c030203090606010215040311100612020310021e0705070902 63
    0x4200240803241c1c0940524803ca508009403c0142e81d6031404540004007072130103001d9034a201510200180c0400d0028005000200800c4200321480401c03407001500690035480d40c080260040d1210780941c0217103a42481041d006544845c4264040d0394011844412250260090025080012002c0d54000709a800940010b90b0881210a003480f41d100c0035001000840100580101440500300c41c03c1e100300b4000300c1300c550741d60003000015000ca4000316811480e0130001380da81c200a05d5500c100d800f180c00b0100c188884000c0015031041352040440e0490501001c15084501c214aa81c540c0900c8100d840024040c0b0f07070310700c50100e4451301500d00507645c1c00d11010703480c0781c0b0348010301c0581154042d51a0386001e80068502d9600702e503250400d0200754200c2ca502500304089402910803091034010001501403410302d240240c10b0080d011f580b50415020500800ea105903040010f050000040c800400340441d00100005400b0720300740c1e05040d4440c5015401d13030303000941084012082c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 802164523 1250 802163273 802163303
    0x150509040b0423010e100e1e130302060a0c080606092b1401090201050a0f030f0c080109051006051b0102090d08090a08010b1e041b020d021203040206090d0507030807 73
    0x898840f00b0b001d00065010b8046038a84000c4c07141443e0020700421488a49460100e4100c10340c1c0c81c03032941000428140000c5030720380f251024103a0a070007402900180320f090040b40709001e02c2e1140140041d1030b5514901c081d505e801c184840341d8000551581c10010006811808550f441540007510301d1b6000d48503500541800c10005480c846140e40200c1e900d0008468010f030f801908481046040b4200085e03c071010307040070780040541a000c43c0d205400e06456a4100d07500075501130607160029000c0226850b0344280300c2c41808107004820108008014500c04150030440402a045070240090700e01580080810522a040320301159000000704051000d4603000010a028198420007003100e06c0308080010312040d00c081a4030603445911600329140e4503540c008d1461016152078189401c040c80b0f800a41d1900345200c070740018018003040c10240300c41901124022a0001d15007400c1440c040c1c1008205009440e04854911460500200141310030000d001600d02403e8a0100c2c0e0f05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 802165773 1250 802164523 802164581
    0x1b010c141e0c0f10050d020c0106030605130b07110f01140405120f0706091509050f06011703070615150e0f092202060c010f050a1104150509040b04 65
    0x4908420005801450240b1042d459601e1080d66800d02240c101106540208080d0740c0d1b07218001007024200d000090880e0180c0c015007021040328400c0b00200072564403103580f2090b583c0c001c40000c009020b070b50049001c50748944034010303c00080c003007a5904440c014030194212060034030207400200a4100300014000d007800f00050000c078150155203407002440781014180706982c002000c46556034814020301c10454400c43d045e01c05000108031021482c10019035078400490242d1082c8150302c00420040c8104868182501114000b1824a1619500c0201504c21b00c9440441c08011480c00074064149840c140c0001d081919009401354200042c0021b02d8041002c081c003421860050200940e0318201c00b0b9400300030f250420794044414400a5801d1040704447c071115030034000218140704280c2d02a901540c92188208558400340c104000701d07005038460441d400810140304007907207000d01c0c010801c0607001400092225504400502281d20b1101c0c0c540c640020800034032001d44c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 802167023 1250 802165773 802165813
    0xf040612050f0f03041a0f0f071403040f03081605070303090f0605030f130c0f09150509040317090a0206031806070c210905040f0b03060114031b010c14 67
    0x5981e400600800070f94610115130f41c0c46944290384a03540020300c00e4404c0d80d200d40944a007000d10707140b10b0b07548022032403e201294215050940e007800e5801100701c450480002260f0459980c1540d404031149191600c140d1900000e008401d26810045007500166041c4042d00c0030710300c13a84803091028280300d150f20b00381e00c440d00400d050050401c1804000c90741101c0a5900015420340d01050f8011031921407245013180e400003855150720000800c0c00321054001092182842c0b4030b45820310765030404c100c0184c0064030040c0125040030b803900400029005499800100c0c4411603a1041190340420ba0640c403c850700c801c8800c59403040b0503182d00903c150742e001005843c0440c4010403e4a03200c8112201c1104d282280c2d041c00301e402844c500841e09a0000d00c2c1c000c00c200105014414100c0c09401108000ea00c44d0103403900119548602c40c8280302c074290050b001740415a82043d0946903041d1000720607050000d111520800243c1120300004031031140703400b4000015515804107400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 802168273 1250 802167023 802167043
    0x30302041d06010905101e0206090f06060d030810080d05070b07110c0907031805030405030d0215060913120230030c0d090f0c050f0414070e0f04061205 67
    0x112450a201d41c03680c4c0841c0351420307568125203100160b2600c180a40340b8054034104800440c2d4241c6240ba6401e0300401d640f072007444004103030782500c407113a02c3d050780328402241c0460b030110910705078030086803244103155403101894480c00a02510303209444d14004101002400007030000520200b0005c40f5884281c0204203800d00d501c41a6594402c2da89990351000014000c80c2d5290001c0e1100740300360803000c481c0095000c2003007440b2040c03e00c0d584a601a014080c00317441032041049a281c80025101207440c0c000310328807465100d9030704228100344003400003801004c1b0030384810301081580100c4207404010b0b0300248000050a03c19007000340700c400c00c1a0500c60511740d9203918000e07000c21070354484110316001356500410142c02e001010112009000e413180311210100b085526240303c019120100c60050b00a00230b01e08100559440603803103902c0c41c422502240803240074641401500500601c0002c01c06130180100d8111003260b400492140100020401805411f011032400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 802169523 1250 802168273 802168319
    0x2040b0c010f1b021f0f06030524010e04030c0606050411030f0f0c07140a050703050f0f0601050a1809021201021c0c020a170c060c0309190203060705160b010303030204 74
    0x3c526454030041c1d2144140e040005800207001c2c0c4000e000d001a03844160003c21102c0204001500c9080079070703541c0c0c507017608915031020400b41000039103c4408078034126010781c03442030142d981700d030307403c44200308100c0303084402c40e46500f40070074103036214020082001d640700e80583d16450328008401ea120300c05008041800d42070818400020241c00481c3c0044c0c0e0000010841451224455441c0005c0d544000c2c1c0360b4003460b2804030400c1804140d1024140d034070b2049820091583d5403158036054203119540d131003414803100704201c0f070014a4540c1100c0e042070300011501e8594010894500d040c409049440e54001007603074001c0d440c03250070b04801c20b4248003080091070144000c1e50701c01c10b80d6405011984400c941611904a55041b500c1c04a0a0000c2d100903003000008120103401c141c40c14205070203104450000350f074540e0031030303888150024024940343e1515070040e80e81d0307030002441e410400075054040001c41e07543c1024a0095111b0703500141d8561807c64501c003130000101394062 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 802170773 1250 802169523 802169561
    0x114040b010c0c060c0c030c0905040507060806090403030c02010b03060c0903010c080c03060607081b011a090f04080915160203071707060f030f14150102010c050412050102040b0c010f 81
    0x1003c02c4650801e81d00740c800c542000004001c0d10b05201502041d1948003c1900010203000304032044540c0115001d14494001c480140742c4582043d28040c1d01160002d80001a030000a400300b482904841250884c500000604071020f50200c1e080003404c49030862024000282c0c02460300707092040040054003850a0310040c1400740b89000c0c18400034100341d100d1240400c02c1814800180e00301c1e1011103401103803ea40c00c0106403081c2c0a04180d0204007070b0031500800651050030540d01c40e0f8449e450500b400e0981c1e0755584d48400041d00492081600100c101205d141400c0c0d0500c0141030040d0000b00035084901180704040c68285950420201c070b085601c212108902c00203000c5051b10380c2c90501c49481650410220b00400d15100100301305070030502220060503001c40e07040d004141d03840c00c00b4402e030780138001642aa0203d40c0041d0005408000800a21507142c030022a00d920900000d440c084d950711612001e50440c0c41400b18596603071100a1800b8024402d0000e1b018124070404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 802172023 1250 802170773 802170797
    0x9050403020d0f111c0e130509071208070210090f080102040806010906080d05210a050402010206060102010b06180609060f031005010212040b07060b0312041d040b181002030114040b01 81
    0x9621740d04205002c02d000d061071181407050500810a90740e08101c05400e0301c80c03c12103840c02c0006002e054482c442039003e054404128044200e4501a070720381c01c001d0140c0340400607800d03ca1240c07520300c1e103035082102100300032601e0001c030380c100341c0109900700000d038036281400301da80e0400d40180c3c442c204072072030100c041042c001b000c148520310116034245161140000c01d12054544044000c1c03440b201000c40401c04e80c2851170313102d68026070007030342142d03040d1350303140016401c9540c20b4075000ea1269042c03000c1c6600c101d03154400b43c5000380141109050005c80d0300421040c1d00000110350344590040108071443c0ca940f80b070b4400038102440100301180e40040c0d40c3c41c1601c56405901d81e07600001074100c01744107142d0081100990080d044903403101c8800c4520040d50000c0c0079841740e01c02e0b0701d00c0260401c03d500d10744c0e6004603006544400c81d500c80c2000c1c0d452225080030a48814000da034030404004c166440558000c200ca03034050380360081010208400c6414454a544c10700652200c51 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 802173273 1250 802172023 802172057
    0x31b0c19061d030102030a062d051c0f0503033c0601051b0d140c0705010e221a040c12150b0f0901110d0f0e0a09050403020d0f 56
    0x114044588504080c440070380306000d880c940b9002d01c1c031602e400d0760000040c007041e140c00c0d5001c42c01f02c8a09e480480865060f0900016507280503907a0540100da662109004a25051051010340c40891580100040c141d998168440750b200c10150303141e810110030040c0e00c540019040d1a9a50000341c00301d521403e1003a80b440c48045d42c00c5041001120b28000b1364a64041d1003211154107a00c0345901c0c44034001d14000c0c7d40d40102515442c00507034103d80d60000b090a000940381c0310500300c005800d540341403200458200503418101c0d54011140402c96045492006118400c8944204d02049010101b85003800b015951075071030b805a0b24182c252058907038090b404086d101d01c00040400c60820354031001010a096400400b0641c0780001c070f4401c7e0b02070301d03001040610340c00e8a941515400a14045407542d07003011441000c07880e00b09000a10502c0740744140e035030b208000c255070050f039141e00001f811900c0072034045002d60302403415410b080d6049920160801814a001e4840041d030004d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 802174523 1250 802173273 802173319
    0x606041503180b1906090c050d0902010302070804080a1a0f060f01110f07180b030307060c140301031a0a05070207061206170a060e03030f01030f0c08031b0c 69
    0x8020425030340d0000c140c2c540481e8201c031000160414076044403030902182591108000f0300c810f02e840e5143c200009250388942c050381d030092200e5241d0a082543c05038600340501805d901c22070426070308003e4840000d8001010304003600c50080100003a2000303180000c0491603864000140c0603031101004104201d060750b2590011050b5481046031110100683d0700d0701150b480020700340210030300b01c40e07000d5001500004490800c00c1c580c0a80030001451812030b9580c0369516055041001101c01207034454020001641062926a2800700300c0f07100021160400e030011186034020849810240310072a100942048402c41d003044a41800d0a0103075440416101d020184803142401507811044e547c0440014540d030346103800920103945041e81c40d0761804c0340480d0f0a42c030300300280c0070b00003000003a0382c402d03076240306017465a90079916200c0081c0c040300d80880c1c075a54040800701c0c00703a27014000f0300441038001405036230340825660118200340b10420814002e90b60405444011036081139 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 802175773 1250 802174523 802174559
    0xe030a02160b04091e11090f0a030302070b16240b1e10140c0106181406010503090a05070303181d06100c050613020411090102101a09010f0905060604 66
    0x84c001914000a20007144420a041c4820b080d070380313401050324020b240d48005007506031040755203011040e484000c00031103054600010b401a88001402e204444504005043c3c80c4210f0301444210203066480d24454102c48402d22200000e8201070a02080180130b0228102001c8030030f51a8030404100d8034250741070316004988214082c0690844043c014196450600604850683c2da440c01c00c0340e07103000e030801d8450681100c154081c0d8001402c401c0c03241b101c0c041034081c1100600d464410044441c0d40001d4900541c0b406045402d0000440421818004610944132902c513503043c0380e03014940758920392101c0b0b0141c00391f020040504402c402c101d42d02800c1116603548815482c602200c1c1418240710090462081500384070411800e00d4482c0c0f116442100c081c44810030112801410f80550b84441c2d0150748001e140118a0005401a84120112681151f0312000c1e2a0002d083d41c01e0030b91200f04041c1c80720a080c4112a0716015103940300c03400f5944c4502c3c091a04000e580380c066022 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 802177023 1250 802175773 802175789
    0x9120e011707031425020d09090506060c0d0201050603060105060405010801090903030b0904030c020f0d03200f0709060503010b100c03140904050406290a1e090e030a02160b04 77
    0x30700103003000e4040e03406521003041440301c00700503103000200ca0f8002400e6850450160001c410a40505480042d010003400125603c5900c0c46107440d00d17043c0a40400b40215601400c1400b8821120b4401c10107030326806060307400860355040040c1414208103043e000b06d805600104024032030390743c002041da41125050a40041e02850500782100181280c1c0100c640c0001e5480911043c075a00c9075803501c1446c004c40781158501c50402c108010000c1a00d1700901080c1c00d00000320603100170383c0d40c0c140522513910580301486800c00400d0b042407019080306552640d10034050286003002d06c2056001d040030380300a408100c1e07403030002d440d80421860080c1001455070741442043c1020040d01d8184201030014084c9081a10700b1401508040d41041d51404a414040c0c0c0a00c1c040301c0b05041d072010141c09854800d0038114103924102d00ba207007610700c0f004019000150042d072442080024804100a151500c8040000908004004664110520031141d042c01810400811030b41120312003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 802178273 1250 802177023 802177067
    0x9120e220f14010305010b0105041d1305030c0a1e170f1c06030b10061215150203032a030c09130603060204090c020609060f060a0e0a09120e01 63
    0x1490110140c980e006074075a0050908050300140c0c0c1c0180340d424141c902c034100a00c51190071200440b114001da2003220003250703c04006481d0144035001d4250418509407800e8500300c815103c04d45180d21814904002e0f51080190b102403001c0b803058504d0034074600b440840c8000080c5c65209805580619120000c040020702c0d0300c0031700c07803a8100d9444440c00b0783d10403603000380c030712511004203002e20080c0e170042c2d1417100180044500b140c03102d003625080c3e2100d0003024658040c81000300049003c03041004c881d0100800c41e80c2ca010001c8011056960017103a9914010b000c65081e042d40e0340d124000d1058145000b15940042010b0325400744c203a9009a0710b5042c40c00014090802d440e8402c06880e16140c2c02009009407500100151510700c0c40a00010715052400c0b641e81c4000c03035003545d06410810201d00e10100e911383d6190007010050040e0314258844401c100d00c54800d4a04940c15550f401c1c6810410480101c0e030324400c142403e00483c1c40b5120350001e0409d8088403cac0c2c0d00700b4650 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 802179523 1250 802178273 802178329
    0xc07050103051e0a020307030509010902011e0c050a050f0c1f0e041b020115060f080a050c1e030a0507030b031504031404090905060105060405181306020d09120e 71
    0x1441000c0b0800e04543e140c08401c0d0400740c986000035801510140002401e01002603480750b014055540b00c2030f4103a565400c4c0000050350320140710241000282004031a8104d000440c004001008c50b0720b000d01c4c05000c0034039030501340901c1e0504001704140078110002e0071b644920b1002010707031503003c02030900b0300100d0180b40020b4010302c1d049043c072001c055050000c0e60050782c158041001e0020140300d030882c1a4550030140c40c4030b030b2004900000120045c0000b1005040d940086810180d0554030301c5c2450341c0001003914500c11001c0c0090028008000c03c00c2d4080035002d241d030810a0f60030200300104804011079124410400103e030100000c0d008281094407881303c03a460080c80c1000a600d0f59120b01059014040f07546080d01d00b1700c0380400101da5450924112003c54800800c0c006024035041c0304500d0188000f01070785080e03500710440c8004545140020180300c03011a07000100034006150a03407441e14442d4455081003401c401181c10b0351280b84140480031540f03111840b9100c0b07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 802180773 1250 802179523 802179541
    0x30605030304030f1b08150c0c100e030d05011508010905071d031507050a080f150d06020c030304031101140c0d0b0d1712090109080703030209012601050f010201020c0705010305 78
    0x20545d4441e40316064400001c10710800310b0300704510651104030030419203500000749a1030191742d01f5101c4a800480c000e9003008440e41c401904504c014094034201140a40103508558090340550300010003211035400080d48200c0950151a401501300074a040c10440140488006544204440d111100c01542603900300260441480b541c10450302624102e000201180c010310034145c007007201038020071000d41c11313801b0203480352a00c544030000d50000718041010300140701c802952132315400c00480307110b004188025449280207031074a031030420b115510542142d05400e00c03d00140b00368002e0040800c408802c40f00710040403a4080351a54041c0000346050032002c900402200c550301460106c60244c81c003508658100d00c0c07003000c441e5540d401840c00c0ea190800d00400c890410005000064000c5d8003a142e45901803405c0303020418240c5e00440032041c8030b208c4122803030014004100c5803526001003200300000784000c0d8206030700c5426141c1d5a410b640142818141c80e0000036940b0a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 802182023 1250 802180773 802180793
    0xc0d08010b270d02090405010b191a0a2c13020313140313121202160b0a030f0c020106081b1813020d08070303060f030206030712020c0a03120c030605030304030f 71
    0x82e400074170181c8281041c1c50329034004c210f500190360046202c0303400c030310300541768410302c80c1180c000031042a094031580c0300700300040c2e00071388a02043c0400200b03051002c10001001e072841543d404e2012003508d9a8004004003815400c0202c070815004004015500950552081006034002c0d903140201e002c0602081c21401441e40701d180c0415001800640300411800307100809000e1560313162038004918040780c8810304032044030115484000c0811100d4140700007403440b14880e02d800503049140211004c1916050124200182e444807001d01c4a82c1c02809000c18001c40c50140d08126440c04000c22035042ca08035240b1506454400058808000c91301001080f03540180070030307040074251070700e151131b07801005003607000901d00300d40400c80c10074140041007a80c5c0c008101d00d0071640e41400445202d203011002000054081c40740c0e5403240010020458034a00c25210440a040000f09201c2120720500d030718002c060802404001580b008411074041d203820070f4591400d2945401d00120007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 802183273 1250 802182023 802182049
    0x1814090907051002030912030a080c03090106030c03051617070311030a0503040e010e07021207060c17071106060603100303080c091906120e030a0e0a0b0c0d08010b27 73
    0x550400449404a44c1c04001807801100403a40001e4205200468554a010b0500c130390010403640804100100041d07405903034400030700c50000c110182c0726514980341180d580d2084407203511040700790070801800c401c150058100d000b1203a11300007110f800c035a0b45910350f1001502400f001107000f00c85032001e0000102040d0400100c0b65150350b0303202074400c007007401d126401d20b201200c07020907215840800c485503034050a10400d42069080e46845000300441d0300c207002880901c150303951080d41c01244061080c0b800c2c0d00e44880040c0641810390a02d40300070700f014894103080003009004a8039200711401d4a03018500060a55500700110140e0301c0b4032001c0d154010740c051000c1d07015030544845002a9041603840d41300703600e010002e410a03a9035140c6000e81c240c0040c00004031207441031945d60140ca800928142034142e58170024015988400320784031603074005040c0700d032049801c0f110490040c0000c1c548ca40c0341c0000d0903034a003a00b4070340c000c000c00000c0a850b00b080e03450303845d46401000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 802184523 1250 802183273 802183279
    0x1180b150d210f03020306010f050f21071b020913050304090f200304030e191e210b0c0d0e01020d06061803020f12030c07080d181409090705 62
    0x40e010031102c45038440c4600340204000500c00309804205038441d000392805040182c55402d410441c4120595583d0000d01b480f07001c580040c8203c410f655401d40d11554034028032005404c1c035040c07885005080303080c3c03001a00c500e407000000c0c040c016100c03180c1c856440104075045072054045442c03e1400c5200359030010118a0406031006800d58042c0c0c0028000c21548004102048103190303900b11078001201c0180128480000301d00c01d03824680050060005603060280ca0640c80300a0813000005000500c0081c842001060086131107030040c880d400d060007403240101300c03150784d03c50768001001040095002800f1030395180c0051160802820581e488000b1764a075905c40d042d1a00400d518840e000c0014441c02144031644954840e410035207401424620b100c012440901148034641d13008010315120401c03100180c10010310070342000d022a20003400c03600491190041c860f00509044c007c3e80409034804000e02e200045c25910210300c26240340d0350b69a40d50700d0003030526600c0d074080e5070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 802185773 1250 802184523 802184543
    0x6380d062301031508061b0405060d0207051b1003020a0c0b01080319030b0f0402090a091407090e130201030b010909020f0a090f06020601030f06061d010801180b150d 73
    0x300406920401c62800400e0f41e0803c00c1c000301c034080d007041c01e0442c41086a03a0700400082079200b2003440400392180d01d2074070a14a07040e600c3c40410b01c20780c0310031503040100b0381c04117a103c00c210301400a00c0c840da10000e020380400140900107002c0104100f10a4241a40060040c86e80c0d805480051510354200001007683d60b5a612501e480b035110703c10180c1548512040c0b445407034001d11405202c1000038200004404d004014040254000e0710010380c860300e42003001031522024010000e860940c14802806801e10f407101405035082d42d040603c4a51514040014660418504c0da450a40928012803842111001611600c0c129000645602d00004c0c1280101030003030001e007419440c9944104419580380e9010340b070324082c0d002c1c0030300680094004102040d4a0605100e00a014140c0040c042741e40310100b2481000b0202000e0703108210400400c0896400c0c0700b110902850491010401c003890b41d0b030008200c4004001c21102c403407a0f4030098503520307981140ca0303002c1e40c0040c40345 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 802187023 1250 802185773 802185809
    0xf0b03130510090b07020a08030112031101050411011e0c0611070219050a050d050307080c1606031e1803080c0906030a1a0618010f0c06050a06380d06 66
    0x2400403c901620340c1210140412186803000807001c4119030820903182c10359083c040c56040c45d081410341170b41000040c46800e00030003420301c11940903c1c418021440826000340024113501c6d0540c841e441952052082e0300001c079000040200c2250b4070a9000070711102044401156005048010b0340021041901d41203860002c0c14040940364200d400c8081c20383c0e10404c112000c071302d054008105800511000000030400344c05082c10f03480a03001d88110304a81d00d81d4a030701140c194000070002c0d40300c0d040e811003061214044044882d021205202510030b4204003104880035107001810840040c001031001c03040403090759009030006220075581d0910f0156100504800390411440b804001048592460040215452a44103594003c000b07a54540150340c44849030013444240540081c4180003e01d962240740d204800450300021581e007003c0c1010300c4082c010032504040060014000180d0014441e00e0303005103d19040241d49a490300024005408030342d02240d03000b00e10200c40c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 802188273 1250 802187023 802187053
    0xe130f120914041e1a060a02030406081b0a080402150705100e032110050604180c02070f1a12011d13020f010c031404080304030c050a0f0b031305 64
    0x2500888202c26450402e01c9a14402c21040b90101c0c03c074405611500c0350840b5212038103411150500c0c403080074076250660100701003003080e40b10004900050b04006014070202c0d0700000000c4c2c0000d0300e60703510300000820f00a420102d01c584c44681040c440903070b002030110b5581c2c002c0c0000f4034034014082500c41c1040d1910b80c1c0e45414000130040c20741e007082c144419015002081d20310030942c200030320608008540600050480203042d00d01c079102143c5000c20309031a40c400130802080c008410a50440b40403855a080b66030007d010710454000c50810031480f14150f0740d00040d11407450094060b40e294504601d4507110701c9458a1211042100014817000c0c160f40700c84103040320303524071100e694a50780c0702c451104092800030741c40000c620300c0d18000e51140c8120850580701c0d01304902410342d512a00360a5400c2640690729030303480000d081c070030003400c40345c0b0740c0c020070003074075460225410302c515030020703400a00400701c0300700f0088001048101e1102a0403403032600941074441e920019904 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 802189523 1250 802188273 802188287
    0xa1401120609061e0c1106071704050f011a030114070909180203011104031a0108060703051e0f010501020f030f0d02220b0a03060b16020f0604030c0b0703020706090e130f12 76
    0x417940824090900a1068a80440d1a40c81017205035a46180350700c12207107545000101070005e0380d5034030501c5c003200740c1040e0074411a00240c144003034030040d14450604244c01d460a40210001c46510b450610503460340101d801001e6552824010941200605da108405007201401a40c1513080c0a4003c0c0b440e00320b03000800550f8080e031407a54801800f80081c64800000b84039400a5600110000d6a698400e0f40595040b9172a10f2038101c5010700032000b82e450711400c1e02d03400c20103803c00c001044150780400c1000d04d441d140307002541c20714008000c000c01c14000c1e14000461503400082e03800070b007100000395988a030300c1d0401c1004a9500d40044600c580c00100482020919040300841d001e04480c007a620503520003c1404060481c40c1d00344240125160000c54004800b80004800580e0400409000d8030980c802c542c7c40e0810350600a141c81c0155102c0002d010035680c0a1110300001861258004c20950140000c00307050300d8150890f0300448000b801c02003101555016840c1d003c2e02d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 802190773 1250 802189523 802189541
    0x1050a0815032e0506060a27030f05070e060136151d0a050603042406090504020f0109030b0403050307020307140303040210091508090709140a1401120609061e 70
    0x4000c200d00d80e03c0d00b050103502c7c42001c9038071010039540410078444600c0801e203010001505160340000640d2a40c0e1510415054103044456400c00c607420700940200d00041c5a01c04001d28040d0322400303404551140c01940085200880880c030403000e4a480d0306084031200402126401c0501e0041404004209581d17503003410200b0021000690f0b203a00c0c003040a9000d07150300070526032175600d881c0e03100044400c24001d9498104c1d4150381c10b0510300720610a0340d00505540501060740c0c5014410406211011450907041c0401014180085640e08400c241d02a40c503050483d40c1c5e031203e100503032850042c16002041c1a0050b0345284404070084050350241f8030035540320000d001414400d0307540e9100350140c090110b90041007485a10700c1486c003141c00102c0401602d07a01612941001c1c1030b1281c0d10928482100c00f0f20a1114220240c842e034110000415140d0b0b40342d50526114041281044a01520441d140c0c14540c051241980c0640c008412003044c84401511010300c040c0030b804441 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 802192023 1250 802190773 802190863
    0x7020304090e0a020a140a080f01020913150b030a020f1b0c01141c060806010e0f0903070804170c040507080709060306080705010c150203070e0f01050a081503 70
    0x100d140741070000081c5800f19a64020590400c02d8100420301400e4542000803903409100e28500092020b001e02042a82c90b10304400035070b480c0d142c442813100013080c00d440c480040d460300ba502036543c118050a54155030f089100d407581ca480740b40e6540701a001720200c1989102c0005040780e06900d41048a01240c03868000380c840c0008a50019500103941440d00740035000e040150300f000c0e8544455142a041e501d000c0014001c1d00d5410075441c1020981000c20038a042e001440ba00d042a043c015512410300740c01035142c41c0d92680c540ca494043c81c418090034504032b20465203040d0083c44810350f2518050400c0040b0f20b844a03004169001c01d40701d020100700d900c0008200d1078804d00a54060305c00c52401044050310708001151407945096094071010800c0c01c81e120b1202c503900045028030f010340c5d1030380540900e020400052401102491b8103000c020426000345c0e80e000b100481c1c4c0024030901208900305050046820700c080103c80e80f003400918500401824001c005c0000403031108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 802193273 1250 802192023 802192031
    0x40e01050f040c0206010e090708100f1b020c01051c1406010e031603170408100c030f090228080304030f05010e010606050706021318090303112a01140702030409 71
    0x200050204803009040000b0060f041017005000484400d012690004688021640d5650b80e40244a00344032800c416607036590b4580500d80c20441d0a4003c3d0252003203e400150a200c0f0708200c00380d9141800d066240c1071144c0482d03014880704040030380d2504892130f450180100c1c2c41e455040c540e0b203042201d200d0f0205074088540021400c0004000b606804a40c1c0201e43c1c05046458030a650b03541040782c1400e40c0307020000420702c0903050080e108000000d10300894034a00000c0c0280540b0080322800c1380d200d1508041c800507a071020703001d907030702c11084044d0b062480c4541984280c00030315811100c1144000240001044000810380c5007241c0103100820102c490700f03d90070f00340d4516210307020010308240600400700d81d5a9006111925640460030a000c0e50740b110308800401c16100000c126560b80544020f25030103000325152900b0b003501031441e09603120384440c482c542c81200803180f0709003850114600c0200b54031a92040e02c2c0b00d45010b80c1807505400c000d40d41c0e406402642002c82c28 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 802194523 1250 802193273 802193299
    0xe0c031510120327050d0b360c0d080f09040b040e031c052e0509040b091b031b03010209090112023f011506050408070807050609060a020a08040e0105 66
    0x30030203156003175510041542c045680d0303d0f00d460180100250044003072242d00703041c0c140b80b95442c05a0344100c101c0301c880c85041250074400d980c10008107101304c0d03000e8039007488510001a40c0501303c0308400031a00802d030b00d0340100c1b400b24005054224805800a20b4031010b41c00c640b800202070159000000e1604040440c404025000e5030f205071424400703032514025a0340010300000c01c0800352041502041111030351000000c4595030f0996041e503c00002200307000141e6030522110280d0050140c201012041c4000829a00c982d10b985290f140da003400c0280070f80307640030340485082a5000b4141901940c6614240707800c1501e50004a01c41d490030340c9040101d0a41509042c0d6070180c4841e0b22800341691109a061a2400d0a040c500d5559401c0c6240511003204542c1c1c025000b90340d50107446a00f0a104549020201e2300f10a00e02c0c2d004803410020781e40e8040440741c1e1000180c0e6000d40b5121007001c145e1602920f09401408414049408110031a188840504848080b01c0c14104004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 802195773 1250 802194523 802194587
    0x7230919030b06010c02060705032b0c02060601180e0a0c0e01020601030f0303020702060706091407050a0b04260304060e092206090809130f0e0c0315101203 69
    0x550303444014500760320600020159801508850380c6580042c08481c0f4111a5585850440d0700428001042c03404400b090780340c8880342800c0c003100b404007040c02c001c21003045a02075a203110041c00c1a040000b09404032100b02070440c040750041503190b00844003030400000200c09800f00c1d2541c18005541810340803c10f41c40090030714100d03600589010224503168904801960040109a810020820000c00001c03514420040700760b01420495a9212424113050b003031a6440c0d01191181142240602c20301c1603010440c0d049885900d064015a1104201c2d040d41040380000304802e4040494002074203038101000418145084445401680d102159010f902075041d24042d00c5000030a00c4000047c820390081849900840c1d0503410030002c140040c0d50f05000e01740c400e01c0740e611420404520f05450003108400003d00c3c018003a1501c2c0000403d0742d8040f4004845070030703424400482d001c0d403544103000e40135000c005140b8440e0070380c500300a0710040070440421030210a803515001c03944 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 802197023 1250 802195773 802195819
    0xe01290d0b010b0a1403040f0b010f0b0d02090a050a0602030406020708030406080c0c010f02030a090203071a121e181b10111002040f0609060201090308060108072309 73
    0x1c0d4010030a400507420305041880680040035814140424a2032009a044085014520451081c030052800746c40518146240c0034040c0d2225030040c0b1403540501401e01104141c4504000000c3e005071038040d01b40015803003413900c0d072010f41c00c04035040020521035070100042040e05d00740e80880b41c20070741d074141c06944c0344664840d9100148900b40442c503400c41c418010903052040c80004074000381500a00d6040741e006a484203403440d65a010034085081c14400714008000c02e480f164511903d40c5041d00c0e9500c03c5400c0241e054144500080851140b0020b140481a10404194280c81e0507940b44418455411050b04940300b0b40f6000c040300010403180340e15502000d840459035108010003500c0020821000c1320660241c000c610010f18107610180000304600401e400b0b00e11f00d004005000800d0390740002c011641014011404039400403c1a90048001c6c13800d540c0c035607180034084483d0400c0610001000c5080350100b41d002d00024042e140306941180e10789100203181c035181060b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 802198273 1250 802197023 802197049
    0xb240403120c03020d08190f0c0306050a08071202220522020a06080a021b01060504050c12060f0105040e04050d1d01021e120d021c0b030604060506040e0129 69
    0x16440407601480a5211b811070541086020101c0f00380348403900c00c000141c407030644152403005d6440745241d40d07959150056000401003a105030102c0c034101045a0f80340c41903801200c1151900850300d6045445d0304e01d200c031a02d0380c03181103000c04101c03402080d00507160a6542e42c0c200074050700860b0410b0700301686c1c0e500d6190b0080c03d005100380b800e101640d000c04021b05904000c0e9003448110070300e01e802c1210303505075072049000054103400c020070802245c3c0081c0c02030301144800d1001411012010700c0e030300e420901c215900803100d400382d40101ca80b4491034024010300581c2070244020010002104500d1040c44c0c3c650b41201c000000320403000803200b20380c05006900c00c2c0818008054403107002c04441c03000c0303c2540c419102031203011503039912414034002200c1c0d00240c4001c50702d610b0f141d90142500d4006013802210102c0000030390313070321018002411580d52080850705581c1c1c0d540c0100c007610083d100a002201144004030325400c1500d2016201080021001c54189440c2e03d642c2d140b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 802199523 1250 802198273 802198277
    0x30e0d0b0106140c063c0604050c04060804060207060b040609020c0d02010b030a0201120908210105030c0d030f0c0c0f0303140c0604120c051501260d030b240403120c03 74
    0x20741d03881c2d1000c0803500b505c040c50541d003070701b10760400210b082040000140907010440202200c0c1041c0e024002181c900a20aa03144601800184003643d440811240c00540048000d40c80741e4031400e02c00010188404210351142c9401c000182c502c515070060141c00399100c040d5200b10071074070720503820b0380d0302e03511803651640244164400542c0602c07070307501c2610708a840c00200c0030070641d641000ea0340a194400400c41c0025440403c040000704050701620068000d021440c10501c08078074090003060005080c45151f0b004200000d110710030f41156070b40c00c8500100803580d20030714046401d404c0d0100b540028803045400360300101410845500c60742c0301000b805a6030f5180c990b110310002c1c681c00d6800304442504108046681001040200110400c4000c02d9525208840800c2e0724540814840e003000c80e005d810794804040b401e240c0b12500d5080100c0d030107000500150b480d800290702c102049031488085000329007220040e0050381d02ca40c4040150150003101a02c03000720910f80100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 802200773 1250 802199523 802199533
    0xb07061116050f0703151806090b090609190605190911131e0228020114090a020306152e171b0f0c0f011e0903050412030e0d0b0106140c 60
    0x6c1145203170780403000c03019103c10030b442d8148260b0b42c0c2d031058840c101c5056403030003209010b00040c2e000500c00281c00010940080440c4090b1640030110146000e0000d4130240d40c640001d8200f5031401070f0700c0030502c40008200700407000380c0b0b8000700c2d0210a4407018050a010091a4511040d034410840301c020750754003002c0582c40020640020b5844200051040751582250000c80341c42241c410090904580000c113070342c02403500700040340c1170092480d181c0e90b0001e1000005030301c0105003180c1055070000c080940c04152008039407002c5002d2603504503186106442401404950300c171980141072640c0d01c1c400ca180f811075241580300700303441800c0d51005a20407045015215002041c03c6800d02c1e946909044103500500d050417a00140b03800c3c140d4407850740290003044003480b0440628001010062031003140c80050050040307006118040103025025401c0c507000390f61006c504040282860003100003840c01102c0e40f0402c0c42040c000c02e480d070049810b010307824020b440f0401300c43c0700100303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 802202023 1250 802200773 802200803
    0x2010c05031605040806100518040f14160603051b040302150306040b04020408060403140f0a0c0807050102040b0c070b0f0f0a0e120708060f01050102070b07061116050f0703 76
    0x8192100c802d0301d142c01d002041200003880383c0305101c0184641031001801c0201890300e428011082e0040b000c01040496007000c002c00507266801ca0030742980c10015540c800001c00d00024a401ca41001c4090390900310383c130002d0100e9041d000f0390b224419a0945042c0004c503000140703114000c1d800001e5010202c80110103008250002560303104a0003032002c078840341940b0104049901540142405070860b500304814980c03c40f0b03980700f80c515101c404034604003d04030514014003d0004034420003d01080301024800b45505a8100c290002c000310340d11b07985e402440c80103603c60f8103034141c14000c40500280b1001d50100b59280000c01250580c03810b133f500c803191500c0390700c80e4039110103000c480f0309020880d48a584a140100c45404c0c001d003103140c14209003c1c68850000d01c071000d0f96600b2001030080b6607011403040111860044d03059142c00803860710074041d01080c0398800e50a000850381100e4912849481000c4a0080d4296000f100508a8090701c0d4461400047e00d0040c06005030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 802203273 1250 802202023 802202041
    0x60103020a0605030a0b0d030c02030c010906140c0a02280e070f0e06130f0609140310180f0f030905010503100e1302030f0d11071505090612040c0f0602010c0503 71
    0xd41e841700c00c8841c000307820b84041c000903003030b109601004c0e0002034004404404606040215001162090820407041807601000900201c42410100940040400d8140600c00c0400c820340c140b80d4020003888517480c03c819a4200e9401d5040c070001610160744000480c1d20244c41401d0140d070703407951590b1410654004c140d40100c1d20017402508030808120340c225500d2200c6d00703400900318000101d4055864410001c210403455040040407031000c940d8056150b90015400400c4183c510012035203402107010494007020046019019091100e481e00400c4941036603616658404e84030310340b884c0d444100442d041e0108640140e00000c0111090048a191110b040d61004440c48521541000b039800f01e0b041c01c80000380c5800a5020b856a10119500310000e50001d00300038004007003580ca800481510302d501410150248640001d140301c0c50f45420013221128400c04002d41d2003401d0901d004541001c09215001d0f100e041d103040403030264410301605840c050744c0e030788050850700d0f10015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 802204523 1250 802203273 802203277
    0x2306030f040204180f0f03030b0105092119050c1c021309050c130515040c0c0308040c0b0408060603010c0801081f06091d07080a03050f090f0306011511060103020a0605 74
    0x140c03000c0201081d1000300001c1580c5d102091141c0b0030760300c01c0820f003070302c0c600035003619110803010f03050080901100d82191145080d040c0002c00820405542c01000c1440a003421945080440081080300f6110140400081c04984128040c2c1e800d07500c00e4030700354000110000c644402984826401c40100b45080c0702e400c5800000c3c000d100f5035154400801c00248000c0c181111110826150410400c4c03410310380143c5800108103031800d21080d16500c0c07005041c0c01c2080d400400703001502000c10140703e40b01c3d5401028201d00404c860b641c03a25402041d40c0c9020444000744250300b0440c041139100d2060302114101d8004800804a50050042101920310450070661403076568040c0021800c05d58041d01c1c40c4400441e94800280c0440340b030701d500302006900141b00540c4444c00e02800030354030004440e003032500000502d8450140b4400a1107164442a21070ba0521400b0004114040015080b1801da511900c8900060132005d10158489809100203940715620150820000e402500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 802205773 1250 802204523 802204541
    0x1501090308090102071e05120c030607050a020a0c0306050103061d1f02132405130e04061b0509040f060506030f060604080118021008190c0909062306030f040204 71
    0x40d201446e40b2000c0075000815071801807200518201c10812190400d000d80c05003004059029103127820007a00030a07521000680a9004c1140c00552096080d10034450101200e5009001c19501031796801c0000180c0703020b0205079021407801003108031255008d0f00003c040341c80c4401030486130411880303401c042480441140c6029400b009a078482e40c000245240140c200752955034009007640740958141982c40c5034010500030104071403810410020700380001c0b14801c621840d85a9070700e1610a024100d043c07881c4031014940007440061541001c0a040040400e071030070081c941c6401856030946005200302600240204003180c0102141c40c005a80300c0c2002d40f5207803500d5668400384e03007180c02e01180200d61400407400d440451920404d03040340da48491510144504121040740e066402c445182d10941c2e0392100039895460140490300300801c44641c00700119991100c4070401c0000b460f10038480341c1a2221101c490b454418141c0c2e0049209640c08442136070b49600340001008410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 802207023 1250 802205773 802205777
    0x1302090a140109020d0c05180d08300a09211709011e020403021c03090816180603050303071202090d03021b090c0715020c030a09030b15010903080901 66
    0x41c440500d07000415000302c0c000c0a200c2001652108180381c0b0300110744101d040d84040160400aa41106000b55810441d4500459202e4050711040c6095007407440f0301c0703000b2503202c503030610342c501540540c0140c8288001c0c8900c120030103584042ca00000c4501440f00100346803100450881040c10000044411049a01f807095056500741c144d02d2a2860449407031450769103034081d6200c1c42141046c1d02e4040084c032582035081078107540c00240300c0c0000f940d01d01140b00c442c041c11014503106014082c010000c0000391119005255030038400039110303003e1a55045001c0103140c0c0c80d00c0c507511421003102c3d0020040c508507140d0b00d80c1120b40089070803211200030307001c0c428011250b81e02c00c51214501e00c680c00801541c403a0341d1602c070b924191700c1070b110f1182c0800c1040000f80c1000404031000075a0100303012100821481055009000c0c48400300c1c0c1c1d510001c64030090301074000903ca4182c90088440f00101d40c1d404420011140c49154940d00040408008000064081c805000130307075014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 802208273 1250 802207023 802207031
    0x30c040302032e0527011b0e0a05030d0801050114070507090c1106061507020102070306150807140307090c1704060209041503120813080f190201051302090a 69
    0x940000b031824580021180c10b12001c00441444040303021101d40d0610114002440340b8503001484020070b0032a40f50170310701011135040b0074031450401c0d03001030f90302d04450170300e981d51440144000f0154a0264085030240790110008903c0740f0740003038050403080c0980e03290f0b44903a08050044400d1050400a0075101006005060004500303120807005405100d800041080b4202030080c41242d1031031210300150090003d1110b103071503100004c001c00307800c3c0b42c88507070300c60341d07440101c3c5000c00650003d0212890600c11030304040b0042030384406c0b12540011641c81130348800e1021054020071102c20381c1548403503010484038800360003041c8950060300782064103a81c10045010182c00468080b10000c3d8002200c1c00581350505c900906074952460b1100c41c54110340c0d9001444071214000001d0282c5070380021141c2c1c3c003010510355200c0e40510419114001c10805c40e0841e0000e1892444480c02030715840c0c4130a105108031482405030043c001f8070b000301034080c82141d078406801d600d561612 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 802209523 1250 802208273 802208279
    0x302030412180308030103150c0e0a060e0f0303070b01061710060e13020a0804051e0c0f03071205060601091401120e010e01020a050909010f03030c0b090c10030507090503120f030c04 80
    0x507441c042c5000f18003d02207003903231890715140c4404550b400b03000c00b420700c4500c000e030190a44032251104162611401c16007c40241c040004031004460441c1c582c1c180300010b518801c00c40881800c0341203400c1a240c407030320709a000014450400b01102c010000b80d07200310040101c5845140b049044020150941c80c80b076001ca41c07510180d91150701c0d420080781c8640240810400704020200c0c40a54a80550111002e08100c241d1107100100782e241c4034400d0028103a4441e40c080c072068000302907142001e00e0b4810f440ca0030a4844a0441e225800b060310b0303410000d0310240f01c40d004172015405a61300d5805180010b4030b40300501b00440c2e0122190350314103275140061800d100070100e00e2400c1d2243c1c0d8882c1c04003001c0202c00c40d01608030794100d00c00c00008000181e0820344001103140d12103200035981c0d80741600649042d0450704210b500c14041b01629103415099803051340524010750390000d940d621001031590f01e01009048110741e001c00c20080c8504402c0070007450304208000c0c403051400f69 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 802210773 1250 802209523 802209533
    0x60801231c03030504110103051b033718021005071518051b060a0f030213090203251418130225020609040c0507140f0d03020304121803 60
    0x1103100e01c01c6010a54480500050241402d8124001602480c0520080c0b0304800d01807885520f02c0c5a4008000000c00851040c804842c1100218006000c0440509100412480c150380c103d1614000c2285450140d80980c0c0d07021400044081d000351544c850710f07ca01108807842d034040740061701d03001a40680403140860300d0161004220070b6800c44080307007030300d400c10794182008074242401c0c240c810450480d5546401c41a2001021542480c1c1c28527801d5000c154043e2180c241910b64075070030b4090124001c00903501135070050041c0c581c4685c0c00c0c403502a81029544481801d4004101e0500c400848002004000d00c005101c003c200501c041200703010884031100303082c1c03104101e900440c540c40c07014809402c0305031080700096007a140054a40115505109842d94140120f0302c0b40542c0104900074421a2001a881403075003010020722444262200c0d07510407010100c1c01600b010100142c403a0003500c0c019500300b00c1c3c81c0d0703400440200c25102c60b289551000c070840c1d10201c00101080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 802212023 1250 802210773 802210819
    0x18030a060e0c01180b03072a14030702211005010b030403032003010e310201110a031202030a0905030a0206010e010f03260904060b120106080123 64
    0x1920901011a0001070600982d003402040894181040320203004507103526103114104048410b440c0c40c07513a0300e440d81c1c081118104589a00f01c14401d450100074048807211491581181c0e009602404070b10029040721a141d00c52180060360099000401c40305079200d404e41030701c41140710803c50f1f010450010040c03050700d400340c1c0034043d000004030070032041c0354150203442460380fd0030313512018048081681208500042c05030312210350701280000d8081a912400c1a0180460103c007002000c6014070410083c84040040340001d508400c50b100d12900042c11101e425070640311030041425038200f141c0203400040000d401d160f100c0c1100400b040050000f48150081907002e4222581030040b00381c00900c0603031040c00000d203100380400c003085520b80600200c407416401e80da50414000d43c078005600606960503171062600c034000039910340910060101d10300c0308401000c160784e94001030f14041c5091240104d64401ca00145202408050540000850081c980350180100e08505400a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 802213273 1250 802212023 802212043
    0xe0f0303010306060902030f07030b01030b0409120f031e090f0f0c030b0f0708040602030403030e07170f0c0d1b0906090b040b0d0210030b030a0203060705041a0f0406051803 76
    0x16420020040c4240100390042c14003030000c40900354a50300b8400303400209400c0041c808010159160035a4455078404c0d0402209054018402e1103165841c0c00d00c038980e95122105800441c010190300b002580c0a8005c2041c2c01c07002000350f5194000d615504406401111360454400702d104030703d90001100d10782d103074002d00d01440e40600760a0840c5011100a44040c000201e0400b285003080303c9513902c060310640c001c0d40004003603240e807110320b016000303040301c200e5800d0540148540072074400717281c0c81102d4414501900711940c04151100c01904c0704580300746a038100351142a031101058003c010b03030700c402c000f2040c0c8a080c1a03442156404940310340d04080110b0307840d60500c00851a1030301034003d55030000c41d580c00c942881e0b6400111710001e540304a8045c10b07143c42d03094139299014450986500c3d00a02a2026071038200801030036684140a000f100060308401258140c20503016107182030300809203203103810306010041d902600008454150741640058000031a20148010549 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 802214523 1250 802213273 802213303
    0x60112110a050901020f060f01051c0b16030f090215070318030c03020a0b030f0612010e010e070f0f03030f0e040b1e090c0c030412080906040f0e01050d12120e 70
    0x503440d6143c00207040502000520301d03242d0100781803003a100d20500c0b08a04556045804000401580360000d04d04414444003420740c19400e810000400304c00640d02c00c0e20242035804000345c1800a0300c0030300721140290041c0d040000307031444002c000fa5060003054142e0017070906142c015425003e00c0c040258581007216802c1c0c42c03810800031070520b115054050b1050030100c4ac01c5240c003c003031409181004244903ca0303160030801c20400c2c2c5003980b0081048204000911580a0540070789980b010310b442140100b0400610014a1482483d18202941e505a0360b8001241c902c5404861141204188603401903507028001291354071440142c0a07504460340681d4038844031001c0240f001c10081408980345802c11107108070400200441d000d95202c040820150703495402e0942c03070345c0112403001d9000030002401103024440c00045a0491320b14800107155680c0703a03001e0050b1503c9202000300301c0c44e910b64162000a0050500c54041009034100040021002003a640b0b01244c04004841c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 802215773 1250 802214523 802214527
    0x40218040f0b22060b01030b0607080301030c080d0f0503090c0d03020d02010b09010f03020409060b0d0b011a19031d06160e040903020303061309120302090f0a030b060112110a05 78
    0x41000220b0444951000340d03070b00000c0b00c1034801d03004100e155981c8400240400c1c0d0314044014168082e9000c1d10a0b00000782c400740d00c4001d18941454164401c0c08291103a0406c840d0015480b20005810f1000c2c01155a801c0c20214a00c0700549160700050519466805000c145180b03689411000000c0b0a0180d4018152628040c40182c2101ea14100c56030003910305000512104220026810032642c2c1070740d000550304502d050440081108100e49940883d0044410040c04070780e40c10241600c0003908c00101d80c440d511200241032241c0c1816a50b1198003c03154400c0c00c2c040c0e4040c401e000d00300072030460710b02006480c490034507030120341c000303d540c20025a8032941540320181d140c1512065408110006c0716460296407400010f04c41c511450032580d00018482e101d0700701060459000e4000c01d0030340349004020300650401c883c2c2d580107500c1614403040070320b00103a00c0c2c0d0489030003007030801858031741e4801145e42c2920458001e143e16164603800000c10021001041c15446940ea119 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 802217023 1250 802215773 802215803
    0x2032d0316030c0309020901051908060702030702010206010f05090f0402010e150d0c090f09020c0304080712060b040b0a03060b0d0510090309050d05120d060b160c080d02120304021804 81
    0x58111034000e550f28082614083c2c150340180c071903800700e50540710f086070070800300f0380c0c03446448106204682002200d4050b0b03100303202c0903540000203001d005100340c0030f131070441c0c0c0c0307070000e54540720213502c07030503a00003450004942c20602032420709030080e0040c9440a95002c4081c04103600c107440150104510000040e0104070a440e0721400c1d842c0000c61401e445101c0c541402005030084070300519003a580d00141103021400b080080341d00030f10100080d100303c1a600c5a82410030608074400b0341c0c015080400d42d41c0c451506103d002c00c0704c0b200600e0401c0e0141103445d2440100030100e1000c1d041603400aa000c0811f40c01c0002c14540c409112021420310940c0c50300030310040517030f03120358003419240ca081c0b000681d0100d60101c648842d10703442520703088003102c98400303080150700c6910014030000c0e10000c203d06002070b420801d80502941415543c0d03440100c1d42e503044003114100143c2007842000380211141d002590042d000510a48106500031803072049144207803070468403456004945 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 802218273 1250 802217023 802217027
    0x240507060204031b0305100e06061215040c0602010f180b10090f021b0303060330071401111e070606050405010b0c19020904020f0406030c08010c1101060602032d0316 73
    0x101f007651520b040103004d101c07500b07410756580d194003030051481014001c2cbd009100400c100b000c00303001c40b00804595440d08150030030008a040c4e60180c20015401e041c440b84104c0030b180114004024011242603c6852a88030f40c600e05d46c003e0000300038040442e0340001c0030350343c40c001d1500d608041c000059540485c1c9a0312840a080039020241903002807041110641d4049507030382d5078540d07216071540c13409031000f08800c090382844003180301600d0204400c018001902e45074641d48013118000c100c1ea04030106c400c400e6010f84114681c00700c0c0519511080d6615038005403010502c10360300481c10b02c3e00e4600003425510242c0007034240301da02040c81400500c02b00451210400c140c1040700710202d083d00810301c0c20030000c0000e4050413150003d888191201d511400055030414060f00d11240ca408225000e06080b20000d0002613813426420000c0606104042c01c807038154004610b0f04411000c450103414051940c64408100700744002c01e0642103000a522612402100303032000d01c204080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 802219523 1250 802218273 802218283
    0x1060e090c031606091802190f081509071b080a030905060718060c1e111201270807060c02060609090c010f080a02040f0f0e01240507060204031b0305 66
    0x3080d101810040320410407145c11544103010340da407442e002c030440f07800290944007034410a01e8460400501d100319000c2280d109400403010f401e1035442e20600d40754040b03010601884d110450341d000c91042d0104101d035010391410204e21115090050016911341c56103001504a0803580c404a500c902032582040010310005500001500b421600302c80002d0100140f980c10f802600c00344040c02418805010503041420000c85258001c03100711202c900e01400c00c030b9010194240990401160901119030600620840a040e0300c00020300c9882072071803034a00400900d080c0d9110303200308031031000300d0458040c032078000040e50010b001d81d08040042c440a50402454144690084001c04001d40e03848890240100d047e482c0c80310080d00c0c3d0381c041c071f80280b00d5a400b80faa4002859800500c0c0e01c02500510221080100c120a060b070381c1b032810412041400c0f60b0b540028800c60a402d071280c0c0200050149a4082d810050605449903501c0003002000c1505403603150107100d007001009400c00c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 802220773 1250 802219523 802219543
    0x3090b25050c0703120e040f0c020f0a1505061210020324180c090a031a160c032f0f07150509060318060c0d1407051b01060e090c03 58
    0xa089803521075a102d4a039215941c501000300290b80100340c003080d0720300c600004881c208004008215060034800520014510030b0311f06005070161000c0d40c0c0402d4004034510003115001b00c5415211312401d02c0b20401800d004101c940d0104900c030345001c026030104a0f851503542e11110040e41c82c14010300d45042102c620601c10400020108900e40c3c07602c030603031108411007000710303e6049a01c0700001505035005503021190030141c1c2c6000001806040840350000d9410a0321041c070f1525642500340c6402c0c1d071641d88a02054a1854100001e03116006075114440201c0d001040d406400c48440c0400300c0c0542c5d40b0303c01c4e0b0712034140b17032103a5441440807030010f0482d5058103489468070398028121b03015501210344160310120005910001003401d8200100c40c10041d1603452402c3d4074520300540012804040f058640700d000c2c65041038641550b0f0192000e51182800c10314110203007010042a019040415502d82d4000501503545644460007040010058a1820744000502d031501c01c00e16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 802222023 1250 802220773 802220777
    0x31b031618150503090703061104181109131e0506010f021c0c020a0801050702060f01150903020d14070b0a0215010f05060a02070e0c03060414090d080703090b25 71
    0x42010810103003018440400d0324a0b6062290322a41d40540781d60410b481c0c0e41c405031045051080b00b000c0c01022030003d006490454006104056501500d402161580201000441c80402c505d84140c07405401011b154108880040351a008032442e1900d15070254005440d402e031524103000c0f0395070700304041510b20074040c80107026034404400b0800e840b90040b050601405803005604041d03480d40c03500d55010381030b650700a01160070301c264003c1d5290011900000300f100d0305c2001080c0c8900343c002d01e11401c045581c0703c08003242560200100800118001ca0304482212070201d4401000c0c0030080003040d8648846481c0c00182d180070341016540d00c00742c05004101e1006118080c0d0f0100f0b250f09854003500d41c1900c4c2d1441c504140e21b448043c1c2c202d04011403150082140d0b041880004522891081d241440311803400c91441c0c0d5141425a1a00a00d070041c901c600340b043d100380c11722940031364180f4010800f11066252001104010f440e001c030740ea4140c1c64010181e54401c942c411a2580c80c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 802223273 1250 802222023 802222067
    0xb0103051306150803070c0e070c0c030611160f0b06032e020c070803030103120f05121015020102031501170408070606210c0f061202031b0316 63
    0x12219401e01000402001000700d80e81e0201c800e90440c1c60701c00c6002a000c100c0849641352158241142a84568803500c80c2442480001604441c82600d00c11092507016958040c03150440e9944009420801480000c2e110f05108038000c00c101004054a1340e4001e406031440c0341d1075400c3c8520f4000005040602941c00001580643d2941e200840200420204180e154140c90120503019201e440c500b540e003485101408100820044008c604032132180d6200110700d84413070800d8034813801c1c50003510040b80d4140106504014039018150f401200b040480415a8a80651203c8046840702c00401030f035002c002c010306002d0361181303a4140b580908001d070052400c0701203541c04801c000d01c018552a4040340703000030081941c00060107440060450565414940551a128422944292103800c0604000140a0101c030480b0068801680c0c50041c503104d20380c5090065800500410f00782e100510480c81e00010b000c2c061030003088400408088107480a00c010070314141c415403940d2003140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 802224523 1250 802223273 802223281
    0xc0618240a0605061603050708090402031021080a110a06020409150506090a1e05040c080f07140f160c031a091f09140703060c09090b0609011b170d0b010305 69
    0xd8184102d100c1a03241c80d00c01d0361240d0f103251100440c040da00750b02f1f030010700100c2401001e1035402c41910030f03205004050011201c008031100000e12012001803c0303c403040015200c1a48615001c8018451400071103032600c1150792100100d0b800f40d0710100310143d541c11800403041c043c0c0684001404100d40442c189288800080d9065405100d03501d1040803800304448010b110310300d0720300141801002000f50556031900a007007000d0803a0881e200442907000104514010b01e111100b10400030890381c108280040341480c40e0380a40504c00c11850341e8219071002920041e9000007461151a000801c0605140c100c2c3d1617002c007820826094002c1000c491100d20800b03102100c1188138000800c130b1610304e0908010035031110680512500072140080180400c98200f03014441080d032300c0200c140c2d41e4540307550440b80c145001d1544090100404200c83d0701c1100e0407011011060103401800c0030f55510030003040001a270b0011040c9000c070b40c000c03a1329030f82c1c800d110b240c00080c00d00b80306502e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 802225773 1250 802224523 802224547
    0x1090503031218030301090911090709061101020723010b09040503070201050306130507030c1d030601030b070e030604060c0201060b09091605041a040302150c0618240a060506 77
    0x580c40e040703601090007a0009003074003c01d40b01c28000340450f03010f407070f901d503147c502c82d00140140b094180c0b08045c503503d40b00308500307110941138030a25065903168000713420a0b5007190701c0d05c40d00f0206405903400740203072400318601465825a692442003c03103140031000100c01e01f9503200c0080584602801d00400c400300d0008000c644006a09182c61641c030b030b48410000300641c0b45840d12004291800c400c00188980550280c19981d09a8440c1c0c00b080c00d40d48004040400011031072505908008010030010360303030280450700b00e400c1d800c219507420146404a80b42a8081340c00b82d03251a100c44001420310340a1165001521204400c94a08018080030641000020305400ca00408124145407164464810340b4041c050b04880040581140e4052000680190005074800e1001e03103080401c00c8003034400c031003034164400301500300ea0b5214200031602d54071401000c5030034042c06400000c1c41c3d402c42c000f0090701e2584002003103241800070b00b000423038240c0e402040c000d20003008202c0303001d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 802227023 1250 802225773 802225777
    0x10503061603090602040b040b0702120601080304030303091e080403201f0e06041716031101110c030d09080105090f100c0c06090804051f090509040f021315050109050303 75
    0x1e0281004140140e5030310300700000f4455075115124402012130045483c4050320001e0184074001c82d03070035002c030080e0810151140c400303100f00c2c3c0d80d581c4104800c00000b40a07400440079140146012034141c0c45100125560701c2402008480b0b01c1300c009414030030070500d19041c600500d00c00400c0018201c04401184c0c3c643c2c46040e180b408010789542510f02c00784a60440102080c0c0903000c2c589480d0307105084100b1035511010084a405140103044440303088081c90800c8035040000217078030202d40401502c002043e010408510f000c0c15048041c9504c0401505085c3c0c041c0340d440201c03481c0740c00c0b041405c46c0e90181c00a040380d040403038141d84000002401c02c2e10719600940c0043c0021000c00d054074000700d604401402c65003400d000e00140000381002d082216030980d6000b44c170722030115a00c0300d8003602c405078901045002c94284418185800340300c6c0c0c007038825601024404a6a00011141001d13200c0c2c1c044010b40300c640c05040c80c900e40c00e103500202801c0c00c0c410903ea0404000030344034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 802228273 1250 802227023 802227061
    0xc021c021c0e0a09091e170c030c010e0309040e0f100209120f0307031b050a202e08071b0618050d030c1404090c09050a03120e0f1008060303092701050306 68
    0xc7d440403500400706101401110b090b002c110008001100400021765203a40110321818465441d10500c41c90303200000c10758000036501d10002c0c020040d4030400070802900310356052508601500c1074006110390400482603881243c00085440e4040d40c600102203265003c072541900c624003000394001140000d404a4060f4480c9500060303281048a070107180486606295011503013030076000c641103100311116215002d04c068055070300890072051f039604000303840000c0046c0f41e42801e440500456122030441c140300b0540441c0107400780800000808101c20140d542d42c002000500380e56400d032041c807003001024180b0211766250990889440d00552203000c1d070f00ca484261a031001881381c25080040d141c008c10501c031094603400c01900309a10414014081015003060b0840b07860b0980305099644802030058202540701e0404840c03610000e4803c50b098031080c407072410203640301c50541b081041d842c51344210b010201c800b801011441031303010034001e401440c10300110f080c8041c0c00b1411 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 802229523 1250 802228273 802228313
    0xa0f09020609090405100c17010611030f09030a0f060e0709051b03040c080a0804030b01060503240414150913031707020a02060d0c021c021c0e0a09091e 67
    0x83c90303480d030600f1801c0850143c0400e91780c07845e22002e001d01c140c02000804051022030308419050303880301002d0381d40c1c0094444152003940207110500306007100c2c00c003d020880c07014050311030000f0740d9586d04800040500c412240301e40c980502c06c2d80d10301d003000b101d4014070800070144210304001e40c590900300c0b484801034000220000c001400d0083c05a2604003c0080d9401c0718001500c41c2416502600a40003c40318040701c4400020041d12a8056038081c200305441d11801da2001c600b0700c080042c1c2c85143e6500183c94044041030000e03c0035240d8460450b0300b001c4901c2158040c1003104c00f100051294440c038260310150030100780e10070001d03480342618410034021500e41010a0785000402d100095014a001440703888101d150f4101030f2541c80313941c0031200000c1e2145000032845100d04900740050f40540d0100030300c1c6240d0344420450382d48a0602000b0700c820702010a80c840815001040c40700c0e12918070384204484092001c2201400304506803c108013507840888120b1030111040c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 802230773 1250 802229523 802229539
    0x10501053304030b0709170606010c03030b1509040b03120f1c050702070504051302011416080c0d02150c0702010518131a031204150c1a0a0f09020609 66
    0x6160406111804864003000780e1040c0c5450f035078640700b040200708549110000714032003000a40a46101c030204440d00b00080507040a0361654011a0f10704004102941010f4445055140d039446907061215440c001d0080d40307903100954810f01007a201c0c45007805000b0761001120201c255444019500828000000e89503101c04c215404000d031581c000b403a0750f03824502018000403a40002e499030444100307440900255850455210a500d00b212019001c144050034014004510354010800150890741d059840001622000700c5504110301e0716409030f00c003890141f8110f404004401100074083d03000d40103803070180c40000c03850107540e10003414881d000c942500e0680c021101840561405400c00100e8a03404201704054204032100c85032103450154011298140891090b884241250141d454941b60100f801030b0307090701c0b0400074100030038038901200151512108800724845010480071608040c2c46030f6040380e002800f040c203010310b4211548016114181510745e088803c0714151 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 802232023 1250 802230773 802230829
    0x2040b041104090209100e2808031b06010b0a020d030f020d050f060405010501030c0912020f1f030501140a0504090218090a0b1806010302060304060e03030a1d01050105 74
    0x103010380070155503522041d001107804a410010342d400703020660000c0701d1604500b200c0340700030303101d080901030700541140750000080034250312481c02d25450725095103081d400030384d82c0341041d040da00312150340c42c4c11000e0f00002c562144002c201403409004104582d9127096081038002c0e64800d19400018140350722140c03407050b40011541592a00071160034144001d140c0112008200c0c0005c840d0640716500d0f040020550b03501c00d01c16504d40e03d510b500d5689805091800340700e80c003441014102da0007040e058008450740ca6198204075400701030050320307405400502000d801d540c016000b049a204850002040c290345450101e0200c880c1514001070800d41d50012400e030400503088030100740011803e10000c82800103c528002c2d0103900e40c5602600e40100c0000242450701041549a00060040c005071a10b50300a640081c410040010400043d940640c156001100d100c80100c1d036401e0f45000d000303241000011141c2d04200200410740c10000007900302c3e10034845c2e0b210103014400501e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 802233273 1250 802232023 802232029
    0x1c0308070905040c210c2c040c0c030912020307090c030f09030207140a031703070c050f012307120b0102030c070b030105040e030304030215040c03061407270302040b 73
    0x4001500c0094000c3c0480f10500401801202490210026216045403141d175481c006101d5580d4807481a80c81d09003030480c402c040d4106502d600d030005007405000c2e03002c0034543e440d03100c0c10f09943c140d40c6030103049401c9410f0240402072917910441180440f50351000041c2d40120b840340590300c80400009103583c1c01c5404900501040a5241c2d03418a060150005d00d030300010b0724000c07a050503081c401c24059003000d201c09801c10340300042444095241410300c5103130260145500080324030301202580341c0c64540615004904100c201039954413003554802191441550413055440b80c061049420301800003861071103800d508105495031080748114503882402103031064075099045409064848412022a42c070070322071a4400d88c60010640351460b000b0041ea41314a0b050b40241c20720b81d0682108440701c3d20001e1003151910344040e8040001200ca1183c040003a507a099010102d1a260001030466092101c0c0d0520041c90a03611204c20100075405400703032039041d41d0101e00c002800f004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 802234523 1250 802233273 802233287
    0x3070b070921060b01050c0a0803130b0a0903020d0827100606030b040c030c020a0f02060d02030a0902041a0a14042c01110702010504090213090221061c030807 70
    0x1900e2110301c4960b00c00d0011541000c81c44480c0982420000440b070342c00190740c07034880c001e0610555007082d0724076004511031070701955002c0c12041c00b4580801066940e250350250440d81c42a11039075a00703a070800e16904200003041c10050703042907007135800d0110900459081c280c5c1c0e200a8003c6010600710310f580c0511186100c03507074010007031040c1511003001401078517510604074003552401c10452447e5209001301c0740206404e4015004042603900c0d40c0c640700840910a07178102c40104550039201c01c03203100452088001507000034198180d44104015640c0384071650300484444c0c6110341036a51810412400c440580307070741000c500100300118000d4090364005120030140d00000040c9000303034050340c0c25a428041d0017000701c00703130f0584494014003807200c0184c0050340601080c464a007080c0e0007803040300e61000c007185088fd40e80c3d4842e820380e0b128210710070880c0700c01d00c01c0e03001140d01212120b42040044401050703452900b00e6010081d510072002408120349000410115801040707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 802235773 1250 802234523 802234529
    0xa03022416060e03121609050604120501150b04260109030f1803080d02030a0212091b0406050927010501060903120203161112011503020a0608010803070b0709 70
    0x8290340c590090800840340d454040d001500e14038201543c2c00c50b110b8012003220702c8400800585445030311910030002130b03801c240040b074046c02030b604030118003651050060401400754041c024400c07840c1e0b140c46400c3d14142d511042c2107064001d001d120069650090b80c00b40c6500b410606103501d1100300c130020801003040041015480d000e884420b0507808541d0510030419502d41810600700941710b48818455440301601070707802803009403a0720b0301c9a0000c5400032240d000141c00c111021440c1c541011003070300c260116038064011100034044070390b40305504580848040010901d080c002c1007510800030308000042041c09213801d00d2280a2002014001d0040020800c0d903843e1000901613010307a02041ea9502030001ca1801c0d0a440001110703034500072440d05600024007640c2d1045940d4600003403030b40c000c4900c000903051000c02d1152021540b609032400603944e1843c0140101000340360446020044060018410385000000303c91700e02d039000584000b0781c0d5070281e003100c00580c00e030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 802237023 1250 802235773 802235839
    0xb0306060d02100306030f060605010206011d01030b0c0c0f0606030607020304030b0f04021c080a1e1709070b0a081e060102031209100c020c2e03090c0b0705150a09020a0302 76
    0x1f841c1c2406005c0d8a038010b00941780c00382c00321411070341c86100711145500300d0072400c030080403d28010b01c001070f0802e0711950800c034025200c40c01e28100180250a12000c011010100c0e4018810008240780c2044070b107800c80780c3c90000d14a06410754840030b1400c9401429107900c1100303900801c0454841c81c024002001c2c0c0203103414041d0341c151070108a00d6014050900c00104044840c81038660311750b00d0542c99900b140c80b18000352822100b0b1102200000f0600c2e0b125016202c0c0001e80d08404400402100c2c6c80d030707030341c142140ca00b540b011560000c00d4481d044070012140c0400c1540e907000030807911146441003281007155200461a8030304181c1d003811241c52400c020780d0f4404c80e0b400048462410f0000c544501800e0010b80041c4540440c0c0c4105034242c4044042d8505134901a07030021b0500f81c0200813880c0011307100c0941002c00c0e41700c03920481d81ca87c4620b0341180d00c0c0d6a604075590b0030400604090001c2002e54000900116041c000139115402d505041c2c20001800c160250280b0910 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 802238273 1250 802237023 802237043
    0x10504170c10050907091508070e0c0d0509010f0510050108090610060c080f0a03050f06090702070b0a090e01060801060f030204060e01050a020c15042c16200307060b0306060d0210030603 82
    0xd048243c4400c07c07912400c6c00c0340c4900000803032000c0001c48602d105400003078400303061560010f91080500030260610149543e28040d0202600450080d41d00c2416940c44090030280f801d8001072109000403c25000f41d080f9109103c500801c403a41d000c1215050318090800388541c4c100300300584601140200304207000954105000c0d01600440e220b40384540c0c81054541d41e5200b80000c1e240c0468442c00140c00000040c09062500c40141545244500d40701e0301c851b460303c6d00508610400c0e007085012401c80c1c001000041c0d40300010549041d070600d8154142840c000700a01a00341078036140d03041c081e0101d91001c84520030040341040c1400107080c0944c0500c4840ca04a5a9005018400382c65001e026a00388444900f084090040003068182c0c82540d1011480f21450104c21407600c2040405e070f41c0030507203040200c2b156003e002d0320400f440c2c0c1c0d4661881c056046800700c16401c1d009403c250104584c0ea03031201e003a171158503015984444a0200040100c005003140d4100030943d040b8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 802239523 1250 802238273 802238291
    0xc030c0106090c0216150c14010b0301321801020d150807060206190605101d091e0c0c03070f060e0a080d0f02040b0c010504170c1005090709 62
    0x540001e000c64600880400c00400081c5040380c07241c0380c04042c0754101c11030030b00800030324000800c041d42160300751400744115503080c0e80f2140d03082e41c1c03003a0b081601d0b911041040010b01e000e01c44d0703400131103203e50300f080e040041200c280064000300e0014144441100001441c401c03540280078005e6203010f008558642d26600000020442c1680700640400c018002180f40880081c1010a8801360703002442240d480d5000c420300c22401085c00d19200e0f4880000040310b0311246204070705000541c90750308204d902c0c451a5206a405ca111880c4140603440501c03146034031200c40e000000c501400d000c4000c0c1c2d19000720100900c1000c450700c0d042e200008102d400d0040140d08410030324400c440c14088100040035455840f132100c0c00141802c481041400c000340e9042d8403400030090912070150030079550b101744654a0b0042c8002c10751503511481000b00b080200d40e180740b00784500c0502a4141107040c0303d401d0341d400c404820f0225055030f61000c200d0040007044004001c000c51001403010b02c003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 802240773 1250 802239523 802239547
    0x70b04050d020c2706042307030f0213140a030b1008250b1e0703030605030c030a05120a030e030309073201050306010302070215040f090e070603110c03 67
    0x10310381c01120040c0144902840d403480c008074040b05500c080c1e02d00b0031912079078003107401c441003010700140d51256a4408038503048018008034140041d19040350300d403502c2c04200c05010755260180340d09401d48100402041850900b940704180e5400781c4403104108a6140403079042420b41d000500420310134010002d01c982800005415950a0703001c0c1e13281201c0c02900000300002d070040c01d1680e014078030014065464500d02401103640c043c21084604010325101c100340380d200e0b41c401c1d00065124403042c0b0950070704000803403902e9415001082489503a40310a501c17001d0300c2c2c600108001e00044c100c501c50784260401100c0401260a0b207659040100085544083c280b150041010508216a501c101c01400d6010b6a0200d01d9107034015040c02c000440705540014515814140e090190304090b880d40d101c00221204000300c1d181d6a0f6080064800031a44254007140c195401c0c941c20261849000c40c1d114102e40e09414046011018580c0680c5a0301a40c9900401440b020030702c502c1a40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 802242023 1250 802240773 802240783
    0x406020f1e18040212060d0203030403060c1d0d120509060d02030a140615070f0c21030912021f14070305130e0717070909020703031b11120d02070b0405 67
    0x341d01c0b10400c800705030400e00060340a0342525040c4400040009400b070304000480211091005050fa880c068407a82c0f45411104064440c80000b41c10a168022030704659502014000c011145044d4440b81943d03420f1599034150400c404004000c2600c0c0440e8544109070341369499501001e5440745480c040040041030f03180300e20304038800084007103015400c2c00c0001c0f034164450f8020991900090361140031420148039001c80d03652980802c0002ca00302c8400e84810035850303440150b4850345003800e000381804c02a4000311020284000c2510051703450100c0800800306a42c142e8802020039502942c0c00b040c255180d50380b05d000021000109980b14005050704004228010145500c4401c410181001180d540300860000c05401c00e15075903180040b684541c581c83c0880c0c078661100802e4040e80c201c2101240807c2d2078803006140ca45e07200741c03c00c07200703903c0380b4241ea0300d00e0342c3c4010103641d211100c0c1a031888400026048429600540440b43c4482d003084122025040c50303d0910707610 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 802243273 1250 802242023 802242037
    0x9060b0901050a180203040f0c03030806090109020301060504061805090c1902031c0b040912050d06050402030709061427010e04051515210612010605090406020f1e 72
    0x911188400070802e403500c05102000d8030001d080000f100300014000c84001d52024009482c80581e1405001c0000e00b14500c110245100fa5035010050503c80c003071040c0074034107811031513410b40144014002d17030341e100059808940f117034684191000a108062044403600b0303000160405480d00421080c03803010401016001b04103400c4091107a110702c4100d031240100c800a50740d0811480f0a0808595550010414907400810000307208050f603468090081d0040d01300400704401040c2200f0040e0300b445414010901a9020b41c55480c00000050090205004080a0207500c16550b003140c40c1c080155404030341070301c4580c030501c41408104080f50410b1080765001501c00d82940701a801c050017454001c0d49915500403036021400d0820010184002d90010f41d03a8050010740045002215482c09107612406103caa41c14a4005d11510110701f1000d41016070402c1e9080051303403107410140d40e1160704074400588401101c03650322514858980440703070710f00b900701410711564020b00080050f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 802244523 1250 802243273 802243279
    0x9210f040b2a100e0f0d0e19030f080703020f030403050304172a030c030604080403060c0503040b0106080c040302040e06190605060306040c03020f03010909050c150a0e0a080109060b 80
    0x30500c10b11a0321a001c1ca082041e030115034001c611000342c02440c5802c0010b140d1140019203407601e5203402030750301c6e040c0007800c1c00c4006044642a85c0e07031070901b501c80b00210444045415a038030b095480303514040e0581079000b17214070b200081001c1858407d106403205030488400751307650707903035203040290f5070ba0818021380310382404480504644000015035650400b5628040310f1001030404500803100c0100d03446a5018084d8890120050382c051000901c00c078441c1808030348607401c5007050f00440b400f0200380c100303000c010024040440d8201c1d600b00e04564a500c1d01d5060380e928907070701d24600e0241d540000e40050624007104524a008234286104003822a1603582e481d8080c0e920b98180c40d118420079410100c20004200d00e410150041c0494007098100540b818441585121066100340d104002c5241d40324031000030000140920f04c00d941c42100d07058002c3d0038050b0001028030408060341e02380031000d0850501c58441d420490014446c0e180208500300403414840d001d020b51030b140c1c0e44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 802245773 1250 802244523 802244557
    0xa0b06040b270106030c0f1101020c0706030608100c0203030f131202300f030a0204051c0c050613350c0f18011811030114040509010509210f040b 64
    0x249540310344105004090f00381c1c1d40c02c41960000c7d0050310b80c04034110703110400f550204444080c82404006140003002507030350000e0000d00d002074842c20b100701c9401c01c2c941d4034104140060043c0d40081901c1d00f1910440440030a504c44602e90a5100c2d000c01000f0a13400e2555201d1351080e40102da0944c80c40c0e095010f41c07440c6040103560058180f201c00f5000b200c25000d1181c03a40c05080c02c4080d42d888401020014501a00c0e0f20000d4225940f80125807441c001a14070b2008020407400c3e0b4400910080e070703110b070a109800318441034601d0030b4010a940f1240d5905911030cd24500e02541d0084c2c00411440c022031100401101d40724000704502034011082004e40c4001d9003072407055800e9811913074242030790513401c0c5002c40b5140107099140b1006940c0fa655030030010045800114000c00348401d41c58828051841403001340c800060141c03d682c3d15010400009a402040d94400710b00420280c3c810400da1a2900c4400e0141c0f0380e07001d030142c001060119420064034010801c554800459032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 802247023 1250 802245773 802245779
    0x1020d03050115050d02040b030a091e0201081909021002011d0a2d05030c0a021509090a0209010c05071203091a0a0c0c030609050c09010b0a020a0b06040b2701 70
    0x340c1590028400c40c4044100003001424003403241c809058030010030342025180541d0360b492001e0542041e42c80c0203109589401c03120412000d1040f0541050070410500b076690754640001c0d041e4a40200100960701c0e0b42250f0f0b841c1a10306078480400994001c010b10300103041108020300038a4100800d85200c02102014160001c0c0045c5070200d00742d01000700c455040a16008200f03804030608090048004520400c0000b002800681524401c1c080206440380d0940100f00e850f660703114800c55440c04c108a01e0029071a20030020fa4041e4804502607507810305040102c981c1008203502400c2c500407001c001c510641d0b501c2506409030701a0307880a0001da00c80c0f804521545e0407058000b0b070010100944e6012900031221140d0260113003210b0786419941b41c4410055038804031080b02d59400c1640b00654902c0d10503201800340c00d00701002414084207031070296031012102030190442c8041c60010780150740303a803c45500c0c00c801401003a855920102081c0411003000c00d03611842007000004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 802248273 1250 802247023 802247027
    0xb18180108060c07021f1e03090c120203100b030c0a030b04020a0b0f0316050d090303020c06010b04080705090c130b120a02070c0b07060f05090c043209100501030b0601020d 76
    0x14901e066001880c0e140b22080c41b0580800710026605a1001d1100c000d0501c1e210b5500d2407110810603209807000301d491a01407600c40030824403074114401c17440b8040c00402c00740e00d000a4843c5001c0704048001343c031800c0704001070302d032100b03000507558402036114010040040c080001801203100350341040c40c80307840e01060800e41c0902c58050b40348850a000007201c00d10500300c1c5c8444c014250a03c18a084070b414840800c2e12101d403c240e011079000110030b544c542040100038014680d54164074107242c04c0c01c14480d12003c076807190343c0c89a44100045404044003204952505031040d0048110176a01c41680071b42d80c10200e4122520314008002803020b00d00d03402240d51a543c081c02e05661103080c6004003045400c54102079550390780e01c4030010300507000c602c591350241e01680d008204041203035040009545411076280c40d440c0c00006008664812000b504c640c1c6082e801c1c0c00c140320395402000314a4544440b00b04041981400000024006a0034906015200c01c0e400d843d20a4400c40003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 802249523 1250 802248273 802248277
    0xc040e030f0f0d020c010f0c08180607030f061d011a1236011a0a080304050409030c21170601200309030715080702060f010b18180108060c 61
    0x81c111011000300042980703404250000c0900c44805100141030002c128109401c5031810980007440b280c2d64110358542e03e40240f4481c4c2d00c2001ca50b846014200b01105050b2104405030200083c191500ca800c492018280c01a42c0a018603071001001c100780074104d220215401c0c803928440a810031031141003e030700f490442e000c80c9016003454140752202d040d90f21048045e0030101d2043c422050f9031071080201d204402150b64400400440d02e008015046569220143c501a07c43c4443e400200103001002c8140c800b00c0b9807c80300001c0d0303844103080039280c1c0002000014002c4681c144180403103c10070080109401a030355a603079201d0a4185003200144050360106d01042031241c000c445d4114188031a1143c02e40da0b426030f800e01401c003002c02d2400c3c400d900f0aa4000c02c0814a8040702c1303074000c0c2c4042e4441b1441c401401c480c2070000700f845407900c0602800c0c04031000081c000a468451020f0380100c4000a4400d880e080d0b810a40005222020300511803903000340c8022510300c83d12142 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 802250773 1250 802249523 802249537
    0x2040509190f141614061605060103110118170a0c0b0c01060617060906040e010204090204090e07120807020321091005030106020312060d060e0f01060e10230a06020c040e03 76
    0x6000c4c40c002d0415200f2a210080d018200754041c40c1044001841d0075036204000390365201c0c000601040d41035203029a02e102109220a04100345600030000c036060005252080759124a01d01c00e940390105c04143c1051003840002d0110440c45000060440001c8024041c80b8100c0000300120b540b40c50b01250302c00c3c005051018211045008203c551078034800b03081d0095001440080c00006040045003640c10982c0a00d240550220b020805885a4003c008044507414040c20002e0f040841c803850a0741c004c1e034007a00858001c2600c42c11520104500b041c240c0c0106040380c114200c03650240070907848140b0302405088200f4440703d0060046090780e06844098014500380300c0441c900314030b60b4100a00309540440241007400101c2d50510400c0c0d081448000680b0700c0c9444c00008034259a5550300c02d042c4000c0036010844290a84005c1005039845468080b45108a2801001d0400e0a040f28190f00410030580068169000200e00401800c181d50900118061001c010740b0390040403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 802252023 1250 802250773 802250803
    0x70506180606130b0a050301110702011403040f26030112050d09030c05060c10020c03031f051318061a01120510030215040812120606070f02040509190f14 68
    0x4003a00d00303c20307041e40104500c150301030725402c080da60b507100290075103c01680a982441e070008524042d540e00c1140384c11034440c0585550728604059842c410440400100038211000e0702000c485482c42c100440720303000303400c0a00340303440c1d50311002031500780c0e0b004030b000f00d84600c41c0e1240d12014a018411141c1103d03001912166028909070034000310390300100d0f00d810540208030b5503180e030103c20f101801c03004c49450300071926172405809003031401498031025000b0710760000c01000240d40700b0310100d0780440c0016001c102e0128040390f55182c040106001001c2d0303070503c0360310100000c41900300c035242784003640e44030061a040c2d6100310403140300b0350390050403400d200024005410111920700941444481c1c10b0b02e810783c1d4000d01402e1017480e0b00c0080901c0030001d5801c521545890030f01d50812400c4400342d14040040d40c496440c0c0a20344030003409586c86200081c0c0e2118203100701d40848040c000d03482845003080c82c0000e540f400c801002c4695410a1407009038880c40000c1d905456a466 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 802253273 1250 802252023 802252039
    0x60626060418080f043006021303140105060f0414010b0f040305060709090627050408040504140a060603200d0b060703050c011a0d14070506070506180606 68
    0x106062002400000b002e02c1c00400c000e210702800103000000400184441240f059111810041e42c040d84604a0310180c2000103040b8421042003817458404040380d902810060380d5000c003401042e00d60515074005082851030340d40038440d80710190002c0d4481c120807140c070380703800ca45842084226072400621511010103c00144142c81444c00206071040109080a040660381c1d0b50f2640342503011214400007807440c0e0020020344030140180800351030b840128801900b401002443c0e4880f00714207601203180c6560208042c403213000c040f6005800003400c1402104200108203804c8842910040c681b40c0c5070000005001d0711a104980c002c028150f4500c00c161068256150a0b80102084044041d51014904016641e0400a0203814480d40b44c040c1ca40e0349031034010742151090340e482144902d14010505480e51612030310050180c0c8451b50310144010740c02000e141113000e40029402a00c00121328050000c0014501d110305550390114040701c1401c1800350f01e403a0160723051034103e455 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 802254523 1250 802253273 802253281
    0x4020c0d12240f050303040338340206040210090504090b0f1b030601110c0603010e2202060a0f02160303080a240b091305040501060626 60
    0x20542085201101d400404074090720000c2420702c040000451640059000c4101040700b031100300c00c44001004110055070405146840724142e44448015034124003003c0d1006503200c43c0030380d551a600c0140080c0710108ca2504101c1303031400c2700040c1e900c02c094a5424007030b660111580480880c0041c2942c0c0030341081c0d1030f40d0b070074010b8100840c1c2d203602c1805441080850152960f21038101075030302808c0300c500541040340b4081603100002d0202040e0103812283c000703c00c00501c0071a90088820b28140074100d24107101141000f030441d20f401d0f489040003000040c00350301d040e56039004400c01c03880300380c01c10b10816000c0a40e2085100c002d400c44010310061030342740d0080031502e04a500c5401510f0300040c0e00c00780382c01703040030f0341e00110041140301c014040c80b01c9141c403c13101e41c0c024038141e001d0900300374100c0a9104035a44100242c00500241c041150f40303c90b40f400f28a0036800074240014182842d0140c007801c0710780101000a03000480d00c039903140c0740c11191000c0c0302110140000c5511 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 802255773 1250 802254523 802254527
    0x60f06021e07060c0201050f2a0c0d020907050c10020c160305120d1b030e070503211803061e160c06050a0204080d02030405030f06011d06010e10020a02010e04020c0d 73
    0x130300c000680c14001c1c24420306401c15030050080c241c40181c41440c01201481045d0081c1c0ea0f583c46130101c5071980700d03a01401076a1110710b0502d8181e40c044884c44043da80365441100e0300d1040c6d003500c0a60b400381140300041a5001d402401c20b2000710401da400602d5082240c070400380c9948030180c0503500102186d61010b88410051060a40115022a0070405124440b000e080c0c44d091150019a0301c035641d24405170140012030161004801905140360070404990190b4020f00d4030b4ad8121000003030f082543d280e40258021001c0300070b000e036851450b12102804005041d040f601e440c0180003c0045e106822188032440280c1243c1c0310b02040c90116140c2100800d0000d00380c035100c40d42000003007070801042101002044481d4000c640c2c660419050600b0f00e181c0b0704001d011588008010300102c2d003040c042d00c10707090307030f10540030f059a58201c0100e807581d004203011508103110030400c02100394040340b40301c8400e000780c84041c058010002800100d1284600c03175406a000b8020700310000d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 802257023 1250 802255773 802255787
    0x30a080112020a051f140f04050625050304150212180a03050337020a021201060510030905060702070308180310050c131208040302010e13060f06021e0706 68
    0x141c0098510944103495002107140345201720003000706140c000400004107640141c5514480e400110524200240011004683d004a01841d80b08000110307501440700045280401c0b21105d0026152681c40c007030030025102d0788940540f43d62815050f540c0380c81907000142c016440001e1001c0c081c58031440000090005a00d041800d911898a0700008080ba4040010703160064455112241c40e08003c5046010303842d0302c040e201c1d03001c3c019105150a96401040c89105e0b9501580e089441c413080c804014010000754028940c00743d400c4007111070803030f8540d101c0303101c1d98801c6046805e42d4460701000c2c0d03698012844003c000d02c40400200b00009003110a482e03640c0405012500c20410170f00840702500c070200c4028082206c0414040381d20200c0031041801800c4065480c62410603036100c5480b98881d40c00007a050111611941401d92941c102500e10010a503104000e0a0346450121001d181c041c440d060044c46003411400d000390030540d003030384c030410b21200400b82148ae044051b5812 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 802258273 1250 802257023 802257059
    0x3090b070c1b0609050f040504050a140321040320061815180712030909020a140304050f060709060c2a0321050304110d051e06061002030a0801 63
    0x889201c650b080030a040707074819000740c02192100b18600e41003034240a0382e81c000480180c8217078204802d00c40400c8008c64210b00c01c54111281500c41c1c031003001c9842c507600c00c903080c0020740c81603200300d81d207119090b0201c00d010314402d5481c409820f8041c101007214032001c00840d1400d4107c000403a402032804c1100305156901101074968191140c072402c41c80c08400c6521b04000c40d0755000100038440b050108001400b0700c0103140250b0031054400400203030700f500801ea03000394006001980580503601c2c601c000d0b4907840000e0340c0c0e80780c1454050340790700c03283d080d0303044a11448000c60314aa000d10740680c01c4da10315541c2c1801000703403034440c500070743c0380528030000c0e100300303d10742d4082d41c0c0c90081080003642c0901c00d00c011400500361010b403507404040d52102080014406e110014146411107500c01104507520445483c0c42c0c00d0290078406003040c014540b0508186860000001207040d9105030400c0340d03403400d58800e00000380d890b07108c0d41811000040005c0014015031101240038415 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 802259523 1250 802258273 802258283
    0x302091302131d010c030e061306091e02040506271003080708120105041107030c02030c060301090f05010b181203090d0614090706140a2303011503090b070c 69
    0x42001001d51050450301618000e03820f801c96910307a10200d200c00d00400b090f10a4521b4104010031551403403070784428000c0c00702c031501000201d4100c103110994018241d0190481c03400c0540e010441c5c4d134281603c0301440c0c200e01841c2418002030341071501360b641c3c1c2d03245030b5040c1884003104184e070004042074200501001c1101401c0303c0100c081101c100c06003541a205501480d518a56803000c01031a52059000600c0356080c40091419401b02809440c1e003190325042482110300e0074070001c1d08020503140080e400100200c00091805420740018a044401541c200556621094019210300c1010081c0300f01a0240c10314080b5414600c49032000c18400d60241c80c00c141d03071040003d250206985d01680d80644807500c0364860492a02c40d240c001451b080141400c51510102030304141018411401c41a000f103803010180d8040c040501421048590b82110b041d09000f2400064000303001d6200c2040e203942480c0107542c044e00c1500a026003009103144d40e6501d409003210010035100782258 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 802260773 1250 802259523 802259539
    0x90f24140f0406030f1a0f090a080a0e10050901030b030a0b3d030606051c0b07020708030c030d060f0b0d0209150a09150302120a05060607051915060302091302 70
    0x101049090358903614080c0700d2130343c42c102c160540803916119400501100d50320301058041c808107550000d820200b05500100c2b01d5200c4402c0001900d840307030f0840e080ca400c000d900e250303015940c2d4044001c00350350500740ca0412001150f03000741655031021020060949154001096025448592800f0309109d60b100840d4180081d82c1000d41e924a400780759800a200c01c0014810003441d40a0b00740034002c152080301d071450340111405036034141e8000c0503160740505004510418424000d0700301610b80e5404896540b0300d01810280c1d070794891a0040c1381241381a40100b0068944e12903241103401d8101c4d1141400c0f020300700d46c0005c3d404244002e40c0310f28035400382c1241814100143c4010a40e584501d0440361514641c105166003140c140700c2007600c100005424015800522900448981b0700011142c0c0e401010805a1003545809412032003010b10717800e0913883c03100460310b03603038880e100c0743c10300c0ba210aa1540590f40140030003035002d00110000340c80c1d407100e0f00e800b590060008147e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 802262023 1250 802260773 802260779
    0xb0a180809150a09030b06010f08150348010507060f020702090906060108070203130e13050a0b010602070f0f0303080a06030605010f081c0c0f0c090f24140f0406 71
    0xb050764080450000451007420b810410b03c80310042d425441031080c24850000004260001c002c040b0042448103118414000424107803400c0243e000c03040c000b0040c072450454200300d1244255001406c0d01c800481c5141c07500d00d4001d0201710302008030306c181c4405083ca65075a4940e0301030082d00072170698031582444107801694607142803a00604841016040f0f40c203191000428900d0010b1504080d940704100302c1e640344240d28444000c440320516800f007261aa2291041c101020303040190003445003004840034000412041c9040720095001c0740d051942d00c45105058004034851002102c040100820109008070410f550255464100141d465229900d60040301c401b0303003015500d101444801d04c45c4c08420059154607101c000800f4920724401c0000921074a0014002422440c18555500070401080b90701d0019102c014010b001d03400c99058140020119409001c034188040c070101c1e07002c05070310031403041038030b10107115110641800001d0101c15441000840e030841c1e5500e41c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 802263273 1250 802262023 802262059
    0x302090904080c0c2215050d0c051011060106030e0316060608010b060c100b01050706022209090c0905071112030103020a170d1d1c0b0a180809 63
    0x9881584a0482c064482da8000080d501e41440358446601650250f485100c0c00042c00306850341d404002500071914000c0401840360528060f8845500146200c0c80a0300b0000301c80000c10940d181510400190070f5220310480d0111307001e045851060300142c0052200034030940004500913800c0c1c0032649040207510010b0b541c0c01c2040e40540d00302d0796440041c03148040038080d0707042a14044a0f4581000a58800a42c0720440d00e038103012140c1d9101e0740c48860340d0007002900c14142d00800b045480d20300543c60201d008400f00f1220606007103074032010541240a1048010342900701130200c0015040400b48802400c1c054410b100b0301030441e0840c2e08043d020040c4000a03e020701980340c40e0351451052120306039070b503003001c0e0f80e424a00c20019811080046c412180b28140d01e0b00d00c2008079020300203103103880140762191300300300004581c44c48035800002c595402c5100301c0040308603688410400e0111200651904e0581542525034000f042c5c3c840c0c05850032074401400001900d010710741c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 802264523 1250 802263273 802263289
    0x220b0f1302060a080901111e0904110403150b010507150903140c07181e0c170103140d0813151508160b19180503030c1006050a0501020309010f030209 66
    0x40440014100410002017913400c0c06040400c050411009080c103012040710b030702124074005000140300e400300e00307507606a884e40c210302c3c80c0e4150076a03907640d15600d0342003004070111490040c111460502c0d164014a500c51412aa0030326042625400366044000c0c0355006080400000d07000c022070490b0711150514104000c0c41c0d815221401094030f079240c00035860034980380080c030f0212a803400600310a0060550349242900441c29400592032440b0101510b451301c1ca5030610019034000c000100030040709401c400e18145024044803000c034546403040784d02a030304480b40c1440d85522000a40002d91462041803001581c01000c54403a40d6040c1000d1254643e41c4105a194480012280111214000340e80608400109149401d400552600c1041c650000b0102004190b036245a2942d6100240c0c3c800f43c940181681c4d9528402c151040d520006900602d004604e0300c0c0000400b40740c0720184404071101a00030b1350800d0180001902c00003642500b000a044d02009222003582e20003003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 802265773 1250 802264523 802264537
    0xe0301020f0d1a01170a061d0708060415050411191e111e01020d3305030c12070e0c04031a06010c1103070914220b0f130206 55
    0x1031a2500c80c50482100b20940701c03c26102681c0d090340c065550940d903481401d200d284440e028140c207080d00c8019003403004012940c04a44128000c5001c1a000c80300404001d0281000f07941e03035203280d00d4010070081101c0743c0a462410030b01c3c05450400084c24682c06c9800b41c0f101801585052800c01450706241050002144000980c00e000f00001c1c503d440b0041d0140b07040354900300c444009400c414555a0040c048140d034044014140e00c0034000003501151248090030030203119885c6904a02e02c03043c2041490305800ca00340c191400282c1d0030f01000782c1c0444c3c030010700a1000b8100d1909110410500c4944005580604d002c0410282150410680100c20301c0e071301d05940c0d618500b425908000314100c1c100c0b003010b8031024000036030f03413010481200903007241100401d031210b140001d1801c13000340c1c0000c8801e418100c4000389042d4030f901103841b0312a07204039040d1a4040d00b2456000d0400d0f40301c02000c516002002c0b50b035200390a024a40d00c03490448280e40410021340000d074007908005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 802267023 1250 802265773 802265797
    0xd020f010311030a0204080d020d0f1803051c03060501030209030a0f02060f0307020307023d111b030c010507050a030e030a0b0a0903201905151f0f0e040b04030e030102 74
    0x2000c000c6038a003040203840c000001c9c0f000e003245c07051410b0700802610f80c0400a40411140e8000030320040ca124402200071030f8030100311440c500075401100480d5000c98500ca004c00d00d02040025154064000c640c24440300a01070189000c20359140d4164131517560b020b03a0011803d001039480c2e000448001c42c054141070300207548422107841042400154440c454071001482c120b80c1d05103c0c2141c0d503407020100f812444c0c0e0078501007003004582d00100d104c4018820301c224010420000614a543d0080c190180c05075610588004019150383c80380103002001c44e80802c080e9000b20340b050030810700002c401825560014140d44800505074016141100080d642c1c5660000300350b001161201200c4014103101e8020680741640764036002c2807003801070118107080c0c801e0108441031040014000c19581c16850351b0918910004600000f44082c00c900e1310504070100d075440498482d4001c591010f0052201c40da9107a4410181c4240a0400ca050208500c95246155800c1c0041d0802100c40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 802268273 1250 802267023 802267027
    0x30c07031b0605040e07211d070e010b0a0f020c04020a0f030b0409020306060607260403020109080f0c060d090b040b1b09154e060d020f010311030a02 66
    0x250201e03034500ca4580d200d4070600500304410842c5c0d030400e44104d588852503060141000d400c0f4030071103070b14111802848a0a51800d9128403051303003003000342038009003481c00300d0391101d460700d4950105160a004100c40101c044c020246654450540e070205021280b064840702207015020509903000032560700c0110360000c40b45044290700d480750381e10072002250280710b0f5501e941c01080c1c0320302c40075187c0c50242c04d00040b99001e0080c070b421003c001c080120200e0711b0f00c0c0c03a80b21b001405c0781c00c640412130000d107803028000fa0440703000039134030380201842c0041c244901d40b600c2004105e90007103000703600e0207848000c6007020034581079803944201e0080581e400e1614200e03100d40044104d18254144107a0b040c08810059200d10744080f80000500d034800c1c0d501c2d5180307002080450340c4a81400051a05d5038495002084101c142c421540206800c0c400f00c0c1c0302e10810404084811100aa00048070740540341c0980b0b080541d10b2070301201170600003a20701316184603440e50382c03049540440d600c0e00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 802269523 1250 802268273 802268303
    0x30c0303191a0f01080a09020a030602040602150f0112020d080d1b02030a080c072d021806010206040f2607050d03020406080133020c01090e070c0311030c0703 70
    0x15402032800c58841e03615440021402c2d1000182c410715041d07007190401001c0d0000451031401c42d442109410740040c1541d03401507803131030200040d5105025080c01405200c0c09038138421200d040003401145040740098081e03081100924007840c408000f41e80c031502c03155140340880d56800051038606041e240c089101d03951000100c01c000280c141c000d08540c01006034060300c81e4003109054012003034064043c0e032034003036003480e110001e191104080250320388080014203034081116600807620903640140c1500225000d09140c007011035001d0f000d43c001c4c5000070300140412a645008134815103905000c421007506440412a0140c440c285038040000c0704814844200406d1202002da880c00358509030a00d40300920400040c8500502a800707075010700e80003401a042d101c00d041c2018140321005070005402552038116941683c045040148041111080d042c2950721440c0380752a040c0c0214060350703048510b00e401448020310741c0000e0120b00d64007803081c40241d0040d8002c00c0c007126a549 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 802270773 1250 802269523 802269571
    0xd0804080c0f030f070918050105010e1905040c0512010603050d0f03060b03060a0302010c051216060b18070f020a0804080f0d030509120c0a020d1b0b0306061b030c0303 74
    0x80511480c840d500c01c20020321120000174041d030594099070f50110352002041185108034500c014000d0880d4240000440c08581d100c0640348207460480b031401c48035400780c0111044030400e81d405070050a161a0034070480c1004400300d52448035810000030541e5585d00c802d0b04100703041c5c0c001c0001403441d400c80388000740c3c14002e050140c140136080134554104080019069282d03480000d051002401518040c44018460190804450b21034079503140b0401d802c2100000c11440211030a500d06001c814072801c10342040652801c10240020f00d60305c501005965042e086025041144204e000c0c3c40d0024078620050402050b96030001d0521500a910a5080120f04030490f01010714000410030601d10024031201e031130b6140110380b6950764075131481900300194140081e400050403070364034040140091004802c908918221000681ca6405854152006450680d844030052080120741106a900012400c100700c003140d184ca102c1c010801e0560f00102c4084a01182054418618907 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 802272023 1250 802270773 802270789
    0x106080622020c0f0105060d0f140601060903021003050402090408031306020d0f05090f0c0613121208060d210309140c040c080126070b121b07020306070e0d0804080c 73
    0x135400902ca24078115000c1810501c0050015210203000c40c1c8410601c001c24003904091100441501c4480d82c4642c806072241c0d21031f1104074001c1c1c6c3c0b82244441d00c54468812a4015039004210700303141c0c0c85a031160300c0c181c1c2024002100e000080b9110400040e850304c0181342e01c0c00c2145010070820380d551641400c890006081c51615003106508444a150201e081e50300c042048800507118840c4541e100d0749089240c102c12040c001042d02c1c2803d01021050307030a0f01c03000d55030301e40c4c1071035a420f000c0c05865211540010701c1c1d07a0760105075050042ca5009152a030350581c0c90005108141512002caa1f8007002c0c1044085800200101c60241814040c1070180a12400c020036a5450012624002c184513031316424891601d242200b60544103102c40002401110501d1751604503840780e041200605864503880d511000c4035540791740c003081c403d560b0410380003006804660386a01042d00d40281c1d0340301e416400030b101107494000030310702000761000e000c40c400204401407600c01400410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 802273273 1250 802272023 802272043
    0x1309050f0106050a0507030306090911031b0d020f18040f111005030606070c03080f0a0e040905280609060516110d0e0604150e010f0504030b0106080622020c 69
    0x2409590340140800ca0304001280e085003014a012603907125035007401c03030007402c20350442540c20b410404d0080034480c0718041c5140c540700880590f029180e89403030822a0081030205160400d09200007000546802c4800315129280035003050548021180089080007080390300301e8000c0008440c14052000650b01c80e04034020541e98160684561032028000c0d01005110511a0700006548000c0245c50241c4100565204151300c1c0c460040002051654000d80c2e030744d1303001070301010031f000d920b141c00e004081001d0b03041703000b901403114035020940304185201c1295001c0a003624942c400941c20740301e15140307076014a20018140c14082e01c00a581e5000f1603144040005001c1d040030318510200f10505682800e0801c0081e002002001c11032038011075111740d50040c3c070706801034043c54200c41c01f0740300c0a009990710401c0b40b080290a0310140a0380c000039000e83e401d0801403108030300482e441a00600000c200c5500d40b9071101c100c001c126681000000d042d5008501202c1d251002c200c1b103054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 802274523 1250 802273273 802273291
    0x150f061103090603060405150312030a0f1104120317010b120105100e0405071709030d05091207030e0609030a0302010603020a060e0612072007031a0f15060f130905 72
    0x20780b21441001480a0201412152040e40d441e404904214502c1c214801c00500240555044644d6000944c0035504120380c0c00c0c0107142003505464036020b042c0304500c0d1400d14424100d040504104400707045029990085042c4026408040042581402c0c058000c10341401c880d0754640310010048110b03481a40400d01032a014100801516041800360700d05041c15580061241c1c1c0c1c8140440e1802500160540304844420500c021603901000810503c9890502804152900040729542d46000c0d105090030050512030071b40003910500c1c1c80a070544005050310308251314540000c0c00c252101100304c000d80e40d10070081086060a001e00e0005125508002d0010038040c4041181c2d44101041501d9002d100000100b41c81c0c05145485400204410040e0000c210340030728595410050006450303242800000108280e81c030020107219000f082886401611402c0e0900160003e0201030360340003200344000b054036200b4038050f003040101c0ca0072031030945180080c40ca080311005000740314 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 802275773 1250 802274523 802274527
    0x2210a0f0e031903020d0228020c01080f0402010c2901050a061211040e1911070206070f030e030609010c0816051210090207081c05091f150f061103 65
    0x20304804819510141c110030102c03e0700c2245444210000d21070000ea8081580c80810220a94196a050002c18003880380c110040d08010380000c6ea6215241005107001a48000003d40c200d004e03103207200d801c00c0c418184803046100507501d080c0580442045403000401030183c000e0606240b5021500500c802d841600010b420400000d0810b101440d114143e10303220f1813010030309540042110001c15680c3c046c480c3c241041c44900042075010301c6c0004010b4146050b00b024000c07800100c03940164014007591903c41556034109100c2e11404094003807015120b81c0c2d8000f030b201802038a10490703680f0000600200040f0004e0080f44000c0c01044281012016501c0c91a0300102142c510a810b404842c2440e501c40080c2c40e00c03584541c01200845001091180070480750401400f410003003c0e420180e0b80048a002e0700c111141218210201d03842403050f402140d100009a540130481c0640c04078400c0f1002e41d443c0002c18066200440c144c0c0da42400304070b155401b0100d850a0481d02c40618 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 802277023 1250 802275773 802275791
    0x506030406091a1519051e010801090519051801050f1b07051e03070f0308010509060d0b070f0e0301180506060603010308120c09030d0305040b0606040b0403060f02210a0f 75
    0x309000c50704c000d5507002e1311055054100300c0808240315402010014429241c1500803010881480481402c00340170505000000c120030f1000d024440c841d903202510701001c402c403403140c20040c14019118800400105800140500d001c0c01168862107149205110307c0c1000448240c480050240085250345c1c01d110b0322002600c00701d003041c41221807245400581210084581c20340c440e0f41030080800100d401880105074001e218a412680100ca00b00019524102403000d03183c856403004100e07100250019810a00031118000e8265062900745000707801d40300402e0841c0c420038945400280f10710895400c103e401c1090980c8403034107a0700707135040d9403442c2c1e2180c116000c5c0003040340034046064001891405c0800694568240040885105c0c0c00d003040b0250080105075020340d003101e403071800030311350707041800842d0100c0322040c0305503203031901e90b45540001b07200ca000e402081603000c0100305009054840d102c0707900c245110825480c0d04114200c1d6003150103c50400110500b8071040c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 802278273 1250 802277023 802277041
    0x60711030709060308030f09070503060f01060f080105030a020d0c0902070b040b0c0c031617120a0b0f0d02090c0906070b070305060102010b0d0807020a08030309070603060f08070303180506030406091a 88
    0x1680d005211f800003500390303484000a540c1412415000715030144166010800008881604141202c1d0f083e02c4408030000c441714100c0d4407031402d0182c103815501541d1104018100282c800c80d405011b64100844c841d12154030f041030b0790005a0a035031998055040c00306101c400c281441d00808084291442c0042ca400c00035124011442d04249106003d0b4141c81480111429050940345285c0000e686c1c40c01d28100d048030b075000765040c2101600c1d28907000b5440c1000c1d001c80b001504020141c0c011800d0a41c200110f8880040004a00c203030305004100091710340744090300f0001e224000148191038225402011520010035103811681000e03a8080e00d91180c42020b240e168110395265603c00050011452a9040358014401844004100302d45003d0110319241511640d6409018007940c0d000640c114a4a07805001c0c40780c1c02600d41000068000d00120994403040c25508465640d00c10003e10150001c80d0140c4045031180e8580742084024103104401003000b0706c81c1031a034101082c40e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 802279523 1250 802278273 802278277
    0x501050a1205031204061b020a05030d0b01020f10051e010506030705091f02010608070e010e010501051e07081321020913200103110a0e1c02060711030709060308 71
    0x2010840300441e0307005420310005004031105050142c9103068682440c3c64031500030809150004400c134803041c2da01b60300c2440821450076181d0044002d6003403900c00500b5100408000950506620500814680608041c000c5942265040800040707a11300303613140300d2400300055245440030140c0c800500181d03448a0941c0d4001d20310345049a202d05400700440c1d020000303082c50418410021440e244c003581e05410460a40351001c0c20307508a2551100d05640d100270a01400086c0c1442c3d10060107103510920140100c6004611000e8644211020002240d405a1401e45000c000000c00a00503003407500c0000040005083d0404104115050007450390a6a08007d10035a1102d001c40c80340701080d62611101c5800c92482804e40d0b01007800e40380080f0045510302e01003400d00b241028080c00503015981c14014a0311b0f444a442c43d400d0070400400b03006040c03008031a0461150704051b0316400c02800d00313648541001da400b003c42108141c07070300c001a40003840c4682070440600001b104981 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 802280773 1250 802279523 802279529
    0x5060a140a090e0f090f0c03100c2610050109030323190306090c090e0c030606120106050c010e03030c0406031a031207060c08070e0904031701080102040e0a0501050a 73
    0x192500d80c0116802142c1000159101c91611031a51050002c1d02c0c0302000458000c1c140281201c031031540c40c840c0c0544510b0003065499154001c4030031040c100505e074001d0b00b0b64003594640140b4041c1c1c41c0d1340091000c1c20f000c01d004505521030080201004011002d00007420090908110252541d60010a021000003011407130040542201c141c1c0c00c0044196603513400b2201c41890010140c0400400a05080c0300b4120054104261078030398500640da00c01c10b41c0c6903c00130b41c1d60b50780c4d48140c08895900c0508440e400070020000d04000e110058000d5000e004155122980c1d5504442c01c2425101803802d0708000c0e4208105000d0000705080407981140ea4904022502c2040b0459400c45540008003641d05402161340d0a4910b010394402020400d214840810410101c01400ca408030001ca91150104400d400c40c0e004525021700c83c154003903c41d1800d00343d24115000c0706a0301d0107003030384009190ba401140500000180d0750041d5806031175002c0c10885507145c100001c0e1500003a00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 802282023 1250 802280773 802280807
    0x1b02060f040f2a06050d0b04090515040510050117060f240f06030109090201110a021e06090406080609150c0901030c0203041505031005090f04030e01200a03020705060a 74
    0x102640e2030341642903918a102e9420443d8007040190b4411016045034019560b003d0228603001901c41c80d483c00344618014246c10000400310400354403100600c0c8503010380191a540314060401c0381101e15030041d91b01030000b18400002c5d0004102034580f0780700700a0001482110018208101c004041003103260400f0010150440341c801d4902068100403d0000c194100700004000b082d0821550000302d941417007030360b802180d035100481c5962606026a0000c0d44072011010901351002003101807160080001e0440349002804000501103403101d500842250708514204032101200781301041100e054034201401603d0410452503061042609650500d90386030529440548200b06940241c10614a51100383d401c48401519942040b250600310a004050204007030404040540c05007006480700c07010b548459505844d12480501100d04005024510300c1328215801780840c0e103425840046c100065003030800a0500741b040c0c21042c000e2108000c6884410390082008003c1d046403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 802283273 1250 802282023 802282043
    0xf0d0c03050d110a120f0c0510140705070f06020306060d05161103120c031f0f150e0f01030b132a0801060f05130e01081c082e05041b02060f040f 64
    0x80050b5000340344087c0c0503080c0d00c01e45420504c0465560b000e201817481000641c0504d41d40c100044a803407080c144001e1946403450841000243c450f0091500301d54024071050078201d00012980440b0f0040300e40f8039030400310721075451031290082d8881c500e400281c800707140b8048000348406490840648a0406c50700f00200158540e0012818003200840501c2c0b09290160340710010403980001d0b0203040c0c030482c03060031105100c41c01203024540440b0040c000d69440003c440c01074000701000c0c141c3c250010035001d800c0e025007440e40714048541050b00e00b6012500070b1000400d02c402000304820b01404035140040c016190061841d0001281d9403900a64890341000308030068210760740003041c12820000042a005000b041369202a501c0f100300134890f900102c0122900401030300c3c01c924840b064551034021144803001e0b44c3c640d51100035160703031080d60341c0c0204040340d4100202c070380c1d5080001008100c40b85e041c00880e4100742c1e8070303002540d1818651540d50306184460310040c400951 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 802284523 1250 802283273 802283297
    0x9010902090a0b031803191101020a080c0a0306150f080a09020306130f0203010903110f0601050114070201030e0d050301081c08061318060501061413050f0d0c03050d110a12 76
    0x82d07045807641d04400b05d086d00c2e00e40702c45510b80c0c4087c0300074020950114003040300c1e0119055051080d540342441aa1301d40e0b0007900e801c150170070103510110001080540716103002c200224842c4030062655400c2d50382da03104000c0028014009032000c1d210380c5445050408000142c1d500180407a0000c021001c500500960303071804150511001400a425500302401c0d00c0c1130513045214014041014170a540b90f160003d80265280c840c01d000d0580400c885043d82c15000540c0780103844000c0c07041c1400170303601500c0ba95103441c0043c41d1040030000344c2c0000042c4940c850a000c00340d41c0784403d0558407180103401c00050803c0c0001400903000d1090b07a40b501c24001115003251001070080000c1e410703131800078203203c000392109010b07110100b004c1402040c81048403100300e41200c21200f2031103028034104010001c221702c3c43d0104540c0700309032244203404110040f80300e0000710310800061413002c600c0c02000d0541040069524850780140300355201040031081142c1e62400300703143c41422084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 802285773 1250 802284523 802284541
    0x215010b0a0f172d04030c170306010207140a0e15030c011701091e05040f030f110a02040e07051306050a0b030c1c0f0c09090b0d240f020a0e09010902090a0b03 70
    0xd00140c21010034800401808149508019141d689a0141c403007000c8828402070709008d140f10560740d6900680c440710042100c03e403a06807100017484010111400c4030b9541804003104081034400048503c507030130041d030b0980750400c0032610303406003801d012400900b1850b072514000d805200b4206001d40b1480d804403d0040d070300856181421ba00c4040001d818141801000240150f0342140802d518000144e0500d006141e240302d11a0420010240c1e941c2039428807001d410704c0c1010b40401c2c824040007150036904d060f1070703800c1841c1400001802d0380c80c09040042d0b508082d40f10100c00ca2040083c40403500500d801c03144a0030340e004d00c030b4813030703d43d00d0310044007c5c0409440b400d0810b150044241c00c042d4030100700742c21140041d44c140704440702d000030800e42044c001c030010041100a410800f02d410001c2080b411440c03118000618507072000c01d90030a90388090885400142001c140325a6480c1c4203603080d000d48441c40c405c604000e20000456a41200d50260000031a070120000700020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 802287023 1250 802285773 802285831
    0x190510090506040b0a080303060108011a0a03270515150604330e2b0213060e07030603050615060906090d080c072103050a0f0215010b0a0f17 62
    0x400071708801e08076603417110555140d4009841c0c0741c0c0054941000080d0b100b624600001450002c16a1640343c0300303140000754014118141c109580794803d00240c0061003010b005010120b0048001c0e01c8001812400e035080f540006100c6002002c1a80c0b04c058507484e0700c01594103036049910101c8103d00b02e00c4044c0031181010124581d408204600c118200d030b804040500080c60a030bc20b00559804070b8075541080450200b075030614450703d02400d0161030440c0212814101c2c031a00099034030748401481030039240440d4910b01081c1c643c1400c2040080400001c0c0d408000b10192120030595000099894803620880074800d100c0411101c2c0b8695840e442ca4820a5005c0341160f41c1d1141c0c0000640ca900051158a4081c401c0e880078451100702c5070302d01c002d01c40c1d043c1c3e13039113140889120082d588100300b022800c00b1840b03410760900c0e484421580140c060034820100c15140c65444a00030080003070f642803581000602000c02031341d941621240d0350814803030185000c410b000d43c041c224100d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 802288273 1250 802287023 802287041
    0x1002030103240906111c050f04030e0a08070605070b22080d0608070305011b020619050a02090316050307140d2a0902070c0b0913050402010203090d05010519051009050604 75
    0x24034103808416545e1503217005103144244801c1324541c803004190700740c1c121402180c0d10211900404001800a446242c688190043c0104000103040d19804501e2038000e00360003000204100003002000c3c04031500f01c090748885012211000e005038000024140b5400d520020b000c410b020074000e03889402c603002030b0050144241220201e80c1c0e2420014040c00090500210b5a0001e07902c100c4c1d203610110f4154032440904201c40c003120860355109004010007059040350755800e11074188155010f1000301405100b01441d41c1a480c1804201811310398650702048000720340c28903c0000761510502280907541000780c000ca4411001580205001d600080040010701c2c00008900e00320030364003074076030b180c0070310b80c0c0d40c501c1074030352803100818840c21140592050a890310b107d03d0a0507500456402407040c81924148103800c004240000c1d800c100860b45d50f515801044140c4ca40814101c0e01c052254000b40700600b0070303444102c058940ca0003141c20391915980020300c0c81e00c85801013091 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 802289523 1250 802288273 802288283
    0xa030b121605100f0206072a0b04061d0c0d0c0812180102030319051915050f040903051e040305060c030f06030a170703090503150910020301032409 65
    0x8a0701c69111403503191180d0182500c41c45011403d00c001e9441140d58004c0c0042c20b07001000e464580500640c1c0c00401c4580b089100100c50390740306104c0446c15584940320340f148000440e02e040c6468204242c80c0c4650800c0003014007000d601c0a010000510101444000d90380c540c8000302500703009441000b00d41001c03240b4450a04040810f08011004181ca85040c41040c008804600700490316440709a404841c01c05c01007124000e203017065448642c101c5034000d10f001505845605207012740702494894000074450f040c04000c50308003000c042c460014111400c1001050a0350f0144c024003a0342035030214405030215480803068088110340103076800100700c81103403406003c01d410b0f550003190704144181d8403102081c01420000360070200d080d4003500ca2501c3c080e111140c1a601d070006903040d02080030703440b000500381d1401c0c4003210020140302c1d1035040710319002802074948100350140d808401c0c030400041000c80e44a208002410050341410410032140b02c44000150803c00c1002c4d007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 802290773 1250 802289523 802289533
    0x3060906070c050a2013090206033909120102040e041202030412120f0c0b2a13030c0609080a023703020a08070f0b0c0307080c01051504020406050a030b12 68
    0x113072001740c9150b48003c40e90210307036106240319240d0170a01031b10403c04000f50010030a00100d20b0307000001d481301c9404821240108402c02544095007a4041020990483c0000018441d030b2141004c441054a251480e00294038061800303404419410700240068058903003409a8001c141c400d1003250001c2000d80741e008001c1c0a9814002c2c50203005e511841c01288910b40c07001d40f00b40c01000402c00c0241c02140c6880a48d64062002006482d010303208604015203d41c014803005054025040c0080d151490400741815843c00000e1a6901d0700050103100c0b49910404c414500003448416160381591003100d8200c110310300c10854405500d034210001d40c8008003007441c1000b80100c1044a000319402107900d0f40c0c440c4840c4e00c403141c0d401100309600e43d0b50301c00d00100504400808200c0000d004591801e044c0391156103081d0064559201c2c26511541070000640d401c2c1e50744100410215011890140b03402c4024105125250111080c1034860402000613940c83c01501c5128200d501528 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 802292023 1250 802290773 802290803
    0x1a0909012d0b1c0b0f010e0a08030a0801091107050d0c1a0103050c01120e030a031d0f100608011b03050a0605210624190f0e011403060906070c050a 65
    0x45000e07001044160f84000925081c414504542e014070040400040c103601000c001000044501d034030f050304555084083c402c0000b42c0400300b08010007904420790348008007541410721f402c5c01c5c0d80c4081c44060b100c4000b803120b0408540b001c1a4402d101c04141040c01e48803c40703103800715014a422214060801002e000042030000114003c030740500240c2c0e5072100b803107041d05804121603040c2c07403a600ca80d00c10710a00708064003075031069601b145804c400060800c50810020710b001c000000d842055017003500720f42d03103800d003901038640546030f40300003400701d528034081100310101c0f1250070f003003016145d10114180c40a103620200141c04081d188a156280d1201030f1a200d06035003050244910030b1900180b84088c0e03a500705c09481e140b40f0fa021702100b2460381002298411003d0340c1032000041240040c0745103959500c1001000802105400396142000014074040c804100038000d030000801c00003283c002027500f07580a09a420b04040031115030420f03038601078208034000e0100340213002031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 802293273 1250 802292023 802292039
    0xf010321030605031905010b010c171305040c02010c09080613030e0f04090b070207060e0609061e03040323070302100f06030602340f0b070512040c1a0909012d 70
    0x20701d0317a0341c0a60000e01003036201c5001150300382c8148401900a041e5600700e403007207804c500000c1c0355003a0b0017002c0100c00d0f6103400c0050119a19103002c0c0015030355440e00540401d4001503124010103042003d0f200c0c42c50601084118032410002c02010400310502c18a5103642d10111381451410141c0100000b134010701c0c0c200c1044c0c0054a0b1744d800341c4174402001406a00c590000f152920020f001a8108000c0e1014090650000002009080c0d51050601b104c5a00c074030146105a0180d5a11400f0a07412183c01700143c2c0220080131230700c0d4042061070301007a0009540c4441c1e112914002500302102d0303d504000b08401c1d04010203035030001548000c00042c0d505091103180fa00340c0c1100340c40c8044505131801c2c000f0120b00424210b07100c100c2802254a03e608181e108006041151074168860f43c0b81d9183c06044808840f00f0314151028402110880040c40803407800788a4640742c02c0d0010f0005829185c14403507824427900d01102e022202d02940e0300424403030f000b6408a2880750f00c800b50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 802294523 1250 802293273 802293313
    0x30631140d2d0e09041e05060714031e07050f22060f020d050f070204110d14012303070e010806090d0201021602210615090f01032103060503 62
    0x141881d03580319101902c800403841500b0224098440d00c8401030045103000303021041e5001001070f2440a251400c1500340600300785444d22140c07188025029614011401400b10000b21101e010101828410016002d880f00b003190102c01c00a1000e89850b640c02c8400c0300c05116803005079090100108050981a1000741c680441d41c4e65148014a841d4a03240d01b15028070b0031007005030040e03001ca03458490f9940580c004084501d0007101072407420b40280c02160a41382c803c822034840c900c00141c820061400e034428507280c001e4030300f4a107102d540f400316580300c01800c0d030441b8000c1c0c00f40140c03440d0959408100000040414a0903614290307035070386403c0d446000c201c3e600e0348140964120b00c95910301c18407c0300d0007001509035841440c00310360284518802180081d4100c1c044070009418800c0f0304212041c45184c80d071644110382480c000501c000090086c00c030612510101c401030001811103c407a03c2c00c802c00424545c40250210012000f400f2641d010503014001d41200180302400024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 802295773 1250 802294523 802294547
    0x7050c12010903231c2406080f010f15030e060a05060907140301060e0303130b1b01020f0307050309160e010f211b030606090b030631140d 61
    0x250450681c06440c0d0014144408921044403010100603175a8050b00008100c0d05040c00303d500007410000e02202920100d40f814403040f0f1120b403580b020001c241e0300a0071594041c0c1c030382d08091055403606100e401c0b040c500c1d014100b45000c81000d00f1110038465031000282140d440100e07445820503841c3c0c80002c19042e60302c203010300f1440c0001000070340115017401401c04500e507041d14581c6003005c02c640203000744115681c0b50004100c4110b014002c09840c001800c40c44840d1660390305041101c14003040f540c0008030302c59005010203c581100c8400303503607219115007850740d034903070302c1d0300e40c070703420b040d00c02c0d10060080c4d074003903000f00c1c90620546005060f1281c3c0101c40c2c0342503480d600408814400c6000c04450315410107201d000140d6402403030204908068903c4105035202e944040580301d407a00943c80b2aa1744260242851400f000219003004164112600c800140c821100c10031311540851203200f0000700c1c0d0041000100d40920600c18162000d0f260344141000c2c0052985d00048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 802297023 1250 802295773 802295777
    0x10060b03090c1813030903021002010b0415030c03080a030212181212132306100b03010609291606061505120415020304030f080f0114040207050c12010903 68
    0x8503403207002c0e050030b2200300d100c004001400306207030742c0719002c04140740070091045017000800c0000000580303850b11749084446485d0008983c055007902400100c4460200d00c50108241603001c2000c41c0e800454142500d030003016283e69540b01503002d40203441000160700310b0b260510100800b030a110100b40c0c4054411600780d80106c03440704c110b85058004e1104c0614000383d4080072a9084440918046000344100f4110721283c054045140180d0720314086440560000e508001400c140e040c08440a01040d500444c199410080002c085d99258019454100c00b55500e0001803841386091440542c5881c61096883c1a030600102244a012900711801800c0c00d0010070540c0740440401c01d01640f582d500c80c02e0003c4a0045c90301c2d4800903009940d001400e481d8180c2c0d00e51240000d5200354080d84610075807943d0140000c241e160b004081c240c02c01008001445805440d003000308001d44205c0300581c481070035080c000e040c808607414080d8400d1031211401c00518040d08030216041c026 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 802298273 1250 802297023 802297033
    0x161e080a05070b010906050a0e091c03090b0f090d0f17010914101a0f0705240106031503230d0e12030408030a0503100e0f0103060c020309030d1110060b0309 69
    0x207041c5c4036007980c900b0300a103030340a43c8411081c0000360055620903403182030503040315010400341c20030000c410306526081e0f00090700c0e00101010f00c040008207903041410b0400001642c03a21000341c0b6240c40015030000c04120461038440b441521981c6940c0f05140c03289080c24865a40782640c3c00200090700c140002d8045600000e000308401c03c0b030500407605c1307115200e524030240c200310f89000d6008840440c1005001e0154801060b030400c0110144d40c00d1709180e80540d40c501c1d401e803100c0e00b416417190003014181244019820600a00001280da022102400054180b51501c0916685030f464006c01c1c46200382c0103850740d61120714011251b4040d03c00e0060b40440f000b15949900c101c0c0580a07140d403041101100311449080110b5010a4800e00f207048184c0715501d030b040c00c800035140501210081c80c01801030025034840c00c100d0070094001989801c0303044000c0790702c4054085d0311809003e2010819180307a2414050b0319000c2d104024200111a01c07810a00c9140e042600c000071188a9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 802299523 1250 802298273 802298279
    0x80c04060b1801051b0f0309041805070b070303022b0608011406121905011401170a02010309060f0e07090f020f07120c3005161e080a05070b01 63
    0x30303041210346401541141099026000b801076903117600c0000303d10b50f4201e40202c155040340c0144101c2942c03081c03000142d940c81d80d000b403c100a550301483ca180c40c24103100000c1c00080e400240100468010302c1c952912017030306050176002070054101c0991924100760b0b040400421003081442442184031040101c46d403100b12050072600d14050fa410450348090110b2a00d00e000c01c5505403030b01c03400003142c840761020b0140054040c401a81202c20707030b46482c1c5800c443c03040d107443c00c0d014240b1685005000c458001703005d03a8417041c0e180c000e418507666071603001c01d0051640001c8542901d080040c08200031701940e00d5a1140188a40d00103140341ca00c041290034403038022103890311803a441641c200212a100c020171148401d80200a000112010500141c00c0365003401868844d000703184c41d0b650000503548500b5594802000410004101201c51491250380c900300f15a040a09404486240c400300d100c41da040310b4015003200800b1640500a5512600401b5100e105120030f15043e40d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 802300773 1250 802299523 802299539
    0x709060f0e13091703071d012c04110408100e0721020a0303031e06030302030a0e0a03021513120804092c01061401020303100603090c0f080c0406 64
    0x300501000025008048440d8a2030030007901002421003800006050000e940c40400104071003011900b07000c4044100010760350040801100c00c0711070280c840d0790b100d00200082c01d00595064201c41280f03d00700800d5182041045d503011910054400c01c80260007141c01020740e0040c2c03241c03041910517a045103030030000c02c2c000d4031402c202001c0108200c60038803805030540128000c0c4c1c02c1034488016a80800b6079540ca43c288000c3d8000d480004d8810700381b041001c40161840665419541040d408100286c0e001044540d030510030f16083c00100c0e560070001d403102c1c48a80c000780d40010310540304a0710b0041e8100800c0101075454144480698800364421709002e44000a00144428441040601c0040e0040070200c0002c45540c0e074040d0781e04160007800040d112000c0203982d551a8148a10a5031840380d4803000c400340029811850842d84241c0c0501d0503004000c1016140c2003140d040207044680f803805019031104580700c05807200130329691541c3e541000c91180d41010360002c0c0d001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 802302023 1250 802300773 802300787
    0x120c050d0305151c171213110301150e06030102130b19020f0a02090727090b030a35070614060619030b010207080a0501020304060b09060625080c0105070906 69
    0x901c4c1402214038840240c86041030003102c2d9540c0280e1100822000d500c1c4484110002e109041801114000e071600381890740750600c0e15111107010368504403850140c02c9220b001d030011100340c00b180151559481d004a40a801120040750300c1d880c1001c40850303000d14082c00303840d0605800035100040904010106e03a14030404084983c2604403507402c030f0150821484442c1c0c80102070404500361420042403c4d402520b0102903602e5580040041c07080c180d8a00071804072351001c80082c880d900b00d84d1100d80035040d06808140d100d04905040782852108002c15445031008880e465445c0e940d40c1c10a040949861105c1107031101c117100c001415840e02c03605460820049502010448400d0070003900101310050a0506500c84c568001a001307a0070040440404c2c0f05030009603e9040c6032a02d0400e4607028130360070b842002c51608100c00e68031000169405542c0f086000001c481981001680400c120100a006100d0001d42090301c10815041540201d0680e0360314011240c1d50581140c02c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 802303273 1250 802302023 802302049
    0x90d03091d01052419020a0c180c1d0123041e0605070b0426030c0a0311040302180c09060304060501140d08040504090c050904061b020316120c050d030515 68
    0x501c0c4284100d84401c0b41e00354030f080b175105903801100d00040d000c5c7c40e81040840c4907072148042c03902c200b120044400e03040c00741d80e00c0c1e803842d410300c4c2c81d803540d80e140b1084d4800415140d050401118800707150f0b1045144800030705801c0c80880240d9103d4441d005050091000c82004071081220640050b0752417082044580c015040001401961100c0e6a40f06500500000704160340c044005c070a40b80d50905801540200c1d0903200d050382d15160b806000d0191707180010344c3c010142d0103000400c007580781d06650030f0b814003d4074518020340d41c40a43c42e50403401802201e0342c11030000300401080003c56800b5905807401e907402000f1380e4000d1000c116940e00301203401030004200744005c0200341420b1308103080031840303141c0038000103480750b01280c00010100e9040d140580c6403410700421810311182420500442c4c4043c40c900b0444684500b070450046200800c6d415a641841c44094410413501d200140d114003a40c0810400a1000f0050141030701c20108212500901140616207900b02d0a45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 802304523 1250 802303273 802303339
    0x240804020303120c1b0d09080109050703060213080106150801080610091d060901050f0c041215020409090507050301060603020c1b0f210d0311090d03091d0105 70
    0xb07405000d480c49005140c000d0581c980c0110b00317010054080100b0140300109000040c0101103140391070b10010118852544806280d915001c0d5903808100e0208800c02030f07076082100541c1d1000400d074800100d1006900503100ea5103030031008202650b4480300000380d25055600c0040690300c0710000758503030009485a51646008507000c02000350550060b0094142c1d086800c08029240000541045811941c00955035503d1040101b90003500540310f130800c40f60b80d1043d09040c20305820001c8002e040b41c000d0309201e00e5581d60101040d02d0380450b0003a040c1d4200c10320540b41186001d0fa65040c807801114860b50806001113021031003071003603c400e410902e00074001403020121942d14215444030799a04241e00701d075079031060344a03060040c4800c070400ca483d903000c0d00c01e0140141402000001e9008040c113142c1d1f11040941d958007030720221a0111b9030007500752254501994500110780c00947c0d001d44c08910089030346007030720281e4120b40c000da588400321280d403804905101241d0100d484 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 802305773 1250 802304523 802304527
    0x3050708240307031104050702030307140903390906010f08041e0c060306151205090a0b0123150a0804060902061303110103060303080112020a0e01240804020303 71
    0x110303000003040c03900d400c440106007440d00540110042800e107001500309a60707089800c400c041050405200d1740d0761003105403020310300318103046000a125560700a2144101350000c074080a140c1d078284100120011240700d014140030403a140850031240a484203801e000801c138100c406824002c3c201881038605a41d082c20000901900f40c80701c4401510070340701132502d1420ba020340c0c1641182075400307900138901c02043c1071030400e004055510603000015000192101450b43c503410004c0001d40c1088102c0120b1740341d0b80e0280c400d280c041e81103405825030186800000b010f20200368060f12a4101c1d0342d0b4441e010f8208420300c80c030a00035240e50410f5102c2080f0690450303100c0c5a00c150418031801300420414103d40014584e904051110307000100d6142d402c208010300364031682c4064100b070038180f12403451504e01402d81803051040c0c01c041d0303070207070f600b0421556103517200405808031064002c402d507120002d0205e50010117442c0380e6080030300e0f1080043c1354001c58460b4881e40d80200194 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 802307023 1250 802305773 802305781
    0x606010201050c0f0a110d09030215090a120602090d030f02070f030803040620070818011d01120e0610030302070f08030d1a03100f0510080a1106040e100503060703050708 75
    0x130b51039600c00440c40003001020303031003800010020b02c01034141c0081c1d680c81710042070640c01000f82106075220010b104000c200f09070100d5456020075141190419200c4201b4031002e81040341c0613108a49140303030b0003a00c074690b1204043e0015060000c004081d800c82e01030035181c0b80d038010001c4140c04094034440c81480040d0000707201c1d800088190f60320340021032600d2091496414103400102e003c440d982c001041c00500d1103154888415628000d18082d0a100c28a9445801c0700700010400d5040050900c42c40040c81c00d540c00c07500b90901d08001b02ca0b03480c03a02d800304800307490072400201c005010f408000a0b140e52600207503401c1e41d0340e14025501c5c249120407d20010040c03501422001c402042ca803080d030f69024000b18100c15820b5002140070030b00d061490048941c020851030340a00003640c14000c0c0d56001034807804056100c5103e880d480f185000141d080d0185034440f00c003051110301002282c080d1003c9002c1103070b1080d01150b405888044060b0240c0d6000c0b6030032800101950002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 802308273 1250 802307023 802307047
    0x4140a020a0219060c021c0f030e120c010209091f2c010b0c2b1412102408040f02121e1006140904050c090f090606010201050c 56
    0x1401900c050740115412000041d095041100c4003520659105554085c0304245507018003030582e5400407110110710f04000301c0005171008044041c080c1c200b603607030155016105000c01c6845880051011307001d0321192400b441034040d600400da0907008440c0040030030640d80c11101070b1000c089006045c02900350400c0144030240544a10008690304a0340b101c10f0f40d6542140355030301034417a07560310b683d6506103c50710b03e1401c0d594070820301105010703a0400300100000c1c9412101e603516441c0a40845c64201009107407405007542c205680101481032003e5510741c041e00b142120340700300202c21449a038041000d60841c00902400200c1c1315200003900050420406004281c0700030a4065100c4005040d107283c4240d07940e00340c001900c889000b83e0004000c01155409151600042c44441d090105c034006000010200e1030180701d0307003008141040014041c044400b90003401e003d960340380c21000c10100d0034043c0c81c181c0c0140981c0d0049001944180100f600c654540104945418488140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 802309523 1250 802308273 802308277
    0x3081e090a0507080c18100b07061b0f14130b0a0206010627030b07030e060f1009051501050307200136120c1703040308012907020f270604140a02 64
    0x140341482400507c00f141c10940138000e4050f0600443c0b0001c0c2401c0303000340e00c001c00c02c4501c0070401404500016001c00903400700c041505071200710051074403240c02c02c0c80d13101801c200b600904100100440e070484002d0380003495038102d4065540305804820b40c517504c0007038a80301410980890840d01c40c00d102281251404c01c0c4c02c1a41460000f4144d034101d259941045429100091038035019000c0c0300150b500035400101400329010304100c00d082c17440c407450b00c0d056600760f114144480400003c101c68041c41a04000d6520040c400c44039219004015009045030402d8040040c25400e80a11232480c8443c0d032070152800b240480d001030091745402d40c041c1d60450101081140f28902c0e400020703080d001c0003c02800712403c0c2c40d107030f04003071501504242c07058102c4486d07142c41c01021846022042c54600d44031807801d400a0b078500d03c60012030210090f0410740f603007282e00d030203014042c800d4160002d1100c140b51801024540c40341420007003a100040d5888102c0011407010074050340440d80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 802310773 1250 802309523 802309531
    0x30c1b0605101a090f0a051239090c0705030403030f03060603060503030d1a0a12020f03010209100f05040306021c0e070812180901170c09011203081e090a0507080c18 73
    0x4401802607a500006108454441c0810046e030000101022a88860400d03c0c03e055a0b44003050071200100000317011070089024032740d1181c7c51510108940da201c40c0f04441d00c4503040016250780b81e40301d08000c2c0c1010b028119901c0000d20303080700015054420301c604030990350010b02640c0390840c40741800c000b801841c3c007248107220b481d40c814061686d030498928006e02c0205048010304d0028010008003200050740f1314000d07401048201c0e010750b10341901401d40021410022141070341180120b40c00d009540000b40054030000c2d201e04200c1c0e001c1050680f5008000c010b0000e04600059942c440349148109000355000350000d81d0814518400b506021103c42c498407207007450700c40080da5424003a407001e0241050120215081c95040c4584002c03203400f5194800554544507003605022001d41024041142c10000304803031100317201404600c880c1244011003141050071032981c44041300075044400e8410b81000141d240c01c0070a495141080040c4465058000e40c041c801c84d07610014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 802312023 1250 802310773 802310779
    0x30e19030b2502210f030615090418052b050f450303070803060607050f0607022b180305010501030f0b0105010e10030c1b0605101a090f 60
    0x2668a200d246082d5107614500c2d9a03008010010750900070508041801c880c1c0300450008000124481032003000721b940001003a240c884001c1c6003018609000d000c4c3d010b82c5503210b170034280d0175080c18602e00300d2036036554010000d84643d4688410241d46003405540740c100f4030002001d80c580014015000f52580b00503401c581c40c034058012004030081c4460b08540c210540848541d4440a4909407502c00b00860030510341070000c4590340000d41d83d009410780100503c0000000a1050b01d498080d110910b60080440743e010030540e2a954803000110313802d400610405a05603440c444c40a9007114400f400c0c0b81c86c4c65104c101550807541d01c1103100c40c10444130000103001000078000d00c0351500031070240314200916001e80c0f81803100c201069016a0400081900052482e5221a84031300420410305000941c0080c0c03100550740041c410a1003000380005075004828000d1a0308154842c40c044d40a003a500c5440d107801041401280243c1e11900c081400300c01594249844804034601c401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 802313273 1250 802312023 802312051
    0x5181e0a060504060e070819020628020a060c050406090b070f14060103110603040b0a050402030708150406050f0c07240c020c192106090206070b0103030e19030b 71
    0x41e03101c860649900760b804031903044d0355450074500d240707080c002940500f200c48050541c031030440360342c3e0400000c0310602034420790001402d00d1010f0b0344002146201d000b1016003504001d00c2c1d11001e5180d4100e030206442080c02d10131000f14661160b0211025100075803142c0611074108840601b05400610041798260740401c400c0010454014003210401d11110007014158114680090380002140006008620600c284000604c08007a0340740e004184002c0005d040e600d90000a180a400707a01c205014040c2c090088440c0b001e2444441c441da00442051050340c45450030203202000231510078680c04018011900000c50b11180c6140c01e40c20080e00c00b1a144610f10080110303100807107224090703407003030b140d03003e031824601802800160742500d034981152030625003038907003404803200c0d000301c0c4000c1c400c04d0204021a4890741c03020750064102c43d11400c0c14900500c03544000c2c0002c3d0301040d5401e9101401e40742a80589416941c80d0481920700342c0b85075107501d944100a09803002c1c030481 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 802314523 1250 802313273 802313293
    0x14073002060d240b0f0f0c0109080307180e0112020d03050409060b030618190f1b0503040c0e0705071509140313060e03030414030313080a0605181e 65
    0x200e402a46943d1440c0b4429100640c0080c582161000095205002024051241a00505691003a940ca0000ea200929680c14180d01d00c1030051013815802000c040000c0f06000819500c4040c0210014415070b04000c481d40791240d441c4490300034850205801c0311104440014201000a01e007a03a202e410000d007031580b0360840741b00742c40745900040c41d10700c004000c0103541e1511020f51049400385001d094090300b0945c3c8400e10141c0d0100c00d49000c1138a50f0324102406001e40c1c40300c1b000f0308000b1108103620b21403410007881035006981c26950311481440100b03100e491840760310701400d09629054544012607980b1000107000c51445661542d440d020100440c407012040052205030340c4c040c0da9504542d06079000394030440d030881401c00189000034844c0d92400004c407002d0b241d46005a0500a0304c0f83c00207481c6109140319500514915103001540b07420010780c841406204240030301159407901302c0040001c0150b448060150b010f1554a207643e0104a0041200c0c2008000c1e41c860300c030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 802315773 1250 802314523 802314547
    0x50c0103091502071523070e01050f13030c0b0f04120c0e041505181f06050a0b070b150108190e0a03020c0a05010c05031213020d1407300206 62
    0x15904c255400c08060040100c078140034403c40c01404050071201c12000940042103518202c02842602804034013080c03500360703078002d01c2561214080c55208969510404030740c0d01c040301d00c03031101702c0f0f185400039004900e49200c501910f000c0ca42c7ca01e520b03420140350500303000703111400b508182c0701c03804140c40104020003c020122320941c082ca841e00d03607a02c00c15102108940f0010142c0940c2a80e50101c0707550400e01040f150b49071414000700300c0d440e0000d40300001c000c06e50740c1d1109601110000000412420090140449601800d180603a9607141c0104450940d04181d145002603c003000146007614950842c03400d20780e00d140e0015003414840c45052070480d0420f801d40240e03111181c050020700d416940400944800e1030071342c1d21742000790b8600b50f072800f4604003034440c0000c04d40011000341e070450003d400d82d50014044c01c0c000d186410404d0f008012541c1c102d005000340710003c905104411007a00c10300c0d03d501a0301030b5058492141c05d08483c007001049034004420810000109 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 802317023 1250 802315773 802315777
    0x803010602010911030105130303050a230703150f030303020717040f0509090c01140a0e1011010506090601020c0d0c030c03060c110a051504030e1008060f0d050c0103091502 76
    0x44035640000452a90074142100e4418480c1400c9201e681824200031540001075a00e03d06158181400b091079103c140050000d04a800014041c01103003284500030040d40b400014080c9a580d142009581c1c20302c4403030b440290217800b80e418400307007113070081000a201e81d00a0050340d000349644941c08041e47c03801000c0303520690081c1c1c40310451101c18412841c10946c0290454190002422030008840c0082d100f01242054001e08090100d80030071f58500452804440040041406c4032501d40400c01501f45000c2d030700c2c00e005541c0ba0000281d01c0e4104284090300445050b001400075090072400c010b840c45041c5c104440f801c181c1c150000c0022081100c004c0038500c6600b000c501083d4948004004c14100c40184000343d12256124021034030100ccc03ca000142c4e070020f0704855540714103042c1e0703040000465240d0480082c2500100c85680000103502a4a04039441041520402c040001c01c004c40c020151094001203000d601a60003940152800d5100d003410341440640c42802504903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 802318273 1250 802317023 802317029
    0xd050a0506010e0a0b041404020904020a080d031407020a11060d1d0a030f020303041a06010311030f090d18150c05031303020112060308090123160b090304030b0c1303080301 76
    0x15009400348103403643c1da4017540e55a54416141005100004a018102140b002c2c00c0a80641e08d90f101040a540325100050054100c0300200c4507070381034002000f00200b0381954034507061555500410000f80c80880e001d041181c03c02c840c409020038074000c00080d903001c9502c40c0102692110760740e4880c03c05c1c44060158941480140c4150003850401038a0070302c5c8011041f086410800401c400170f2000750754007501c410150490300540d0765010041e0024020107100010144001c8100440c40c035881042e41c0c070034501c00c410713910001464282a5124a204004401e8040606a0600c41803202c404600c1c00c071036040c9086204144d0b02c0d11924116444110041c06809500d03070180155600b00001b918200f4a512040143c00e140d0b0310380810a00800c0076850400c003584400d00c12440c6c40800102014240340c82d503e80d2a5103071180760f6030204107610100c486101540002e1503550000c4240c404994010262a442d035580700b6806100750b0003030107445102d0440d03d5000c000308020030091406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 802319523 1250 802318273 802318289
    0x309040b13110306041a030601140105070b040b040507150f0507330b0a030c030807050a0209130218060a05151207050406021009030e01030f0207080a02010c110613020d050a050601 79
    0x3e02c2c14140207100c02d40d10510000307051250841c102c0c44841c3c400040f00c074112804540706010f5110b000004840714443c0d148040c201c12031303910511007404a52002540a28440c03070445000c280c3d00c0703124804612440d4008001301d003003140c400200e01c0c0550000c0010030300ca01c40007203e5200c40030005c0c0c0c84020360f26140348028429031592004000511590361000400c4414005061850755a041104103900008200301404039602041100c01c0005d0404268000c11b00b11051618540d24544070440310b4080e80b01c0da60318107003540006603451165008003005480c554505040108ac48485001c00c0c44040100004014000081c11a89440350154055958195035a46050002468990002c11526406180245202c0004d41007007480c0580b076020709012135060343c140c007807400034000e04002916092000070004030071a0306521010074094a501c4066591001ea08295915442250080d400f00c195041140c0035240640b44844494410b00484407900055623a40b03090010aa0000207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 802320773 1250 802319523 802319527
    0xb0307050714030f0a0801060e0d080a110d050a02070f0b1210082d060618090a051906050c030907030b180d020610050d151505060313020109170309040b1311 69
    0x920170b84c1c004d030220300402003458100740f9224010700245010420b19802407001c0c00004030740756414010100516140030328803d968850705200005095603004c00d80c030000600074518042400c0c00c3c01c4481d14151025980d0941c14036240440c11803440c0c0000d40514043c800d401400076a4010030031405070b0f0808030030f64000d64907051001c54a0070907440c040c0c020b4550444800c019240e10b5504000850040100b0b94001e26203920038900c4c1000b1101101914a01490310340721003251080c40c58000300c600c1418104001d503500390100c0d50601082d01d290419400010080000c07498109885070885440310700c108403100010350003480c080840480c0005600b1000420501451402800000b460241c0d000842d104803540c1e0850310310384040d00d0015041d51084400240b2070381e041504046c0c04040d202555070304040c40161b40054170703038500b2070000d403d03850701041082540c20303c0e655084002000f03500748000c1000300800b420450031300d55008412008550b40c99452809030843d064040c201981d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 802322023 1250 802320773 802320787
    0x4301217060405090d120605100306080c0a0308070b0c09061b06070f020c1c020a231804060c1707051b03030601020c09090a1a06190b0307050714030f 66
    0x640e0911004040502c0baa02e0036007088890a00403035101645c4141c0e107080090303442140e284900600054010a402c0360a08040032102c0b0b0b01540b01d0320954090030112100d034a041020081c4451450100508060301840f944c2c0006500f04481ca4100906134401421311720307071340040743d000d0b0820000310745180e10103550841280e60901c4640d81040b114071345103540a0f02084069900d00010003c40d002c0c081e18558241030030030302403418540640c0100070001d01680c40c5881640044203c04480800407042002003192902203404520341f00c041030300d4044c55590b915a0001040041d240c01c0502204c02e07528034119070641c0641c1c1c4650300c0d5480d490344980c075a0607003c256800c40f00c2e40c40070552080050040980c0c000401a401c0d01c0115101c030303007586d208901c0c27508241207030310000d0006110314286d5081e0441d00100c03501c0350806a4520010340110341008840044511071265070050810100d1400f601c254002c104180c0107a50b4a0100c40340e0348030741469a88520714209440e01701140c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 802323273 1250 802322023 802322057
    0x3140a032414030a03090519120305070210020303101403010f0e0d0e0405132402040815090607080106030c110a050705040b0303030f01060309210c0501050c043012 72
    0xd8081c010b041d0010003690b84d240d03401418202d0f8900419200d04000714040300d00c880c1c006603800180030181d50b007079514400340c0f401074126003160500301d1050b0b4003100041a190b01c0007040e0b900c84e43e0b40821580b801403501600c220000340900307100d50155281c140e02c2a002d6454041c80709280248401080d11003150391380101012500619030344501c2c105801d000c8061086084942c25541005000049070780c01899103a16035078480c406080a0b00100d0009214400820500c1c10b0012a140040882c0d032522966a121002101d1a2011809075030041c4803aa10942c0065001c0c082d60600040340f241f03c1e15528a00106690b0845543d07103d80c05c144008d003403500178580c2340d19080c4c0c021829401e04c44d41c0c10b4403214050040d0010103036203404410034840e120000c0b180e01d002070940c55900c800c010000800b042808081070380d03150f00703280100d20000b01110448003140e0b0103426100039510b86401803d1400c120709042610000c00c0c1c12820302007103030005088640c07503003902e406043ca001400d003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 802324523 1250 802323273 802323299
    0x6041d031b0705010903020f151620010804050a030f11031201150c0c1208070f1112190201050d020d0203100801060e0717250e090109050403140a0324 66
    0x45a030401a0f0030004100585070042c0301c0392542300840e4070a90303a6101141f501554001c21403101c20b000300210840003400340084000328171f4081b03070140c140c2c070300040c200668034144151401045d135440143d021010903c6000a485019250b00c1c006843e40b000455852841c0c1000c80d051075030400c05401040540c04c20001c2c0e100303000035402c01802020040d16003003440c1d1142e1140450726000c8592100401a624040710525a80041c03202004a02800c04030341e140b940c0e511030790040d0340c0b200000848000000e00313803906d50303601080d110811005a00440b4070760841e2000c0141c2c1c80d020f10441c1803208941c0050f5108481541e2854401454040500d094541c0340d8400780303450180030140701607107601c84202c150000c100701884c4903036120310100880c00c100400840d03020541c0c24648158165016500302c1d0700031021210b01800d40d80b113000c00340454100f5900200071810504072504010400b03009801d442c01982000101014081c1d000136091400764500185c600403200c080c00160102d030a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 802325773 1250 802324523 802324529
    0x20901030b0d0314030a110a0e1305091f0e030403050c100f0203040b0c0a0f0c091a0a4b0918081b012a051206041d031b07 54
    0x102c40422008603100640002111074010903060320020001d043c54085d604010410000007240c07541e42e030704101d40101103000244d1020300c034002c0f4903d07000c02d164280c003495011304403c002520747c80124801401e01c1015241003404426115000208031400c02d001a10046000360040d003908419502001846401d035075844c000e002001c429031801650005c2903038151181070800c0e9aa030100f4000d202c0c60a40341c4440148001c041882e008208080944e00304220340c1c9814040c0014004070658001c00400e00039201d40040d44203504019494070700b1007a9030180446180c8190003241c03041500005e8554880802c05000800c0302c071840750350815140740c01885807107810002041c411154901340d1920100c09010700d02c1c04039810300c060071212414100500303090020000c0307481410702c0200104007c443c0f0b2440c1d4515945982c3c3c0b40d40210f0440b082d140c11110402c4c00380d0395484c1000700402c100558211402c0c05006d18059007a030401c0101000e1711400030041161902100d16031411045070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 802327023 1250 802325773 802325779
    0x31f0c18080c0f01021207030c0201121b020c03030703020309040b0a051e0118050319060e0d200303070813050705060a20070b04091e15060e0301140c2b020901030b 72
    0x502c684050100e006c0541d0245d60341441d20600d52981800100c550384008000e01c000b0902d030450703001071580d1101d101034860031281c0940d92010a88400c00d5202d010341c08021740581c200300150042c40c5010b6210044140d0020981e08080e034540001c034a091070210394030b1302003205541000e00590303001403c150024070f5130764102d0340c00ca0501e00460b440382c103d0603204600d441c80d142040100819500503030700345000b81e000c8964503018518000c00d00100012082c020390507650400c00d00fa503000c01102e00c0b5032040e40320411540c42c1c0c41e0b85010f4080075000c06481134041d082c00031825581708001091987c41c95940d600c100c198250019402084003181102c03660320010007046408008425542292100d04001950f00c01000d00108240030245a0759480742c680300003200c2c0c01000034825020307525290396058009002e5401d140c00c0310380200f0340c40740012504001480b0b00d800380004103800c0084181c1d90718202d5020707122a0125020600c003080386600401d1520341941e062003a405565011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 802328273 1250 802327023 802327033
    0x60f09182d1410090c020c0301021809060a1508040507031a011d01060e010c03111c080c03090c100537141909080a0602070b0105031f0c18080c0f0102 66
    0x1100000001203113482109130700c503268031000210780d000f802444074146d00540290750716481291000c1800c80c0d45850207109030742000103d4400d082003450003082d40c41c000049034110003200f50595002c103000b00100e0b6940310b508400303c0024001c0c0c0000480f010100c0c519540355050005400850104c2402803c0c50506c00d4010811103a01c018151001c54007800c140320610443e080456000c0d001e0191040d4510400b055510040c40085103000280170a42e01c00519031201d0100d8040c2e4802590008007543c0500112002481c22107049101c008a50a040349840c4012518032692084501144500010240f00a07041d14180c1c20800f041112480c046000c41030f81d5522050900070b8220b0051000d02d510f203c1250540034007001c0018000d6642240d040780401d1030720300041e501c42c01c0115000302e0020000112401c0c001820b58075840e200c1a60700c41c03c0044541400104684004a41005070003d0352850208000074144e029040c0c000103000b42c0004202403204002c6034403030700c41c11035001c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 802329523 1250 802328273 802328281
    0xe01021c050a0902040203011d0c04080622230c0d08040b030603070b0c0105100914070f0e0d03090e0c0906030c030402210d0801060f09182d14 63
    0x18411018a0060003010300152030345492000784010181e07000025080791001001041d070361005810480d82280b0340c1c8030071340260f50352202c40159000710b21400c100b039888500410742e00100111103010072050150440115481521000205545904d110400081f0803840d0a80f107081406255080a0251181c54220700d141e030b649071403481a0303c01c1186800f408404113500e40d80900801c40101036030f204039070701c848010381c1d8139008042c25694941d07140180000010800e40070b0140740b840c44a0b0007088203059440c404240e5040e41100c0c440010040500340c1c4140990710b031842c0f004001d0007590b078142c0d585d0516008058080001d020100d201d003042c00a0041c9030389100490764051107032b0411a40725200c074404580c07800030350a0915018114280100d04280c03001403160000f0000b5922111166030700d4400740c1d4040c4003c82c2100000c0c402c0081801404407440311203028000419000070f030301c0f90801c00c640f514040c1542c1c00c0d064401004801c0b100c0c0d6100e024280183d00e000061a8003410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 802330773 1250 802329523 802329547
    0x301150809012903010908070309090b1f03050603010b0405011d0a150302010f050c0a11032a0616020306010905011e05010c02150922270f0c0312120e0102 68
    0x14400404080320340c030001c0f80c624a031005c0d00710708070880c0d0104000b40c60303c80794603000c1c3c51a4441d0040304400c0d45030407040c030803070725144032507100c0e14465803080c1c020801a11403c40c0500307402080d01d03805640f9804e21580383d0301d4502c03d00e4000d040c0306045503078002c05441025007110000d058100450304111041749460090030030710301207980c2403d1001c0f12600c20354090740c10703008418480440340a10b1403050103000c02d40c240070120203400c9054884140c401c0d40c0210108070b8802501c1e403900b039500c11020103828460b00401540c002c484120001d8034003640080c3c0b621400742c01441415403a00c004124a14540c610700300230840040084410710300700000240740c2400e204010b4480c41482034a01400c540410403113000d001c01a00340c420703451400b1200c08a29080e5800e100f800c902d000040c09107603800c450340d09881411203482e08030821564072044500604140283c416101d0fa91740000054448050082d2000c11030700c1e5440b100d8010704a032003c898444645440d0b40e4010443c0f120410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 802332023 1250 802330773 802330811
    0x90507020c01090332060c0409110a02071e0509040f050606180c1b010e070e0106020a0b1501090b0d060f060e13050c16080702031002070b04060203150402030115080901 74
    0x400c0300000144072032440c81c00c20004810510303411540d020b206c3c203105030901c1f80030041c010f4642603079080c42210908a400d003411b220b092043d80068004042c248840c248a0340c000302c80b5101e8141580002c0d840b00c0009500c000f0070713242111925281c44070481001414400c1d1940100110760001b2140c070303001810394240720000c0c5956a00600007409c1c00002d0b1103451000350390001c04008000d417040300c0d81c200d03590f4141409002c015000c0ba200001b0510320000c0c244141b00e0303209020440a490b00a0581c50442c3d81d0822030b414450a4080850769001002c0981180d42d04800d01240061404801106080300c40c2c200000b040301d201842c00702515041c8071071501c00c00001c800501075030b45403003050b0280640428403082c051010812170a10004202406110b070007101503c0c0c018001601780340c224882da550040504005d040000c010402a601443c1e0004181080001c55802c080000341240d00c01d82082e0100860807981c1c402c11980704800a0303010f5071403c002c002901c0f82c44502c417421 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 802333273 1250 802332023 802332053
    0x306130807020105130b2a0c0607050a02060708031510050a1b15020a08010f0f0e040309030c0b0c010506120714060c01020c03090907020109030e060d1401090507020c010903 76
    0x500d400900301045911490844030760420320000e201605860710324144155202d0200c0c5001400c00d07400a2080e0385251001200e00e2588074020400192184280f010070b03040000c0a542900038903214402684a043c0182031103441120300c95030b44d240000511105260b4848828000e4800303035100c628081d008030480b000d40c4510706145180d4445050459141a0074100040507055005000032000f182ea070054008079917581c80715819603880d020007003c040130030301c1004803207696a0810800c10341e03003001840c2c02500900e003400c082500c070f803a0615003a840d1b03400b8410a01c800516140102c41c01c0c41200c1c0c00000840e0f1815040000c6124507aa48041d80226035101c51b441c0c51218075a035440049500103c0124000d41d114514201c1d02c03900c0c0d410a054050243c066240002c95140c4107202c0d020400b503164590710801da903a8070500810740c02040c898500c045d5103060744024a16200700143c0280803101002c14140b50100d002810302e500d082025040c0440c12000f800010801003240e608 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 802334523 1250 802333273 802333283
    0x30601031802031c2706050703050408060403120c021504060e030702041a0f0108010305030f0a1209060e2505100e10030506180114100e060406020703020f030613 71
    0x10714081e101940380040000c000303506100f00354a000c0400400382c01c46a090559488000095140303d03038013402c491100d0360400385800e0240040c49100d016030b0103090f201d4001e180550500f926032072000e00d40fa500b0b55042d000b14110341004006015540100e1400300181d1000d0310740d1044520803400714050290005144076104c94155041038810000ea6508a030020014070407200700e4004080700c2020040041d004200b0300420880700e50040540034100d0f41c6c458015480e2550300800481c188d0491042d04040005180070505c084407d40100b00709980182000181600d40b40f2004ac035008540b00c4102c00c080ca403242541c4400c0e45072420404403003080c2d0f07194600f0383e0b0f06141100e51101700c125440c1c1c8091265040047e03217905030312103849018140c0d48501c1020302903a9900f183e20302481a40108000c1d420030491908107506e08040040c03c030b00303220280c0215400003441d980c10541210005a100c0e00e410000e51400c002c2410703014400781c001e06007600300b114100180c46101100545 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 802335773 1250 802334523 802334531
    0x60124020d120b060414030f010b061c0605060406050d0e1f0f0b0a080a11010518120f060a02130506040b0412030c0b0c0703021b030c150c0d111204030803060103 71
    0xca001c50300010220350f4002d103a19507441c0c0300d40264401920032043e85010784200b0703ea600c40703400144204194240020112403d00c000401c40340d81d142c00c17130f690f1034900c0f82d00d9204c0050341e900c4240141003d0280d50304c9040d2207103c1c1d840d220080300c5185881e4801c540c000580c10603c000b50300c2c9200c0e290400c20b080450100b41c1c2c01024006092580b160a401141c09000003c0c503540100701c01e0140c510809000c008015180c0c0111203900440814402c0e000070720610000710310704150030711030314102c0314213541d007103207080d505141011011070b84402c840d60005201001e10200700320f8031024100464403c2d09041c1400500b080e140110b005240080c0c40306080307501030500803130140304a9a440444500240b910b0540302c1503e8000c8141180548188516600a035442062110984102030014524074004d03101f00000d0143c04504211911402c204480c060402405880c10010340c584401d09820b2084024900c0d0082c40f040540040c0d0007400140b00180b580700440740c0000092030042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 802337023 1250 802335773 802335797
    0x80a18050f1002010209130914071a0901020a050f06011e0803030f060a090c020c01030f090f11130e061f1410030204080a060b090c0a020316080909040302060124020d 73
    0x31303009116400349942d02202402003514410362079085907052521503210b1240b044143c1c0380341c40d41d808150044120303c902007090b94040d43c181201501d4421f02c144101d80002c0015200c650401404490b41c200d80e40080005000c1c22401c11502c00f105524480c00071281c03480e09428a45900020345030441d81c12940e0003003a400d585e1303180c44501a05000900f0810340450b01340295881c13000e404034501007804c1c00201507545240c0c0c4281211180c01c5081006105100e5542c02d0302d00a080000030f0b0f1000e1500720140c160801c900c5410a500d061074014011410806600c41c8424060a90201d241a0521061080d056050702d0510741201c141d40b540194004002c1c1a00030b80101e030081000c51194501090a2180c15001400000010786c5d0a80380d644a103c0b094841303209103045c8001603030041001c6d940e84841400307602d1156001d0358445003040e079542c0000f440a05c05071010f4005a11200041c401c03408804050b91030411142c0c000f000c0074082c010044d4036400800096420700c90162040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 802338129 1106 802337023 802337027
    0x30215011203080703060b040807030b1b1206221d030c03090f0d06020f070614040f11011107080721020307030b040f0602030103080a18050f10 63
    0xc8070364411a4405844102c0c010303040200b01a961400051006c8198000d0405443c1a40240c000945182408003180001500916443c2080341d0005084550f403021218000b40704c1c4003a400503558039000903901002e50340d2044600c18110703100a0303c404140c0c0b01d0040c21400281c00c00f43c02d440c0e80c00903540c1c2d0041000c0041190f000b0042025a4a000c401c1c004e484000204450034403801c603500c100582c0c021100070300d552100840c2d207408100040c003404511601c0000c5100d050318040c3c6440c07152200301c800c05401c4007110700e0201b849034420048030400440d60b8084401d2039680c1e5100310350740c00c03a030311821071030040341340d003018050424803224800c061f0010000c200c09410b6485030b003c2280090011103204403c0015a00026190300103140203602a40c5c280d6111080008054074000c4440c19030183c05101100500440c0d0b40e03800c12500aa0702558a550210154141 = true := by decide +kernel

theorem cover : BRFrame.Cov 802158273 802338129 := by
  have h0 := BRFrame.cov_init 802158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 802158273 ≤ n) (h2 : n < 802338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
