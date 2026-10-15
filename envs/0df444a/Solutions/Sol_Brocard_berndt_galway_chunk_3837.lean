-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3837
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:26.272248+00:00
-- url     : https://prove2.me/submissions/37670a27-13f5-4a02-9463-81c0ebb5dbd1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 689928057 ≤ n < 690107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 689929307 1250 689928057 689928073
    0x102131d25081b0c0a17091c020303040509040b040b1518071b050105100e0f190212010602010504052518060b0a02032d03071b02190521 60
    0x2581c2d0010010070240155142620801006003054014985048908050540d0320f00301c1c40c103038005a410f98040316141c10240803207a56604c41c01c81400e0451001421804d0421461000902e58822030f001150051590070a1104200040b800c040c040e070300ca11000c5841e43d035000c2400200d14201c420550f4803007000c002c52014000300d20402504019646032800c04102090340440d00410121400c5a003a1354420401c012105103100b640c018160305013484025003402140c840700000d024200e900807003010b0007019403030207056040307501001040f9074090140d83d41c0c240281c020300d411241640c5030b01510340403504034510360340600e944100f8125001b070203604040115545100301c0c801d0a0b2050741d502408107400c28003002808050056500951366800080351030400740504103500202d00d001c2c01c02400b42c9021034021340358003420b507240c41080304640e4100040e40460142e8040e40010a0902c0f4550381d038010090303101075880c1902c00d61080c00c1e412107812000718540c201c25110b43c01c9070034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 689930557 1250 689929307 689929381
    0x515150f01050712170c04090b1f05030c07060513030e01111b0105071406180a0c0306020901050d0c031d0307020d140f06070305060a05030c130e0102131d 68
    0x2070b001c0100205c0ca410409210b900042203412081991203106490010034100040003650069a2010500b551a1000d401004401098110300c009a013010f20001100040d4900c0495054070000d941040c014001420616100307410542c680805400052a5038643c100ca54090200720000a9100000300303900b134520740392030742c401c0c0e41c0882e01810040100000004500700390b075502001c64888010f4031440c01c0090341e405180758503100b001c009803c0444007602090007446800c0407260020b2003da03139007104000490b80f40c49583d12401c0c0252901c00c155604640c03541c0031504d200c12030728040d10074402c07107100c1c0c40d0380e03002d88040250701445200d003003000549680f10303c401b1220020115541c400060354241d080620072101140000d55030f0040208a19104820714000c00058024013108a9510701080403007862400340c900c129159024544c4c1150300350304940b000d240000840c0d0300c2540f41d0700c20402e0b1400e03140015240711178010128408032440410740603040034281c51108080103a00f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 689931807 1250 689930557 689930573
    0x30111090d1412040303080604140109050618090705040c17340305040203070603020c060423034608250905090f012115050f0916120f0c030515150f010507 68
    0x140f60033f030021502038850f6a0f08044030001805401c3e04005030410364189070611040300c405003103c900700808100c403079124000c180c5200f5046441801422840c2c40108041e68400015005904640c41c0320300d8410461907243c1c2c05030340124800c03800c1d903d1007950b40100328207038003c000300c9182039042003020500060700a0b00c541d02a80f040d2a0b03c2c0190748000d50f210303045400510400e62020b803614213080b1104005c4103072400d00c21020349004000d00380920000340901c40f900d20001400f140d00d02149010412140c9407680140b500c1e0340c8003078800c00040050082e506032141900840684c0041545100f10000142c1a01d6400c442095034464142050b0f05e10b50912000351082641620740444500300ea000d028802d180c90011b58041f402c103c102039281902903524101c200d01109000e00524008441200405410800e003a1014106040140d6a0b401c42e40c030003019449266070320000c5481c079420441c03051100c4810f4034400c42000e014881010035113601c9600054080184a001417440c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 689933057 1250 689931807 689931811
    0x120911060307182702030604331d070e010e130c030614090606030403050409020a0309030806093c090a0309060e030d27030503030a0605030111090d141204030308060414010905 77
    0x2c102042c0002a2272000f111103042e0b4403818803c401000315055802c1d80412094000e081940a00c424448140b401c3c481041c406444401004490058900c15a02c101d4000c03010080c0240b030034483d110884004001003070018880b80c0402e051410000d4511403501500950b6140580b0911040d44d0b00c8042145940c0014070407800e1060900001c240c540c00d0744040e010005003a2000a0710000c00d05006c1d00000004000ca44a0000a8100030703150000780080f002410321040b0365004810750803504901003035a020004c120010910401c03001040000380e000c0828065240c0140d055169107046681040c0251b401d505680040320450760b8034070800021040c00300d00c1011811110704a003075940d1084803039100740c91960000c01880410701c4684141401403070202e00070400034040450100c641d01034424024800c4601c44071000c10702140c20703074a000010b009400d50744036011482c0d00c0c0d0504d400c14001980040c4100e0300003000340c00c151241c842103010a40c00d00c9020381c41c060110b0007030800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 689934307 1250 689933057 689933059
    0xf040312110d080613091703071b0c0f05010f1b0804080a0309030605010f1a0c030903060f1b0c0606040b030106090216060b0d031209110603071827020306 68
    0x889036942888440610900c800340031540d0f81e200c0ca0381403440400841461034904a80f02c40e01c0d0021101c0059060080001d20040c8903d03c10f4407555180019039205101110141e104840c5106600410116050400a40d02c0035a10b03001c0a5441341c00450f040764075402a41e0100d00c4250303943d080c0c0031191191080a40c41a25000e1510b0307181d0303100302e0400e11000d0381140465402c0d17500340200410340c01810302600520301c0004840c0d00d440041d050a0000c01c007030201001d0000380149214030301380f045902100f40601202e40700e040144190504020445404040301c504020500c1500040d008640200041301d0003003090751241c00402c0024021052510303455943c41d07000040c4105640041c090040c016003103103070081c04504051064807401740748644181402800c1c0000071303070040641c078001c2440d900f001613a0f000300c3c6803440c01c4400e20044a88e001c40f000c410070a0007030340a00310041c11178001d03140071b9803540d80e0304000080c4080602a40301000e001500d4080001d41607014590201c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 689935557 1250 689934307 689934317
    0x903051602130f020a030e0d0507110f030703080409110a14090d06050a0e0115050105070b09010e19030e090106080711070f03050a021e010909021c0c0f140f040312 72
    0x70842c0006003c966200180c10b4050350049429000319070944200007061240b20f0141003007083d1500300500910a0403002414440801814502c84d16012001c018454014040300d191644a040a20310b542180c1f2030740c800c082c01e101c91038403442000c0702a04c601d448903454260400c0c880074210802d81d08010303460780e008864048000041540c50140e80e000724103903800000d8006035075840e103003500c20050105141002001082029903400400c941100c1d8121100d04882e888441885000d02101d509090f054429211034070405244a403010024500c292201038582c15082c0a0102d444400d01c81c00000c00c440348002000c29000380040e600712681e050503a01284c4d1100c4c0000d41d114416001616a036001034400c0c0c0440c00e210302810072140c1c03202c990000c00400040000d00c00d104038054400030319004520801c41d5500a1160403100060000c144456080710f40e005103601e45600d05a0001131824011924410170b80301261640307030034100d107589001d0171915015008015980c1c01d0302041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 689936807 1250 689935557 689935579
    0x3081204050c1f0906030501032102071203051305240315091006140310260a0f12030c12051803070f06110301050f090712110c010f0903051602 63
    0x5550303101003d4892a6108466003035508501008150041d2600f0100605181c100140042008420040340304a80d050f0340c0341070032a00020807810000c01e076111442117005080c0f294105900903000c3d0064503504800c0510701a40c0d64100b0811000f80515250b19003040c003099400e0740201c40007540d200c0ca0302c1703500c44890a4003d001c60480c03041162040c02c0f001c00284140302507580f003e07812070410350000b8440e046042c05200031804101505c01c44544a51002c01410310ba020110794000c158404c1050b1030808495040100d510417a100c0100e400200705004042c81e24041e02c00c5104401546d9070300a400c4621542d41001001c000d000c3e10072a07482d9070b50425501c103041005007041c501c0781000100103e400c0c40c0550070748989030180c0e8640b507014801480f040e210901d415180344c0088038581c156403200c200940e8121003d10302e921003241486c07030040700c01401e8002002d181c59550000c010a080c1e2041000469480120080c00500c04021041c91681540b2410a4090008101a141e6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 689938057 1250 689936807 689936809
    0x4090b04110a051806030f070812030403021006060c1403160807020d0c0b18030615100e060406050a0206010902071e0c0801050f0f090609030a1d04022b020403081204050c 75
    0xc44c41398501410042e0040c010400c180c2030500c48089401e003c000209051810719000e640c952004201d181d0640b01c0c080005020b0620802140850540819081120303a0300c0c2c00005165090100082d10643c141c40c1031382800400000855920720400e00320004481907a41d00c2041036840408260703404581c002d10103002c50302405800c2c004002820b400380c1d460400102079400c807410510000d102c0d4000c4002c100328000c2445112045000858048100315070400f0b0036640042040051500f000001c41d000c00c80700d4025000708610002a0203c4480360307a182ca070724003a8411014001c2116610240700d00740c4a0714403504000305449801c0720300385592618601800c40307404a860315400036000702400403200703031b450038190400c200030081d107218a0080d940310781e64414071a1070010804c3c188070369510b4172030401a1032900d4900030000c3d951000c01c81c00c5039030180000340d403c10030362039104400c00c50060f440c400c80d02100e920000882c140a03818080c1b8006100091059506024120300000c0c0c1d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 689939307 1250 689938057 689938069
    0x10060605030612190b130f0b1f26030409050c18010507050a140109020d0503131e06050a2109051c090e0601111209030c04090b04110a05 60
    0x5000565190354981c9000b01c00c01562000f8219800b040350402d0b220180c1d10b0040480c4a0391143c0c200600c207207030307880e4036204844a8005840203030210005910302020041c07003160b1140201b0141c01001c060715101034084003034498611a1040314480103c6446282d941480c0002c030a103034660543c3d08060303440c0c0d000b600350f420131612040c10700d00014a41c41e50300c0110840300c1c03d8140a107002e0b41050155038400350342340c040c1c80d8040e045085a030080442c11100f50042e43c1c90542c0680314403021145031070102d03540d07004600b030b030310204004070f001242d068400e000c80d00032149807034400c0e000c0c645801001c1c2c0f06540000c204800304029481c0f11084450321820500b88502c03460400900528a400c0260501c400941d480b0051000310b91605e00647e400500c0c6c03015240f8074200c0d45000d449980040c0c03044100401c03500c240d40141c8017491441d0400401030100c8030b10075415502d8044a00007084200c82000c1d1004140b080d4803404a8081140e428401401a00140c110408903445100140c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 689940557 1250 689939307 689939309
    0xd06061d0907090209060d0e03040b070303020c010c020105430c020108061903060510120b04030e01050702090f0a0b060d0e100e030708070611030f180d0905010c051006 74
    0x4400900082807112200c01006004010b2030070960841c240048800002c01a02c1030312581e00740c0d152600d2084030381c040d0510840e03008140c40041d040e0744285a00c3c0c0174019400ac221102d00c1d5505e88813405400e1030040c058140314000c040c44880c011860901c003181c00700c1c01e03a06940302c8006802d4103000252130600c0c02d283d04221031f40350455000410b10004201034001012030380030300e901d076016104880c000214481520f0784a040480c10365130710ba00044043d807a40c0d012481c4400c22400030303400c3c4583d45400e64001c9009654000101003144019201486011002508041e110001550036024410441c0e001484a1710124403050304400049050b000040e0103140d1507500e28004445500411007a42201d01e50a010701ca0442c3e0460000e0322400380311005800e900000500c001040781075485101000d0100c0d118030344a041c151510541800104d4414a00541c9020025610000002d540c00850420390326030031060f040c40c00450b544c410030402160030740326444600e58091002e00440c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 689941807 1250 689940557 689940599
    0x302101101152303060121050105040303050108060f091f0e0d020319140405190f1203410f0c0d1803080904050411030a0b16031a0d0606 60
    0x1c001c2500341980c1a044501c8411440c0890312411542c41c0f50382c4021640c241112446004980000000c605200b2541d51050005040e54608420401050703010307809079044c0c45030b00c0216207040d600c00e00980303a2100140c0e44190a42d002c20224941403c1a6204000003c0c1d10500800d11650641c42c0300e180518030510580960800301d40184941e10701203003011030b800350745042d02c0c40c01400c00c07480c4068030076030041d18083c40301c82050540843c0c03404614030040c1004000360364070a51ba9603000c0008030701101d0480000303000169500c00c0307603540140e485080768400196488440e4030250b050741c000300381c407030356009440c180420401e0030441c0380a481c41e120030f1806404d4640c402c2030f0040681c00740b0b008844c6000002c0340240045141f02080d10b20071182507600107001e07166801e080030200356261203141e040c452103400c82d04000132151600e0207240c080030280107a0800c02c200b078042c2c0f8048051070320014101003102003907261254100c0078807401000001007040d202c0c00c5540c00c03030380315550790 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 689943057 1250 689941807 689941841
    0x1504030b1e250c1502030a02090303160303050c120609040c09020c030d060815040b09071703180402030c07060504061104060c12020102040e060f0109090f150905010f0302101101 78
    0x118440e242c40c0040c0039014801494550b040e01140c0d9a40c4034041c4804401c40311182c2d02100007603c0c404d15174102c61841c80c0040452b9102d000071113030300c604142c1245c1c0c200c00103402e103404180180e0b145c2c400e03036101d07803403101201c6070a0380c0e1081840300348000204241c0d0090498500081c0007642480100381d40340f401e1002e51b0351190641c1c840401d441c4131fa4000c3c0150b034004440d62900220345c50555800a52091080c4041c1d29405034a5181c0105d9400c0700c41400d107074000c408040c104c000001c0900161001004040f1141401004101d0204450f0301440382c400300702c044005881da41c04158002e1084200080f1110464000c010b6034006070072040104000e034030070740140b014442c0803451080d9288000d41c0f40506207031400880c140098680c500a40403c4e450b0041b076070103210524041c0c100400c04215645040000402920526081c01c9680901032808104d0882e00d0041c541603a101c180c0c000001455517003445075210704007030020108803001c1c0d200611000c1c20301410b907607003039801c001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 689944307 1250 689943057 689943091
    0x20f090f03030a0530011d150109180914011e0b0d200909010f0b0114070b100b0406020607110307030807080a0e1e0c1504030b1e 57
    0x900881180035500103100340e0050102d108080c2d07001048a6070b00030345c1e038400748071505d464560300000040c003001210b21015020010030702e41064009004034889801001000703881e00070003082e035604480355081c00a0304000c001d109805010400b45090078110000181003019030722030200302e250940300300c60355945800c3e944030541250f40361101030311a0400204071188480d00020312040800e0b60060501d107450b040303442064110500b00c0030364000a0080500c2c0d2910390070b820300a00c505036088003814074101d61807451b540301301ca4010312400140d40c6145425001c0c2c44200350407000801d0030b58485200d0901040303010044000d0402010306800a00b41828190740140801c590701840213542d61007031244401081d4480a00341c2c0011041c00c254010f9201d4041450107803181c4900b10745c00c3d2080b81c05920703818107801100214207030750909848580101500300126062400440400c0d28800c6c0800c1c00418a040c180707980080e0708184084050940411a06a0620840e1860b4064a035424 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 689945557 1250 689944307 689944309
    0x905060c0a0203040b19180609050d0822051e0603041e1b08121603081801060e15030106080303160302090d0305070311031908040f0204050f040c060e0f01030e10020f09 74
    0x44642000d0707c14404045c00c05d030800500405041c410300c607807403240820006030400d000005048414011200c8000b900510700011110108401d900c00c0e03d0045002e1035090113180c06207206e1030b1200c078005000500d1500c440c1c82b42c142d60170010200540440e4407041c8400000c500202c000501d4120051f041c5000c3e00e0481036a0601240308201241090200003042103482c2005010319246d9060410f116242c40381c1e0018040c9400504080b982c5601c1c00c0e2001c11180c0c039007699544036821800302c000d1030351952030525081e10803171700c10544036a000b4000301d165041c1a03410502010340500d001400c200300000040c4400c2003e0400b034011840014241d402d060744000d42580c0301d80043d00035458098610407101100304031003100020858040c0100c0d0401640c40340312000c1940091044c00282802c07100301e084244151001c60340100043d03030000302c0b50b0040c054442d944030000e110001840d0a032005401411091078600340714081d00d0400c100d4064a4405000b03d40c080d41c98264139044040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 689946807 1250 689945557 689945567
    0x31506050603100b0307140d0f0b030c01020c1e06070c050325090906150611060a0603050c0906120d0503090c0a080c0121090b16030905060c0a0203040b19 68
    0x2800041c001c0004008000500c10300b0714030b035070403101c20702d400550b00c0e525074004550f80c1c3e143c40300c2140758001c002902000580c95030016001aa0a40c0003044a11410b60805649051078000c45016800100c41d0101c240752078002d2514440301101c003640c0c401500300010b009a482900101e0380100030a20600103428200a200310701d031801800c1441e140000d00a402c8003511511540c0101c039114040700040041640010000446c000d00d9503c40540f106c9002d8003a203820304c0807200d10311032440085c58140c030501494007101d8101d0054a071070f01d501d209100881500400d419006640180003460307548080040ca441e28100703503609626400d02c1040d0f203040c00c045a08a500c20600018280201000404c40c0361811000f401c0c4054450340048441c950351407a03249200c443c61505106800741310390701c2001072080f9800c0300056a1031840002c2502103030380125010700640c1c4000000380c0c80c0e8546200501941d602401100d0a25655a05080b95544140003448104040002c1d9181c1240c000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 689948057 1250 689946807 689946809
    0x10050f12040311211b07030605060405060904080304020607061b030c08090732100206011805040f121e09080106061112131d24010509010507020a0807031506 69
    0x41c0c005002c00e541418004a406100d00d2550803903480006090840c0305c000002d000549003115068442e001d0b41d03800c0100040004030360f03071030080e810000015241d1910100407032046901884031800c41d103940d02803240f00e82100c601100d900c3e50311009078048400b03529a43c07810044a0b9400300f40c0c2811305400520f09440542491201e41c07040300f0a0103403c0320900c0b001085000a24981c2c1100314015a49007002c010f1040c0d150458600d850f039810a0360701141c900d0503100e48450b003d020440d000b0b410400c65100720b0303001c2d01c400c80a05155000400350200201040c0f103d1034003006844421800303580c2d080c1079022a81c0885c43c0154100f00807802070048900034000d07402c2c41c0140701900c0c110382da20380c02040c041c0c459020001604075a2604030850402c098902401c0390892041102607040c00c080e82a00e041d0308140520284514800d80b0408580880406943c1c4e981044404001500e8030380090004982c0301089401c049030120307040200100840c007c00c2e80022402080348904c080302c242e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 689949307 1250 689948057 689948087
    0x17030904050c0d0e160905060a15020d1803030504090c0c1b050301050c0702010219060207202d01110f01020d270203120f120a0b0411070c0510050f120403 68
    0x8205200750600041700e0741075040380c00c9100040f482d070751041c000440800c20354001e0300746d900443d01980f0030300d41e00003601d81c40e0b400340e912a481109450801c414041116100040001d5010001441400d40361b07003240e4280c2e6194249141d0241c96642d03400b0380010800c12007203611354080001c2005290901030030b42c1007070214503618034242898000039280c0310007800b14414041400187d604002c901c0d81281c4c3d02039040f00420300c0c602c0039034504003810041c40590354824040700a492486603400c2c01c4030040402209290410100090010350700200740070f1140c1e0450040344404501d1200a00050011840341c140014484c0c102d04400e040d0000540164104100d1030140480141c44c0010b05035503003101084696143c0c0500480c0d80c52900c900d1159085000f150028002070041130b4010342d9156100300d5041c4440960900104180e01403030501030916002070500304031a00300340d80081c000c00450320704680b6081c40003110700310740d9200500024100906070204801e042c0d00c10f18800c0c070303041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 689950557 1250 689949307 689949313
    0x10030305091c060c0207060e0f040e0f03030f100915090b0102030d14040c0f0608010b0706022a0609010c0804060209040605100503190212161e0206041b0305030417030904050c0d0e 79
    0x605a00803d41e9071407103882707903400b4590795007041034421010407848000014007800c4981c0c070318144122024501e400c0c2c424850074540d6140103c0e4031643d90151504d1600c682c83d8104031149460b15800c044e0042911050541c0000c01c001e10341030b130041c0200c3d43e407102903980c45107003410145464030074006981d00040b03000c41245c40031b20a180c5e00104403411940c080300d046846000608003c0001d120715a010001e40303000d440b42102c94031300700040c00c00c4900c20310165800342d45d034020724500b40c49501803107400240d55040040c00150311a800b6049030320b009400096210b0301c0b6808517500c601c18580c000c0c0803c0300881040040d86040001d80070300311a82e00705606000300d50400b207c00b440040c20141c17100425424150506100796002c2c404e20505081354448100782080281d01c1d1001641d003580c0c0708510101d002001d406060624044075030080c015481c05251888480050505500248440c0400c111000c155030361800b60714006c2800030300440da03401038030400508441518000480c650 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 689951807 1250 689950557 689950577
    0x9060d02031006090e070f05090909100c0206070c02120a080309030418090f02010e15030c1c0605010c0201120b03010504031e030b061b0106030f052410030305091c060c020706 77
    0x1560904400c0d03041882c034201f29250701c1e03840100b41c9035402088015a040b40b00382c400c00c1030701a000991200c48424007101080040040340b422600c8001c00c944e950045104141c4c0c140041c20000241100345c0400b07401d946030b581e201d40c2d49804543c000d07100c1c00b500741c7c4081428420491513078418440006a40350030841044aa0b59000000750f8904c001f0703052154032104415651542080c04840462403d01c655503483c0403401c0c000103030008400b1f00040354034810000ea4505845c0304140582e98161a0441950f549034011030350002124410220b560302c641d03152082e40c800b4019680a64420b07194000055019440c0400e03400d130301600c0030101420039000384a140c13640412079002034400c0313205082800d040180c2501400c42542300510401d640e48400702405004035200015000d40003074000841d80b00500d04107400415610942c400c0501c203005c00009000e00010b00e1300c04400f600d0460046a642c6448400d90142d11080e60960f071503440c48145190305103d40d01c00f8024908000301a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 689953057 1250 689951807 689951819
    0x506070f0c0f03201f0f09020a2304060806010902030907080609240f0a0f020c2407090e1302120a0c0911040b071401140408071101052d09060d0203100609 68
    0x140e8070895085c0000c5a482422055000341900100a0503401034020600c1a55840040144148005040041110381140752900e480e05028a0084801c450010902ca902b071a40c80300007517102400003d423a11a0880000304e460702844914170495111010300040048403a80b15a140b01e2a000b111110110b8420440d4000c0c040d901c0641001400c5c000040712582d003030307c600080c422140d000c10769200c3da40e1241019000400c0c24010010120890005034580c18015210681c44e4007036203100d5081000042c0d0420000f088910900b40000d007644500e5075410326070740c10b1461184045e506010b010b0303030a0243d921180906079640c643c44d0581480c1c03c1c6000c040204902030b500e4024450100500e10800810003500714845940d220b840100c42810a4600b65816a00450b000c031842c0921381e40081c11580984150350f650300c0c40d44582240742c003614104071aa4155144007507030403c4c05004104082e29088040c000c0001d88003c0140e507030518424801c6c8061840d8440001c01101102c1031141c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 689954307 1250 689953057 689953093
    0xf0506070b150d200a081e07170c120303040b0127060306140603060601171b040b04090c02071802030414100204030311060105210c060a09051003090506070f0c0f0320 73
    0x820840f07c0c110388094400c581c0c002d030404916600c60344072100007155010310442e000c185182d82440441c0c0400d100d18031400402d880e4082110b010301a46a83c1d0b004000720300c0303010000341c2c16092000d02260078400e6025880d0807640c2c2a0001e440643c0da580f080701031035034a002079a070003c0081707000780818541900020844030020411000c4440a40301084d5034801850849250860222005844940b503203003500047d08a84581c0004a0034100f445030101e002140c540250380120410101d08010345d50400065880035008840740701d07107111002d040300014890030031081008000035a030f851540c10001e004140d880c480c14015007061004200d01d83d81c42d0f40305440e0303441e40c081c480d03a051681c280550030250020f0502d6000000000c0c0100025807200d40301c401e40b08200d6200c01c07040c40e400c0c0200c0032950500002000c1e9480744010422a03070180c1c4413070200000e10303c1c10b82070321500742d40c030020450050340c02200494510502561b80b9a05040e603040b0006000c40180043c030000504130740 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 689955557 1250 689954307 689954323
    0x902040b09040b16051b030c070b0c07260111030115030216060b01110a05061602010b0d0312021b0304060f02030304050a060510030f14070f0506070b150d200a08 71
    0x1500d240d250940114050043c2d0584503a06c009001804c18000161095603d0340e0100c241c0960b240900000440c0c22039000c400d4800f6868010000e1130540d003001d120f0100c0c01052101003d003a10715000141c00700509024120b0b2800c0030712100d030340325454030010f0702185130f0034817085041c180144040264290211088081c0d2500306c1d0012030414040b00058079156035922600101c0e02030401842c05010002411078060118080d075801400c09160f0100d00322081840c0d0070ba0320034268110500840d00c5500c0b03d441006a102c03005103040c240b0780c1c1007820155a4825160305404c085020401143c2002d03402410b0a500d0014602d5440c0030703900c6c103458050b1158001e11065940e80031a03960084a040e6402560b40414480f820f9030381420f00141c410003032180d1003424800d1400124011041c140010201c07032016102500f002d00c10353720460840070082422040c64814186000c0503a1081900059a4040c03000700c10040450240642c000c2440d41741d190081e601c04508002c02040001e0f070803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 689956807 1250 689955557 689955571
    0x308060f0a05090a02091e06030601230406020f060108010212041403120901151410140705010c05070b01050d170c1c18170303010e070e130902040b09040b 68
    0xc11503650040040d2000c1403980109070080414400c114038100b007a030041503112800c965541c00f111105156400701002c2030b5009030454000d0000c142103500034416424280c40110460300303140741110092403590401e03070003c001680510010f503e40401407110602400d2054020761500120103071400400002410040101e01e41c298003000041090098503086a040c098140907030034040b010a0180111543c1c11140c500c00c2100041c103841212040001c015014014a44421001c181075a040188981c00c996404c0d0401201c03001817002e214484206405031603060711034035142003c000c1030b50160800b9000c0c1d003403c0550408107404114962161121000e038a503182c03241d4281604081d80107030000343e50000c80a402e00886e400000d0f0540f0403400b01602508ca13907903181e1078403c05000840891242e001000140324212103810743c00d5219801c3e003050080420a00040780c812041c46140e000d4031540da000c40e4045284c40d00905060381000c132a208010b007480d440342001c1c044050000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 689958057 1250 689956807 689956819
    0x1511040b0f07120e040b04050105130209011107030303090c08030901120b0613030c081011090f0312030c03060913050601050915090c0901181a090111100606020c030703030806 77
    0x10300c0c00d642a1000c4905940d4804603003d81c495903030101902140340403142500c00c0d81000c0340780c080380c00d161191178100c0b0750040c440076a125418044100a511840c481410814000c80000d0100002c2100340e000310f1180e980025410420704101440d40c91a030800c0181ea0010400010a60b0703002003490b40000101c100041d8400400c1c1c0091018851911140c40b6414807810000c10701001c0803e00c81240c40e000300340c80c0081400010030080301c03400080034030b2502c81070100e40300b1402d084000c034010050103030864100c0070540c4810260703a00308603000341e00c10b0800410031040d810011801c541110340008081c100c00016550191640d0050286030f006055080c0050040841c01000c0540120090020236103030600e0680468986c2c440d10b169030104030021014680207038414503c1341200c11242c29031714407a490201c0c00045034441a82107040001058145031141d80900c142d06220064a5000687c203144c0000642400c0c4030300c1d070381440ba0f00700a20030004070350001030540d13002c40121070b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 689959307 1250 689958057 689958067
    0x15030f13050d0810080a0521043005030d05150a0e0a0f0f06030311120720030c04180c06110d110109120203070c090c0f0f020f191511040b 61
    0x701c41400501e42c40b88006100d911703111410f000700440d18230b02421010040301c0390704244100c000014450b602c620120b03280c400c880701e81c00c41c21051007503106a00c3e4061518031f55060340c907010301d941c0050340c004018030358840c01e114030000c107a400216003070003c0d01c0400407140b6240d1500c880c404010001d1030f443d1303203c40407500d40c40c07503992000d0a0541742000030482c07079440e820020321902e0310131442d82a07445080c0701d0140c500c1d015025282425802416949400300f69a180360318803010180f40354242c411104089455a15800707034050324860900c00d0280b407641420803141b42d610981c0008203012a5132110300117414081003c450440c00b0703040c00c0d010090002d61907030050031000700c0501214040481d0501c00f550100042041c9401800c1e84402a03440c1c581e020100d07150150550302203045480d44816042c0640306080b4401510700555241d01a0344039542c0c20041d518118802021110303030144200011100320702252040010700304291452583c60311058401c500401403194008aa = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 689960557 1250 689959307 689959321
    0x14040c090305030a030e061f1e1a120601032c030904090b060a06050a0c06184b110d06060803041521050c040515030f13050d08 56
    0x640380003541d100040325518441464000c0003480c580102042c60301482d4041070050301070380c1e01700d60f1103a400f80c000c040c51490081c40440c40107a45988400300c02140d01c00081c61000750a9804c018071102018940c0d91105001007000e5201c01070106041c5440c0c10b1004a4205ca102081025113210000c1401a5850302001ca4514000c220030542e00a08042200e003c210100b004a402000180d0300990001d8030f440060f41c1500941e0f0f044000a1904041ca01c04601da40c3c028241821010082c3d21884d65152103111410740304050541d096070b000515190503540c400b045039004001590903030201c41d6081d00010002508e418087c0101c48441200350003580c83c9803a0b4030030700b40d1050b0b00700f2103595600d03103aa0b12074105d880f03000c12001e002105d01d1a90b500030b208407400a0000d42400000c0d4800c01c210100419000e40649600c400c10301000ca05625141405000d8042c1440910303244e1404690100c00102d0041141c40c84042680071540040c03c0014400131400484c00c1c905c0c6180e903a80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 689961807 1250 689960557 689960567
    0x917160b0310091a0904080a0801050a0e22060c0906090906051c050f0607020715050a05340c030b09030a090b07050102130b0904050c1e0f070507032a14040c 69
    0x1a108503408401741050004000116000701140b814a89808581340c0e40e41e02084a001c600f842825106000c060000d0800d20641128070103000d900704001c41c003000700c0e440780800c40703100c40c1c081b1000c01c0c0040d0b0140700442d04207210300014040c005040c4451400c140102c2e12046550703695001c540d1512096408110080c46a02da034182500116080c1c0d25208500950b0746800344220701c00b81c200112550b080d28481d06c1114491400340c0c41c0d89240005e070105407113003140c401200c4500f45940c0c041314280e00c602c04440900d1140100060f82450b400c600b80a1490b00703000e082c0020b15801040032000541d00100440100d42e58007040c5912000c090038541d0182c42000d18410a0791030f101c40c0400c1d2801e081000e03000c80741e81601c00304201c5e44c075a01e10445a20400c9505078900301c4203504161585aa00300804800032401c00707517410818240d0321589825600d810846424202040c141d10142100212003106140070704124941458180c18906900c00440080c0c0203a407510300d9554054022 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 689963057 1250 689961807 689961851
    0x307030305090705220c080c09190506030106050a081305070302090703020c0106090204150f02190302070317070201140708070602090301020c0f0c0a090509070b0a0917160b031009 79
    0x90b1401441c0c1c3c94941403541072002c00c3c000b0110003807814181190092103604002c0c0303c0c0231008203480c9800c23203075402c100c040c0401c20402c8810b02040000480d584c0c460501560003070155840b0540c40b540381004c082d0a0050040024803c802111040380224100149034130403680c059078051403079200d901088001c1e1003288a91150b070340c240b02e030000e1407580c590f0042c000c4440302e880c00c0c44041c0b20308008030790981d4002c94190060b40700010f41d60722001031a91007240c2e035109004a9103013599030382e10340d84204070407144a42c01540100e400e90540d43c00c5150540c54148081301189401070039501c0303640501030440b000d05240e60100c5d2111031030700c00b5811280d40c00ca0440c21a0000c041130101c0744d6072138801e03055482c014000314000003070310140e50103150b0040c0d0741c0c80083e007552401c0546015154002001300010019411400946619840c0e003180c2d4005007200900181c102c40065005103880c0c543c46030017800020400c011060480c41c00e0316007a81c801003004200e002e0b03944da066424900c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 689964307 1250 689963057 689963059
    0x1e4f050a140307080415030f05130b06010509120a03090e070206070305131a06040e03070b150402070b070215071e112104080601120308150a150c11120307030305090705 74
    0x103804078800c25005005030811051f50360504c01060100604001c0e520b096a010340c40102e80d94111001641d5410980c0e444101807510500300f105880c00201d5001040f8042c6d09250042040703402410b80c000b4249019051140211400e41007c2000a41d104c2c0000d01d000700709070f5031304049902034400307a50304844250040c1083d407404182c2c02c0300c01410242a203180b40300da450000d90030304240e40481650a1180c0100b0480da851340d540261100c909504480076a01c15400c2101318009681e00c00300030b00a0308564000c0003900c0c1112101c01d00400045d08000c240400704d007140d035001103102010301d811006807505003051000d902004d45006040b021030200710f0900060080b5200142c00074104507401001283d403680da803005960320018207050080c0000d0345800000d100170b05c0e040c4130904c0c06039004e80b5140710a95540072074996000107030011170009034402d41c580c050140e42d0500f401c501c00c0865000d00e8506d0340c1030f5021303030320300c034039200102410341391800206c0b8030105121803001040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 689965557 1250 689964307 689964323
    0xb0d020a09200a0f0e12030a141209100c0c021c0c0905070c0203010f05010b042102090112030f020f06010909141209030609061e4f050a140307 63
    0xf0a440034107180284080c40d0002210f2a0321042d881c0740c40800c0c9085001400c024500e40b072144001101c501d0b00c100b1100c040014100301006200d00042210740c4101094400360000a85210b03100d019588512465010132605401500250744c0b0030426078480d16403404500900c040d6807a00104200c429445003039a00e241c013081094041e041515001140c1c802c5008020403c003440d224401c0b01c1e000e000b154408041400f05101507961402c040c0520491a810450103001c00d600150f28900c09030000f803030701c1c8507040065007015004030b52402600c91600152009a003c0791840356601014841c40c0021a2104422004d0000b2000540c40000f4140e05a404135440403401400560200e500d26000744100c7c0001070740400c011580c1d9009601103000014a40c0140030003103504100030b0b010500b403910b0102542c9440c0c801800070382d450510704820b10000032498024802c0c00d0260341039543e91921084442c0000303040462221840c56010080410805c0c40070308807440c500500b840101040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 689966807 1250 689965557 689965567
    0x7030504151d0d182301050f0f0c1609020a0e01180e0c12100f1a040b03040c0f09020408030d0e01060f0b030f0c092d0a0b07060b0d020a0920 62
    0x1d68440a138400450703219452806540e0341e401d554513145811281d411380c15252800350b9119610841c000d10b081c1e0b4041903014240381c00c1c1c1e513459040343c1c41460001c1481c1d1001445030380b000b040c40c240200510344640210b0070003100308006080c00e25000c49803030400000014541016040645500180100e03002ca0702251415054100341a4850400d4001006400300042d41401d90b01d0602003e40e14040500306e02e032494503842c1c0480b046540d02038421841c081c440031942940701405548100d01908046000310300c3c014040d400518550000d00c0740d10700402052200c20b000008071440300d10580310000e140741880e074031207004011030b400840400b440003038001007910b0024003550040c140f0040720303c46512803810b01e40d100e02c1290030359508001c0108640240c002010840020074851a1151102c90a90000a540307509140c100425142011070781074280100e80c855040300d540b00790f40941810809070001100600a403058008090f03c401c0400300024060101c906650000f103881510343c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 689968057 1250 689966807 689966833
    0x3070209190e0a11030a0201140706021b1e0105160e030102040312081006020601120605040c1e17030310031506030812040212120a0e0d1a04020907030504151d 70
    0xc00f80391005032802c0d500045000c4007450086034085085034141c541710450b20b481c02d50a0110f41002000362603c0e0b40c2800a20040e402c2105000c0e00034031860f001e0248405404500418103900c9426110140c0c5818200a140307241c01c1c5160b0340c00d1031203042c10b580e510070f4000003a01911844e00000c210007200c0305a04c03203583e0440c41e80c0d40502c1442c4034040507030780c880030101d80d542802d11070340051030808403910f801704d01d00e0342c00150081d028107110503000b516a00d0b20700c100590b8605940304810344e603030300b0131581481d28504403154550360003039480e506200280c058514414003002e40f014500c4080300d00f00014640c4040c0c015640044415221281c800205440c08012038007139001e0759004074980710701340c00030a010411042050029041075007a80c811240f00201b421000d401c19112800003010403c91000440c2040161510882178902441881102400070305581c0c1414141000d01001848480e09a90301000d201c00008820313141881010550501c0c201c2d0762900d000c0c0101405803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 689969307 1250 689968057 689968063
    0x180308030a0207020a0b070620031312110d050c0f03030108060a0c02070306114501020f0703060f0b06130909020117240105070201080103021e03060709050405071103070209190e 78
    0x1045044040303e042c50b2240100320309c000d01c0104c2c1d41601c6448072440140000d8200c2d80200008030241c508801000d80e00b17070380c1038a0b0880d110311800c0809c0010450119a080400110401001c024051801c55245c074101698a407005000b4045194441c458000c1c254820401d62009503007012040c03110988802d0580c2103540f1401c0a09902c3c600240c00c080580400603400020041d00b512100c0345540c041e00d10000041254074050443c000c3c40080d1402c61130802210f0081d500400000809180d20792003102180d4440d0000f42c080c5005000c041c081d05090000401111070107000462500803d2004880f07401103442c084100c2a06c42080c8a0002140c140706200041c4800740243c0d601828401907035140540301e802130001d034207100180b0050600340724400070b0010000c02c62640c80f00c81ca00203820a08125191000204203410403c007601d0b09000f915000405030519000030b0304010700d100d0302c030310658402a026109010102d004510200c0d0110988019080b00b008240c070703d0140d45407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 689970557 1250 689969307 689969321
    0x6040b18060708100905060f040e070909050f060a0e070e100f03030509100801120f0f060c0f020d08061e01111e151e04050c0402040f06180308030a0207020a0b0706 72
    0x4844c8490408a541981441140d000d080010002d140c1d210190b41004050400303203401c1444c074000d80400107020350b003901496a019100c4d10143c0940e0700c002d1303002c0e440c10b80020118002a400d24005e28545e0202203028070659a070201c5605196550030000c41d041c4100d58050518200c6090002040c180d000020705040c1c0d03030440e0064503480340c0c5502181c2d040760a010750034141e4202907041000400c511541000b01d48603a4200800d0712440c2ca601c41255450b040c00004954143e04c80034901e503040c04501d40420b460300301000d1a00b4078802041c40b0744148030480c02c90548085040104e0f82c040c00516512101200840350804d5401d4151240440700c1707000483c0921807101c0b400300700350704440c2c1c8a100342d15085103044454424041c00e5003d0001501c156400e003c0d000c1205420b84440c0002c1014003850500400f11724a0728034010000e0700c075155110280c9144110500014180c041100c0d040131240c100581c85241900024800311442d82c440300c24100001116010854031f80c01c094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 689971807 1250 689970557 689970571
    0x80705150a0c080c0f0a0e0312030f130b06010e04091b1403010221040c120506060a06030903090509090f0714120a0302070501050d090605040b011509060206040b18060708 75
    0x486060648402902c003c0015600862071541c140b00e242c4080000f14041c0c000e15800349460920405540d0200b81048011070a503c5107100c000200140810b1a4220342e400c529500e130b0b8800414217a40b0f46010200380078000070304202151000c20420394a54001592043d0005160240c00c5c14a842c1400c01d40000e225803c035402c9000346e140d1461030103100f0380711441c2c4401090f060100d1030040000f000e801c000c3c070440e040300002c8000b142403a40e0b040d00c1148684104000e10103400e002007000300c5407070b0030fa00c040308050038081100002030340039909804954007514400026110011240d0404880140018035403280480c0094074122401142c40361981c240c03283c0307481000600055449640a16003c1d0160348105010462940702c1c60092900f0800008000b03481e0469540d0101034820170b0f40c081d40c280b1400390061294038030845a00c045000c180c10400c18291910401030744441e40184040c04403080040002e5903e207000070340b1039040f44810141e4995113800000074101c810151244 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 689973057 1250 689971807 689971811
    0x6030f090706021f050703020c030c07051903020f04090c05100c120509010503160903060e0c0108010f050f0f0f06160b0109141519090c030b06030609060d080705150a 73
    0x107100d83c0007007490300580348122450f40540c42c0c1600200b018000140c080c2d410560300701300301d141e03000701440030b80102038100028144003440d0600700020407515140702d03641c800c480141040165900c046409026205960120301c469144c240400100520b600136500000e0003036081d14881c0d44640c41c80161481129415441e5401a80449050143c0411039002c190100040b524401100700750520400c183c0c9004803c0c41e460f41d4410050318140000920a42d2085218101c29a00720100c140500054008440550314000001e400384216000f036038014046400c1e503a14584480c0c0a403100e040d40a04142e030385601a01941c0d044420108040d1083c0341100004200c443c800d0083d46154040030744200b1250300d603036000c0a035680d207680c01c280e8414001d880c030301d0003001e014000b00b0003030000000010308500c0981c00a415640c00007076181c41110204104a00c503607500300c40d541c100d0000e0310520b211030810f181030340d0f4520451001074011310900040088070520300103414800c103811141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 689974307 1250 689973057 689973059
    0x40515130c0507032a030c1a0601092102060c060615120a0b030f010501090608070b0c030a052505030a0e0612010510140d0b030c12030a05030408040506030f0907 71
    0xc04115070260241c4800901c0070091400824071508145840c002618074500c0d006801d4000c3e07094a244000c0c048004c100340208150a0210f03c2d8102e604110500e148407d9602d4a00d0008060084a00038114000403503100c0c2400400b2030081000d440b0342c05003019036100201003031990740300c0040341c0071481412166004509010b98a00f940c00750b070903074040494262500c044c51000f801c100c496030b903014460204400a0b00c0c5c3d01340103440c002d207120500010107500b01180ca03428440d441d0001e4411440420011001d15000400c80d86400c4262400e141c4400d80b006402e0154210480c48014858a0340c07550810b100f80800142444801a2a000f0701304401c10280255401600149151210028010049801c044001440d207a48918207002c10b92034034040c4c80d0360b035003102c01a00442640c03445400b0303480c1010032984a13014030449a207540c038030b2122005a0f0b02d200300e4072004100701d800300206007003202d41e07010b850182c40001d01c0760b42c0303c0c50a000d40e020898000ca540f0465442850383c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 689975557 1250 689974307 689974339
    0x901031b0f0f05041b0e060a2106031e0c230604030308010815090a12031b080108060f010b0307050906070f03080a05010b0a020703020418170403050f0303150d0f02040515 75
    0x41c05c4c401e4049030792603019040480400300501904841d003407205201c910f590202012041010810038030440210000b10305007582458040c51400d0805004e090400521002c04075022007003800460ba004000a2002c000345210402d10560602d030854118001090110030550400105810382c1c43c80c01c12244501a100d1403480c10140540da00100da0308909c601401164032071408042210050501003110300c1583d00b0801d10200003080d102c0003904140c01404000c506110035608201d50050701141541030100484030ba20003d0306000901c03800080100315503d404064604450300800b94440301d40072802c025120f03030400c680c1141d41a18000000c03e0160400e41503d40302c1d0788682c001c2a0031810740e07090000811581310701459a4500b0f04000c00003e0003003449000031020040800e072250316514003185448045940c480342d81d00240204030110348a0302c078098071f01e9411103407907403c522030b402d04031074417902401d003c0e402c681406e0820030307052003c43e001500550241d032080c22810b4080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 689976807 1250 689975557 689975591
    0x50303090c0d110409050a0c3308070f02101b1b0302060106030b0a091b080a0203010302100c030512090c0a05152a0604030201290901031b0f0f0504 65
    0x2a03801450032202aa400300355013803d61081c80420301c288201c0d0901d540e2522092406043e60348111090714051a0038018080c200d030403c4010010520700b1b000708101c140000d060310030010541c608124106044020403442000420780844030500100900380f030f40a40b01300b2005461490402090300e00e1030003000711140e44815000e1030341541c040d00d59079080140c210068603403d400164002032541011800c8221481004900844003d0303e039034134000390070081d201d20b0004040d1350301188184010009a10f5241c2001c0c168201490030350280995403600780c841d809818030840d84e0b60440010844159030004403080748140071940b1001d039a40c0d27002081407a900c0a0f50120f2400e00900008160a9000110220710000c40b1400b5102c0e9403a0000782d881c0c40c4007118240e0041c1e4540c01101c0e6000018503080c190b5403400f42075049503c10325000b04102c0a01844020b1984c8a40724a010000038004525030161420f00140100b4640d60700d907401d00075090340143c41c401c602d01060007403440890 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 689978057 1250 689976807 689976829
    0x31806020c2803030e0d0903080904060f090219051309110f13030308011e09110403021305010e10060e120309030a030e12030c0d18030206040308120109020306060d1d0604050303090c 80
    0x80d907030b59047d0a055a0303c42d551030b00182441c94005e031f10380038003145119000403030382c0c00b5164039400140c55a220041506903405274034180403c3c0503003003000c003d101d40c8200703c400c1915a43d07280403a0581120f03440c4813091281c4c1c20680700581c0d0210b40988600c902d070f00114100d074020355810300781ea603e4611060458254078107081401d000610100014246500b1200004110314402400e00740d40e40c020442a80741360001c52092561742d801405112411000c032034014450f0030035100c246050010280c900c100c0d440c0820711072040c4c0240b88940034810400c558801001501b651400341051501510401000c50154414a03003400d04085002c0700100f40c41d0b000b2201e100030503c402072154240c550040d01c45c45203241c40040240400503855650040c0019440352001542e40d4120030401d50801030180c214020042c0104140300060340e8140680b4000c1c804d8040008038903400011800100180307210409490191000b000180f1a0110186200b0622103081d1030b121038200e82040b44031144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 689979307 1250 689978057 689978083
    0x151605031b01090c080115170a0b0106170a150513060504020417151006080406020c01140901380f090109091a01060804030f11101506031806020c2803030e 68
    0x60030f2401c0040384000042324844022403000e032986841c440e15001c8070150b00f40c01c0a004520042521076505540c111201c0e03000080790410002c00c5403e1000c1c500540c80b03407050170b2144591035140000c040050340520002e0034002c108565603036a41e01c40b40280600101030342d815024400040810841040341c2c607204066030401013a445080c001c0a58003a80b000d0825141541e0a100f801c030781c00801d11845500303001182c2c4c210140e1402c18140340c250742043c2d40c82c00280d81903d01404059881c401c0e00c2c83c1c0c81c0203120100c0070210107000404d40303109000c9840340d40002e640000090074074240e4442001c0c0c030f000d511304a0600c1741c01d4220944d01107083c03040c2400038220000103400309100c0d030040c0c0c15601c3e40e841c1c4031107201180303c1d841c0e00d041d10b800841480550380d5001412001000d0907020b000b4105402c040c044001a100c3c0000e2400b001c800140c4056000900d511001c542030155001680b404a4915400e0103113071455400440001c0d0700700e01191810381ca108008000181500444207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 689980557 1250 689979307 689979341
    0x1203093d0b060412031205010807050f061c050a020c06010311010905030706021b01121506030e0d02030301090e0a020a060504080c0a03080703120b030f1b151605031b01090c0801 78
    0x1320700341e0001c20400c0080400d40422105444101000304907015880c02440000020000d481c148403c000b50034124184040c403407076040041d8045150000a02c551074510040c00080355500c80d42420b019220381450010540580d0340040b08002c8000d81001c1d0040d003ea81d040305403a2070f0000d040d40c6d0000c078090344001d40d108071224001d42034800d0080301202c0701850200c489140c480c54610a507041d480140c0030741d000307480c800e00c1042d85c10700c074400d0309100b48001840c1044a03000041e48034032042c000d0f040265110502101082010001000da10750b0103001c3c0d0104035600e1000914581260140700494060000c564150380340102007101a60741105025290168555040d11100181d1182e041119102e003180300e15a03030b051260070400c010080242511511039000514000d5041710796502c520742850414800300f203102c00751048901c500440c000c0c0079541d030071306a02d1401403914162a4000301c0405400201c1c0640110022074400c03243d103441c098039030319011309076280030002c0402e940d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 689981807 1250 689980557 689980559
    0x204140402120f061c060203040308070503012603210a0f020403020112021c0e1e0d0f0807030f0204030609021c0312020a110105040506090f0f1203093d0b0604 70
    0x61030002140350050300003881001c4048528014120085c80000103441030783e40407082106240d00241e410350701c07040c0d62a0180c51581490f0340041109502c0ba0032112032000070300704000700c0c00208121000c24540040c0e040c0d289505e00c022104000302102c0703e00d800c1e400c200071101609254000d071010303294141c498000a2050060f000025004800c1e200000c1c0ca6406100c0e031001110b10a0004941e518030181c014100c2c070b508076100780320205580004c1580b203550284070003580a000e544482d40b032464040c0260f1900a0204c015000c81c9100880040c0300140010801015510031807007a07100761140c2c2801c2d0380c1a550a100314200c2e50000d4046a00585c0d5085811110340c02410000c00c0ba04050302c0e001039802800742102d4003214121180d83c00042440100c180401104503141884401000c0b040b0031006826201d01d103035060741008900200101e05505002d00001c6008110f40d0840f400f25080c44006085611074240c58070048072808402c13a0f20300300240540540c3c008085d00040c80d003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 689983057 1250 689981807 689981821
    0xa0503090f0f040c121d0a03030921020604060507080708010308090a09110304381b03040f35090d0c0b030a05010b072609060409020414040212 63
    0x7415041c103615501000448450500d540e9a1113401c1000d103080d0340700151a5409404982150424440f50403181ca182816800e800000204000b0b010f80c14600414008140e1621400700280400c40402682c3e00d100120150b640c001038035072140340994403d11903a1203101064828180980b50344002450200060004c9240d11004050301c44e0702400d550b107e603984480044c200e0b06094800e2410a00010910040c410162501485480b8901520701d101c91190352282030201503000407480e940215000403082601d80c0105000490441aa15580e243c2031a20143d0240009000c60b000304100001c6661500300c0741402102c080b1490381100b40720098903007210035400241045a00802d502c0c2840e000416910181c4014040b68108640f40e0522080c40c42c00e65005800c10b110100d400d001d50004140d280da2001004d0b40c001c1185d6402c50b03e00d00c0801d40070310603401e895400010009000a01d680c944e0300900c200d91315600801100c40102c0100400c5e44107808140c990714414101041d44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 689984307 1250 689983057 689983069
    0x12070c050a0f0516080a020f04021201140f0d030c03031a0f04150b0a0f020c09060f0d02280e010503060f22021005071a010e070e0d081303050f0a050309 67
    0x9042c01201200e5859082c1c8501080703080ca55000480f0a4121b50200d9003142000010f2596280040b5001d5007040d242c07d40c451f002c040d0500c03942c10b00040d0b245a140b640c0d110101158078088002c1d01403440f80401c3c2c103000d0507201d90301e80308a0000c2e12f4018801c0d81c81c81680e0300200e100384010808825040c0600810000d0006060089007448240c44005140ba034651300030401c01e0352a4841050040c1050006420401d585c084180074a01103000c0101c0c903969000098041c0348e00311502042c11a041c0041200084a4014001e0038144805000c0300e03030840c030030300d00100c90829410244603030302c8901b031549410060300d096030801c0800c8042010f030381c841403a080440b950001c076070440b40c8103600061240d05102c0301c1e10020480014090050081c0b4400914000e103a2840d40800c652400c0204000600d00034010fa08210b0b28050f001503e0f03594407210780005412a982035140d41445840c8007154005100440d417a10580101e204003240c0443d400c5030b003d070084050b6003440c84c80390034098 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 689985557 1250 689984307 689984333
    0x109020702030c0d050c240f0c0c0a0e0a0e010b030a0303240303030c141c15030f0602090a1205030301050114090d11030c010302090a030f0f0c060512070c050a 70
    0x42c1c94065014542c0d040e445841050307648a0180c40203009240440d8180000d580800341c0440310b18889190700103070b0603103003001c071400d185030319a6069440491001880c06c1c03c43c0715945561101000d1400640e084c01c000c680c034040c207919801008032010704103089080f100030b404202e805810804a12020901070b5100035030f181450300c180b5030a882450441040110560400c0300840d03580c05c0300c5a0b00d268048180003101c03030110201c91138146440e40900324144e1580079249101e840b06142d00144d10210b482c44000c41e44040c150582c0411460000d000e500b103403020741d000704142d5000044861100c001600c6240d0440061499a4200030044840c1003076004401409241000114841d07150b40703200e07010460181c600d074141c0103c454201814041061a100c0c10180140000845543c401d1141811281e102c084404141598542001001840c100240c981c01c0400c20000d01c240d00719000700405007000c5c2c49403074a5502c1a1081c5c1d9001c50300304000e0055401000a0310029210b0000c0704 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 689986807 1250 689985557 689985559
    0xe0d050a05060a0507030b010903110904060f060801061802040605030109091e1b05060c07091509060e09062a18211606080c0a050f03042a06080109020702 68
    0x21500301454407050326008043d00d40321001d5986900300300030954184283c1080107800d1030801039882c9140c0f2180c0e6200e02c000002403180c0c40400201d001c00240354000a103240780d0440500881c0c3e07440408a0080c90303248035044c003044160007004504582c03031007150180c0303446455070ba007181d0900f00441c2c001c26030488219440c41552012042e5003c82c0403a0085c914445d0f224880a681d4011807030000040ea5885540621030500c103948032108080380d45001e0768090080021407a44200e45041000c0c00d560040c910349183c6100032802c1c00310424027601c00e83d010302c11502d03240c4071000c00c0c410841c044104203540c0394483c0040b15601e4011001800c8441010010805001c80080024081154400010490103845841c5c03180ac030303014048072214501c41410300004a03e03110b4050240c0300000c2c85454240d1000a4800200d400788080e1220301400c850440c0d160302d000e02c1c0c850402e1071003440c1d14650461800300507d20710728115158003035400c03569903564240d180031844000303900001e0040b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 689988057 1250 689986807 689986813
    0x507080103030c290105120c22060e010b071a0408040e07030f11190e0f10050708070803010e010819031d060d05060411130b1612030501240e0d05 64
    0x30407501900810a041c4d0408200d003c403825500d40020000c0060681c02e0703032240d030707044030280d503e00d60390700520b444411055000d10111104032141c0c003001000c3d160040d804146c0c40c0400450002048405050ce00d4814084040a904002c140c000e010404813401020759100b000148544080306188540082480c10007081d01071382100380e20151010140e200c039007408003148484204004000c409c4e400a03807820142c400c0344442010911145145102e14002c4400071a480175051144040710f40d10f640090100351112458030b0111980d500078841c81820102d04000410030820200d881c40c0d50714981404d0001c080d01654068030200032020b4845113128120603070b42102d449900c0240411000480002a280b5003032040000312031405e203510942000510590f038420030400040029244003144041d103420b0040d48466045042803030047c001c0061780c1c00b814416805400c024141d8081400c81846184950410b00010104d0b07001e80d800a02d0085c1c10820320300700708850400590140f015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 689989307 1250 689988057 689988083
    0xb04050708060f01121a0a0e01061d010302100e0607050c0901210b0c04080106080f0d180b0d1b11060105030d0f120204030501090f0308090d0e0906040f0c0504080601090507080103030c 81
    0x802003083c4207c030714800c0c0a440d0500c054070301800307200300c070301608501030141344201c00c166103690f81e14414080240101071504201540601400482a515400800c1c459176142c03e46051905c400d050b107240f9000c0c101800c004030307086440320300c0640c42d28199003403008405c207180c6900407940300c0500b556081c0d607002c0101081824081c060b0310060800440207043e81c41d40c3c402d2071032604100001030401c00081481d1854020344018804040b140140013658584403692000380003818460040d140c41400d00007145240340c2c0101240d110382d1465001d07115203a98560905840b4106c5662140001e00c07603200391350031540500f0040c820010516070041c281910380d0b41d01800c42c0c900e0b50b01a51311641c1014120304050780084030562154080c03003c1d0020070191107018103100f0b6014006440348002c5c8000650a8403243d01c5a0047e045446d07050005804049010349640c1c090b000d2080705009090010480c0c07591801160f0045146946201042e882c42d1012220046c0b6844125a0280301d440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 689990557 1250 689989307 689989343
    0x91103030d020414030f0c090703230402030d080c09040c020703050601061707030c050d090303020c0d031d0a0c060c1b270504020a090e07050d0b04050708060f0112 72
    0x20141144a110001c0140d589042143ca41c3d40403e00707180b4240319902240c8007100038103020440c242e030b42c5420f407031070246034580030010340107080c0e0242310b2007081642040d200090810175084a003e580241d0666240b004803d10031185054110b0302901d02d56002c018a070100e0403e83c0c441080d000e01c0d4810f540c805616603075050304008082c0d000c0c0c0c1c00900c06140c00a4401064540c0d08d801405c14203003009440c030070042c06040303409407800ba0702d45959196040c000f8123000380c04407000340c820a000e031082018200c00c0900184500c403004c1c01015003081200424100000f05803040d80c0e082030500041c2c0b8035140e001c45a81c007801400b00c403000c10b5084038901041103065154083c0c800b1800d4200020303903081c14148030b4803407101101e202500300f806020141e1902e44102040d0344405001150806005c020b4038508000d07031780420780240032128008248030191200e140658428425215429521204103175070300c9080d035400c0005803002004000281040416a00b0380d480380502c001030781d103124 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 689991807 1250 689990557 689990563
    0x90509060936030706180c090b060903011508160803030612010b090103030c05161d0403050c0f0307020a0f18050a0f1a150a1b020301090b0c0d050108070b0d091103 72
    0x15030298183c0c008500e110802034203000e038000700c42000703810740800c02e000c0d00d901d0581c030a288160781c5c126658980c10801c03622800200c172070044004c0e00a120708107403d007000d800c2001c1449501e42c03d016014160b14040407851000d0119400e0708019403d50b201c1d0f030100f0a0a21600403d0f14056681d2500007000361900b4904030700950090b01c802411b104039050060900540c907600c03070300107a81c806092010200c100c2041100c43d010304440050f0b5075031450261795034841d00355825803520802242540d9101c0000041007224400d9804000301950395036206c0c080c1da854010500d40354600700110090b10b1aa9003c140d20104a080c041041d40c1926121422110300e0420080300e00b4803c0c0480c2d80340e05040030780b400e03080c04018850b0320f0950302e10303801840803150402072400744003010000c90030341d6800d400c2014060b400612078035080c10030003054034a652146902141e070505210000039402801308035a021a11210320840c07610708090040c80c020007400b1011030b1811803500d01c55105403410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 689993057 1250 689991807 689991901
    0x1021b06090406120503120c1603110a060e01150510080c25120305090d0e060702010207030b07030e0d0504080a02090c12010b09040e070b0406141e0a0905090609 71
    0x12000b4542d11021f540e5800d68540c4001e01e50403a2003010480590390241d0403501190650309850145031030349115140c0d900b003000002014007100d0511411001207603040d440b0030100c07826012002241561a010720110400b10020800424905400141c1b110100c90043c010300a1000103c160b00300b0f203842180d949081460140c81c0701c0d40076001c00355205d03058420303150003000040007443e034141482d10040070f1554072004580518400300d00710f004c590080000c80040c640c4000b410a0300d16082d640203008101d03844c0d00500034404c004403451094091011203054450380d1001d0b080c040410780074841c10100161920510b11010080400142c11125203240078054040e0004c2d40c03000310808201c15905d00803d101041d8010701d00410031900b0600c101e07000c4500c3c50a01182d0702c865004030100074001c04450300c1d04185a41d02200220150310002c01c25041d803511100c410584500c10301c240428115040d6802c029420080356607100e1160151b01300200b410080820201c0a480a1060400c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 689994307 1250 689993057 689993063
    0x6010c0f150606030e0705040e0a1416050603150d03050f0c060a0f0b090609090f0a0309050420032a04060804020906040506280e0f0405060601021b0609040612 70
    0x80c5003400507040000340220001030200d0b1070180000c8010180781c030b459248603c94644070302e40c2c2c1d02d044100d82c0420301c5441c025680001818a10b40900d201241d03d40072440200011100c1110300820640b40c40402e0b84c0c0100b918805000c0e49101503024000318064007007096007449000e01805a684080c00024031b0700c3c04c0214080d003075500307081543c0070640b120784403c045030f0750404084103e680c44003004250702c05401c03900031140c0e45804084a040c64007428211105001c1c1105420a058000b00c066044074025502040804000548950081808030b80e004542404001003040f900096000310158120580340d0740a041c10804060280c0e4802e501080101d0301000c10841940f814070307482d6034001c105480a004d680b901c440051005041c8842c20001810a0704040d2104c0c3c0240030404082c000840411201e0300340301d109840c2c07032002110102c500d03101d0340780000c403d54408102c002d5142c10010103000501d81c5d8408000458000d82c00180d0001d68030040024590310f85807a00c20083c0c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 689995557 1250 689994307 689994323
    0x30312010915090e030a03091703010b250b0117010e0f071d010f05011803020406120b07030b01050306060a110d2c01090e0901180308010f0f1203050306010c0f 70
    0xc000808010744415901c0610b1540c60f1200d54003100c3c2000c0b0803500841440e10b1f0004110140c0d00d424140a405c2071103071090824007200206095000e9402030254000d103a100500c0e03500d070b15000c545808080c42d801060301c0154401040421202d04403c840007100400104680008135103d40c43d1041d02d620080c1250f001c8901040303c1040c8c10070024800310080c5618126605044a900d01a101442164100000d01c40b4404403501c00c0030480016540c01800dd0003001e603030710b030014a0b10068280549110f51190045141c0a00038450170f40c0280068442c03900703695a100410000d078201200c070109112903a0036105c40990300703000c102c0500303603039032541000c00c400c02c03031804103040860041981034924103d40901c00d80e0001b00c0a03081b01c2c1c0030109000c065903081001409058807084d003144e5881e480070b40d8000c26030080c03417250684a0307079400b00800710354500416400d503001c0d00c180c1d021156020720000c00b0904c07803001164000e070181801500c3c40382665a140380a4a806c1e015210b041c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 689996807 1250 689995557 689995571
    0x60e06040c060f1115040206190503150f011d040212010b070b09160302060d0f09060e0c0a21050f10020d050708010803090d0501110f03100614180303120109 69
    0xc0d82240c0214210b40b03c0340f0304040340801c0307130504580e078011081d01a454400d41c1800103045544081c111210003241c0702040820400c0d000b0041c0503074205a072006072808a81d03c039041641840c4081c80c81e201c40c165503801002c82484001c4003c0001101c2c0140c00c141c0030499810300420322100385000704144030010703550340072a080c889034084000d0070100b02908008400c0c00d518242c0011101039a030121096603030394040c2d8201a000340349925a0b10400f50911032103500303015641d805503085807040c00039180e2160381542086800d1100340106070303020b000c01240280002b2049146110948194110b65002202d50469407410b00c41c10131240e000340e00090b420744007800d180100c54000ea01400c00e200c0d00d5040003201500e0b40549c81d034050013113607904628000e1007000d4011500c2c64411143d00799071040400007000d46035200710307039028500000840000e401c40c86849501031619001107c58180802c40a880a511802e9a8619858030041c80360804510b07075882420300030324801d07400013205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 689998057 1250 689996807 689996819
    0x609112208070f261e210d0c0e010c0818181006030b1f020c040509010f050c030c030412020f1207020906031501090b01210b0306150a090504060e06040c 67
    0xc1101404100038021303800d8810300102000a14480c000201001014000152554240740100c1c80380b01405098622081c00d5282e800440200044400c1010921005460200030341e4001c0c0c005441500007004d11094502203007946c80a0114141d50314801c21a1000d42d00020742c0c013044e039030000f10700340054005018170000d110800d50010319040c1030500075148030714001440c0c002640c1c64617280740c0b240304000d110706100b03000760205040020001c00c400d04044103014020800c2481000c0303404e1410021542c81c40740303841039902c103801c4d4448281c9599141c1da16030402e0003040c0c03c00c0055224802c811600034405100b100d00300c0c1304034542262142c44500400000d05005444280650030807014491104140304125064035040ca0380480c1d071254540040315203c1404028017840d128039000b254a01480e034200100c65942203040322110344070048402010544a02e101d40d01050040e01080a031000360491940240144000035050f404481c2139814500121404c0714400e00381e01c804d0001f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 689999307 1250 689998057 689998079
    0x30c0d050607090f081509010f050c090a0e09030403082206030915020702030604020103020a020f100608010e03040b0403020d020a050405090d0306060509060d09022101050702010609112208070f 85
    0x18409941060b0304c0f40d103080156616250b000b00d945c5140c500301070000b290803200f50010118000042d508019501c1c0c0010420342c3c60300020140351103805040800901d24030f40000c020f000d110440b0286240c5480d50381c502d80242d11000a14400d55025144a0300e6506080b400301d00410701e540300828000441e280c800d050b485820314040c401c1e0300c14490040540c50015072180c1c02542800c006958401d080c03010b0740303404156000045076201e440b40102c442011500f102007180c010800910002c0c0310340b1501034807402280180f10145c2d4052204001600d081c03207607184c1140c0080c1070300c6100e03910350340403d065440c11914010349601c003403201c1d000f6039410300c035200c010038151500700d080c030300307070900113015882a00140300a99481e00718272819540d0310411007880d0001d6402c0d203001c132550242180d010b88011038550780554640b03040000c02250f64000c00190196058000d40342026884450f10900c0c9c4100464082040c8020040307a040783c100809000740c11424030b03642d0403620309610848 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 690000557 1250 689999307 689999309
    0xc0105030403050d0914030a0e0f01020f100f020405090103030e0a06050a170c0d1407080c12190e0f0f10020c07210614011e150e030c0d05060709 64
    0x41048820000c000119900c602594020811010007091001e1107090034544c500c002d040d01c1129020014914690303d401000c06040c40300700380c0360604183c00c1c403001661030351400004105213821483c443c421501032907100c801220180c4100500f000e440c0d0012500d10482600201c0204245400015062602d42c043d0401410fa40c0381040c40d00d688007c00616240640c074451941c1c54100008c144e01c50402c2d07060b20400140ba18042182c1d208182c2e48074000341c800d4a865020952030300203c0e0300b61300c10030211040c0450b07146441e6015140c80024074211b03200880d02180d426601c04541c035001a081c85040d0701060000000d00c180c0c00c03541e505604101100050401d0320b481001407803610b110103d15030f011100c00300c58041400601c21503041034901c00102c018001c1d8503000b080200602c8250b24a41620350b000580384140000800015070700d030143c090320410a64500c8000001d038407603440b40700d04002c041d0582e801c9006080104801c20003445040301d81c0d4101a007041441e65110803400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 690001807 1250 690000557 690000559
    0x40f06060f0b0901270611030403060c0e0a090b030d0c051f0c1706030a14030f0c01021206010e030c040b0a0b070b01080118120c0804030519050f0114011509150305090c 74
    0x41a4250034405c2c0440304000344195400d001008103080340c0c07540240180d400440d013044d402d00c611305d20642c00519100e08040c01d98071502c94140080394000d814445e0354402d50010340101940c0d018490242c64070000034000b22518869030003880702c69a9010881403010101c60f1001c80d041d01981e41c05442c00030f500b00c41c0c0c00180e421000b000202d91700000c84078555078000c44103120700e07554810020308620541c0341110b512000000ca4588610055004144030194891841c1d0302d52100c030011240340c1e5001c042c4650560211904080314a0035504c030841c5403400801c1d80d1020b9a49a0041c0c41c40e0b009900d0681301c0380c0c8902c00400c0018030a02178001040c1c02c1c0c150b00c05144200340d5a0310000801d52030050204490440725004018012080340d01175600b18044406420301c0c0c0c02101d9a019040b402200e16002d95445150250f04c140104040c403600c0d100941021380c2807440302c0e032540a000d00800200082c0b80000078844030b002800082c48200ba41d800302e810303d8085259071a00000750282c0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 690003057 1250 690001807 690001847
    0x3010c0c0b090c030c062503020f0c040902241c05041e05030f0901090306060e04060b0604230d120906320903070906060c06150e040f06060f0b0901 65
    0x34003c66a004100742e100c000c01101c1141e1506424060b081d01c001c60341409031081601d50002005064000814a0801a42c4000c0300c0040844205000c2070b2041400700a4100c1d00c0c446048100141115075110b110040b00403441c1030000c061240a0201c2c008656450825a14010301082c80003009086140803500324200300c19056039500c095492181da4040110b0000229920185a00c104140c0008540000050055907261303404540003520a4800302c0d1494980a0480a0703070801109940c204c1d082042a0101400032503030000404d08004d802036070044201e0261000a141d005520044540c035964543c000e42c21301c0c0d000740c2850040e60052035100d9000d00c48594090580c1645d104440b60700500c03d40790000300e40400d1070000d082e046004003a0810b080461000d0b4007865009400d4003503101800001c0c00601c1480d404001801420441070742c030800103000c01c2001e117140f00b2051161100154480d9240c0c8490f41d03640702500100d0750724600082580140da4800200d4007d80d03500144 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 690004307 1250 690003057 690003073
    0x120c0c0301020c0613060608100f050708070906110123060111010b0a061d0a230f0a0621020a0806010809060610081f0906030c150c0b0c0903010c0c0b09 67
    0x200707960303910042c0340c100340d0b80d00661740f0820800c1a0b00402d009110b00c0e004c8600b9000392040c81d4001e4046480341a46861400c0f00040cac91512424003030780185103640312841c2c66400c001045808840c1c041603510b0759901d82d1140d8040294607805621082200600b03480c850034090001450040074000318003060b03052440e00300040d503d03440c00034115860f070306111854403504407007190301d03009041c2015070140c44850000381c07400041d00d24405081c5c0500c80341d12075030000380c2041550549000181e801c0740800105000b024001c0307100c00031000c0741c2507901c0301e8200d03480c0303008041c0d03400000c0c0c0301c000500c4c0d8010700203036581040081d81c0102410001d40424070b400380200e200c03104600c00c0314042000d41c0c8081020340c0c0c2d0401700688401849814035502e5525201004003801107840212842170641c8070003d5801039004051854603800c2e0b0741c50000d000343e40c0ba00f00d000390002d02103912103801040300c09803a68003413089403444070082e1500882c090140c04e00d80545c510080052400f83c0040740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 690005557 1250 690004307 690004327
    0x70f050114040b0f06010e09150a050a08250f0b0c0c04090b07080406020c0f06010312020a030807030b011206090c12060b1204050c0301090305070606083903120c0c030102 75
    0x442076004c400145498090b80c0d596004a990048801c5d1a076001880501800707460504002e0001c6092000d903440300030a541c600500014040c1c40c0714a45203504990301c004034010031031481e400c140400c0c0d00042c02c00d42d100d140700038044020703a20030003807040c00043d080c8081100340000c60320310740b040350204032451050300d0708508400b00401803420810f42e80005410000980d069403003500400c004c0720030361044400382540e110428003040c0d404010046440c9902032000072031799031080c0c0c0366860f40170f40d40304d01d8010f502524501a0315030600c0305401143d10f1045980c071940d0010009150701040700b2104101c082c004031000980400d416040400a1204d01804c604480408403560018041507407941842c6080580e5100010303495424044144203241d03009c0013500c0c92601501040104583e1440130b40e82d41c00c0c10071000c0c90a401030076108a060103c00210b007802400c554074440c5602e11000001e4200f4030700e0119112035540200f40404240010440c000c0004c0c4203900851030885104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 690006807 1250 690005557 690005573
    0x703050406050903071809031403270703020907030501051f0203180409120809150402090f18070b032403070519080703030e1216030224070f05011404 66
    0x8051882030207800105007a91303460030014000200980402440c65a600009920180141000980001d03990070002e03902082c0d00821203003d071003000c1e1a2002c3c83e00003480343c1159248010481104e020364100000541c0310310b600c1c24030401040e0340c0010310b98180410816071b0540318440c141f240241034000c22905400104442c0d403401c4000e605421941518000340150221a0004190700d045500e45c1051542222580303010350001015070f040c030103041140e003044200031100030350710528541c00b0074480c1640310011034100e15441600060041030980c883c0c60241d46a02684114078004200b207100b1841d0b4501544a13200b255140c140c00020000003503980c3c00c81d01507140300e00c00c2030b803004500ca0400c2d45031100800c0e000050354942035481c2400b41c40700c5011510031303011300ca24014400c1e100c0c2001c10407052008552001c010303114155000e0104503444a22140c900003005e08080300803500380c0c80541010380c41481e490708411145c2c50006d09640c03981139806030150300e20040c000010012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 690008057 1250 690006807 690006809
    0xe0f060307092403081305060c0a1709060a0905030d050c060105040e03190e0f040506030a112107050a21030c02011812020f0a1401030218120604051207030504 70
    0x9040401d510402000081e4040b20440c150703120043c1d9050b00000300040c410144c00003141d110703105030145a4610070701001740329614100c001c64101900200008941d01c91048070034860421881c00c1110007808078009501400b600e0003c9483c505042107a4a420040444606d20740d241642c14a1544c0110540c1c440c070601074648910388070307445440f10388020016624012005101c1090246c00c6c40d401810b20101286010f02610080781d42207003e0406000c1d640c000e00d0301800600d5020181e4403400c00c4815503e1119074480ca5101c3d0140e500074981d001d500c0150440780c05040301c2442d00c1c040140d483c01640c0300b00310100810300070301c1e101c01c1e5050384110000e0701800e05461048541c40101c628244401a0000b0103132800000b15103e42a03801c134240141c401c3c1d840c040c0200c084d00400c0444485407155000c105a00080d0945a51003034014020341502c5441d09100042f030309001410009501d5041c4095074010001c2005215041003142441041c444245160483c0e0b40c500400911807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 690009307 1250 690008057 690008069
    0x6040e01180f050c0901030b070207081902091f09060602010f090209010506070524040302100e0c040f020d090605060109150e0409050c210d0318140a050a0503040e0f060307 76
    0x35001a800c2845003e0041354100180100000019a10b1386060862441c0030707118100184581480400c0742100068801140c1c1c00d10440b031820b10301035500b04504032000800500c1036142840c8403c0c860881d01189801908180101042007410150000d007141c050162026240d410312600d4805610b801040b5419a00e0694156580c0c1d590350800a10301207591400e10300c1c50b511855600001803140000074001d41c800c2c3d09070396019003888103110507038600d500004041e401c200d48241007440c082e0b00284103174140703200c0035081500e13080c440c2c01101c00e006026610f80c0d85442c04c0000303c0d0303804400140030300380961568000c1808261300600030b121900c407081c060b030b54400d201c00922034100030398405a0701c0240b2908039001041e403800c807458400e40121005108544416018900070302890119103040f241516400c101915042840000e02003c260740340903202825001c224140580b9880c00c0c003810081d941c036440d251410303001d403400600b061800700c000420b01c1869680494600304882e5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 690010557 1250 690009307 690009323
    0x402060d0b0607050f060103170a0f081302030f030301090510030c060806060d0903020d0f030606050d0b0109180501260c091b04031b0512070e070e090c0306040e0118 73
    0x41e0200410614803d12030040c20030b11628144a040510004072035041e44d101c2c2680440d05040c0580da18100d01a40c84003001184609050701400b511403038409034030800d00f079a00240001c1b0764000c40e0030216000300030031030ba410000050082c01c205014140e000044600040d61061464072454418816400303460204075810300800d850f82d03500826070307031030791003c442c104100354803860f01030340c0c510304040e0305008201c606414800f250301134480c000071107240740c581501c1c00c080ca00d0f2250080c411001401c1c10b100c000c4d4004078042e80049150b40c0e0302d00d4140e0000a0741d50500800c0941c072060710a01092400086454024604012602c1a07600d0010385d0180ca8540750300b0905150400342141060f04100301040020500030004034007598100e0100f16404503d4a510501000100814038650164442c6a00b002210200076103075a0007101440c000805203260400203030340c8101510700d11643c0801200b4000107140c00e218986800c1c1042000704154a44034040c80d40750310b80c41c1c40181c1808 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 690011807 1250 690010557 690010571
    0x1090506030321040309171b0303270d0b100807050a27060e1306060e151002010e010203010b1206010c03140c0f0a05070e0709080615010302070606030302030d140402060d 75
    0x500500f407840203051440d03499900000790f00c0b011360b600c8c0d0680448038034140804005070501e003400b01c100e41c40300340344150802c446449650810844d19010385c0450700083c9c80c140354170111312201200d6015400f1810b80c0c107902803904110703030726100042d0040c43c802c040a910030800d0b0000783d85400110041d00f07110206003241e1007007400040403a940403501059060041101c032050680003201d009100e0442004250703100d00c140d01c040708040303484071542900800c145c1034514058440c240035000ca44000301e04400b0f0f00b1446400e9800a80c031120380c9400c049034490f14020000300b42da034002e00a103084406088140c50041400c420105404020000041d00d81c0c417441082c80160501150b04003100c440c0326592030002c1d038941c158071858545c01030303080200d4a00740c4079903000b4080716100d034010402030726104803200b40700c0113184085050590804c248000541d041c02114000c2d4040d4000e10f40b0b40303c107440c1100545514a489a03007000843e002c000040e9160816036038200901c40b4001642 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 690013057 1250 690011807 690011813
    0x5090a09050106290c070b0322260c0c0f01052b14010308121302090403020f0d2a0f0c120312020c030306151306080109050603032104 59
    0x304003924014125509091011540e02d12140021000401c01c800100b00f5804c940c0c0a05501d01400f801c1500640154038100005000000070310b03000101d03c041d95410380707150b104804842d10280300455070342c001d81c01100e0080805400c0f0b03041e07001401d00e0203071520440307040782c1d40c07102440480d5900c948014840070303003203034400c0060b03c00c02d814001c0c2c58014000a48078040302103144280049031142405c252221a00039407103118100d81c1e00100d403034100301600000340c1c91038000400c05185040014a0103000d40c0e0340485003809140240c0140141554440b035860401001c0c079020414000165280c5021400300041d4040300f6081a03c60741c03a190071881c10b80341c1c943c40309038098074101b00c8220101c0c250b40200141c030302c018800c0e200c0c01d0318111601100010380c01003519034042034105000040c0203007012204852020100301056280585e80b1103021020302c1a40c0054001886a03001030214000d9482070b00e8205400b10000c42c182040e41c100c030003256034400300b40480303050203801080130 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 690014307 1250 690013057 690013061
    0x9031a0601020c0108041401020a0c05070f0b030114040912080a061a090d080d0603030f081303080f090705090a0603020406080307230a1205071e0b061005090303220e0702030405090a 80
    0x300c507d102c0003590f4620101f140201913006d214001c0c2d0b49800382e040c001917a007241c84d002000700c5810410440c150780c07a06c01184107500207100d03032640080c1c4840006000403c107001e00340703240d02c0d60f0716503403818246100404201d411640050707a00312100101c041000301440145d90803030004541348000d4042c103260003050360040328001c611f50f81c18040302208040d0441e1145e152078619540f0f44105a4583c51402100a268003000e404107640300046514103005000c074030341c0a101034045560050381d0750302040d80d03c0412548007030380580d200c030140214030b010700440e4000e040c071070001c50610410b0349a1290342e15038007181c120925040280310301d080300305009466070541c01412210405030300302005483d41d88051001c44500014450381011078550720100a4081c1c0c103d0412072843d0b07a00c000b4094410130329030340c0344280102408040890307503081004010303034903419401c148405001700009152003040e401c1078550b17040742810045040d9000042d10221403085031801c08644440c000480 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 690015557 1250 690014307 690014333
    0x906060c0703060e0a0311010b0f0103270b061203040b12061c150c08090706140f03040c0503010b01050a05090d140604140706020705060d0b01110303040309031a0601020c010804 78
    0x703d481c2c1441640061081d01040e020740f880d0080e142e080c1070846c03500c001ea08845030500810b03030000304103000c0251544079911075540c1c104080b07180e641200300c0290700c841e8094510800c07a0003406030800c00c038013030038208800e0b6024542c4000442c20b103402d003008030005000c1c2004402101500ca4002001982c2d1030714110b20009441d0001e07001d14210b420014191000d03844940101410203504540c110720480d1960310940d2044007800d0103c0c241a01114900c141c03481d4400d1602e00ac1c09080c5c1102c02d148015405148160303058510710340b601003030609645c0044140c2e07051080030300100440c00d410030104c0c2c088200890305903156121920b8075154a042404030455070b40325007030402042112070030307003034006080d03480032078900c56030310423040766a680d1340d018550304120180140e511041103034010007114881414000c104032071003c021031842c6c004840c10fa0006020500c10001e01c43c00d408200c03507140a54041903407030f10f42400081d50340d24a60000340d04100c11100058288180500b64803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 690016807 1250 690015557 690015563
    0x60a02030901182d0809100905031b180408030115020106030f05061b0418050a1d1f02190f020f010c170a06080c010c05070b030c03011d01050906060c0703 68
    0x2010450103400d110440000c0000030340c40035110600300302c05480340e5045400e01160311170381061600c8046401e011000c60228021010712902100101d00d5640a0003c15101080c04490600c030101c1c40c010000c414400000c08288a10200103010102e0090341c21030741540d01c0f113543c1401d1211012401c03030040c0042c0d0320181c82c0300380a056078410030101040746409541804010b01080c041c5150418140c41184030303400e00080c1070700e82d01401070020340102d684145408000503404143c400c010708140812030041429030001a00d0098610b5008004482081918011030a11458001c0c0342d8415080784d1100c0180302203c0000340c8154400c218804009c0500c43c02849000d210744405001030184040101d141d0034084001001a6003511a035812148500003c0040c040b110005640c0b003000c010b000c0d1402d005500000c26448084002980503001c0c180620744d17290300d030512601c40010060b40020b514100c40f0010419955600c01c100e401043c2100c0ba140d0300d0a0082c0c0962601c41258001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 690018057 1250 690016807 690016841
    0xa060f1e0507110a05030606130905071509090911040915140703062103080c04080a0305030a0e0307030801031104020d050a09020f100926010e010c0f0c0302060a02030901 75
    0x3240560060240407602e03c1103890340c00d5a60407408100c280d5009014040e01540480000b0300c0c01c1c81d2008174071600d102c803a80f00080c0d00d200b586949041807440e8100d6203a06c0e01c4520140c00c42070744801010000c08401c1c5d01041143c0c115502c07030019000700c0c00c02c64401ca40350101c010900081e52122405164880c40c1005001e84201d003124420008461078000303e4500600091541e030700d005040603507500e0600440074246541d400341d914240113460504200d40502011803400c8081141010090080e02c1d07030703a100e1405a40060507200010640c100c0c98009001080010b9003003010a070640354002c088200b00390030440410000e00580c445188020300b05414400f80c0015544614030490003550001e80510508061000d5107880714403090008101c00810050300c10b070303144800f40c0c4012001258042c2844210103d0940c1d001d44c0d10084c083e5134421124a10a4100c0c001e0b8042c10a0360408004888003901c010352a00f000400781280542c000000030a50b20b000c0d8840b8034210101000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 690019307 1250 690018057 690018107
    0x40c080607020642040b0a0e011a0c100509010b010c02031b2d03190803040b040303020912250f12050f1903111b010513090515010801090204050a060f 66
    0x201350940b107040140c1034002e51800c01d144d840750400000302c00568034545007140b140c1c0d00c0c00e80d03001d00c0c4100c0c401004019202c180550210301209001c81d040d420f0b000c40b004203190800000090031218031480c1c40d41402200b0181000585021070009400110503100c0c0c40d142c2000c0d008031b0241144076290740403030030150001c42c044040b002020705081d40d0607011105007030f00080340080801018400034080780010300008000480420b45a94020300c41e240150805040c200418641c04080b200300e100d079000540c4444503818030284a034441c10083c09c07450041c62500f071074206484001e0150380c903249401c420b450280f101c02c01a402c20b480300442101e80302c9002d410607075160340700c04034110000350001c050040c8aa000003408074940c004108a10400e02c58000103503100c1c0c0c031460400c040040d281d4000566028940301d9a07115040302c0d90450314001400000401090b016000401c240e0301c140024061a11910b81d4881503074034505112011010402d02034841c0401625980c5074000c030604 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 690020557 1250 690019307 690019411
    0x30709170114090105060f150f03010f08060721150803040f150c02100c020d0b01030b16091a0f0f03090a02211002130b0c06040c0806070206 62
    0x8010b604624800c1201d140c01d4903205001801e90b02d081da40c09500c000116511301103031808040510180b0a551482890007034001e9407600c0640090307000ba9101241502c04102e01d20040c041e043e0b012004e40307040341d8a1540c6513129601a56049840c03030f4000d0717031080e000b481c0d808085109400307846114122030701d8582e900b00b4040b0500040c0102d1200a1041c40c0c0c0c2c4103d14015910440500e80c01807518403841144101120503414100090340d0213202e4030041408505820702c0280030310301420710090030740780008807102241540a03410080207c411000c000c0d00303601e800819010300e40c56a80a5940200000351680ca0180111820aca08000400e001c88a0303030004500d020307070307100741c43ca5030105410002d0300d07568000c15054600d054000013440c3c00b0b5600c080c3e0060030300501c06000e015a0750f0301c3d1040030496401800c00c21310640d1000302440b050006450441d8010004036008280320310341102e000b903da110203001030781d04406181518000340303d007036890310740c541e40ac00e003414285060107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 690021807 1250 690020557 690020561
    0x70204090c06020d09121704051e010305220b18030406020a1502044e0c05040917090d020904081902030f09130f020304080c060105010f140307091701 66
    0x21003100094860010b44148950203045d580b8110350301c4c2c10280e004040c3c2921801803078040609a01c035a40700c1003001240301d070b94018060704c400340e81a601703005028081001608440700038010601c18000c04041a00402191203074015903a8021030040710307601c6030700b981410160854410043c600001ca400303c4c2c42c070350000392003c40d14041c000e00c1e0b510001c000001000c07446540070740d0411400d917458034505102d619002d6039400421503508a140ca107600c1c03e01d040c000032021702c80d40c4d00c021050f502050281c1902948054003040300c04111004ea2555022000182d840407440540070101d6648020340e198280301a0054025240c094a842d144c9000001e95200f0349828004000100666609510000a5130302c12100842580d01d8403c00e00200041c1c6860512610b601d90340b100c0610f60100441d00255000d944902046501e906031400c1c101c0c02c00405805c150704004d14101e585091030350003010443c1640b40404441c1c0d40391204401201c69001d03a03004029150036007603981306803034015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 690023057 1250 690021807 690021809
    0xc03070c30030c0201081302040501091d07061e030b040203010f08060907150e030a05030d201c09021c110a140303030a05090f0a050d0e01020327010302070204090c 72
    0x60111841000407846032280039228514000d000110a110710200550141e101150403004ea00519a0480c40710b0380014181d8209820900500e5110124403c1003070607403d0072601c14820401a241d12030230318000401042d02c450203503020070150b404040c3c1031402a4030031603c7d54806881550b1700d603141c03200341d004092a4840c0c1e46151040c2c0c800180440c402080d080c080c1ca50100b4455604000c800040b04c0c240480480154075004511640000400400082450440101012400d03c450b40880703070031504458a140c580550420084440d0101c0000405060502510000d007070f0f0a2400441e0060403101224010700c410040030200380b00042c030b80c41420400c2140e142c0d100b1900c03450381c0d4450744032509145805500074404200111081c1e0840da80c0300021008544541e041803840c0d48c40c00080c0d0000380c8098010281c0c0711071103035203d02c0100c03000c3d20078002149440325110b01302009414100c12917468203662552a07007203070301c00c0d01100e40c9550000c0090000c1d10080c2807806220384a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 690024307 1250 690023057 690023099
    0xa0b070c06120209090103022b140609071503050408070f05010506211c021c050d050c09100e01030f0c0e03060f0f150409170c15010b040b0c03070c 65
    0x1d140880594442c940221002244c010700720304c00356442d50342440100304a148914404018045030512105004203a0313801081c0542039500f8150350405042e81415006820840b880d08010301c244a80090441340711030116107407030f0000d469940c50410190390b0140b100001d0011804888503414848150019406101e0480d07000d03481b540c0210b480d00d82c821180c000704403180c01101480d1707003518603088a550f03062500c1c0142c54001d10748201d0300150600d00030410001c6400881c0305000401907110f800d5020100b0401e040c60200726100180346001c40c200e1080800481c00c1112030b2991013034020031086498030900344400b01c1165005004800418141802840360200043d01c22201501d014050b907a0305038484101d0f110600410301070044c103281a5003054407650000000b40d2021003004030903d403061000e031104040e507406428402c4400c495501d14250400522480400e0000c65040b288190b054559405000c0403007420360141c41d001900c501d079084400030b03030442c6800c2c0c0400c6810b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 690025557 1250 690024307 690024317
    0x91b0102070b28050c0d0509060705060f0108120a0e060705011409010c110615062101030b0a0f051b07050705040615080a0903080a0e150a0c020f03040b0f090a0b070c06 74
    0x40b0f00801111180100e4400d9030503544841000e43c10030b40910018540054040d0241c1d1900d0030603154940340010580f40f5180214180700100110102805582d200243c08e003400307403405103061070043c1556503809465204840c009405004c019096108201d1451804c80000700c61030b018001c0c5000340f090350b120301c000c95510f9030030041e00c8402280440c8600083c0c100351200584d40310500c80c071504540c0d45501c0700c240d10200071099002e81c030f403494006c5105441c4982c0c0c5d482c108a00130143c5000c0d44102420b41e00781801d0206a0006414a09042c079030500d5140d150005400e05d01d1405c100b5a00442e002440c0120200d02c28840d28103036040340c4429221080d0f940c031040310010455000079409000220b5000100e802d042d038540000f11040c101108a0706000c540070150458808269100004960f0307030010b900c08150180407402c100e903050400755051a15018102c1301911400010b601b80030b000042c40d031803664900300c0c42c001400320940c0300d41c2c442034140b600e03008031070780d501400b00854 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 690026807 1250 690025557 690025627
    0xf02040230090d050309100903050c0319110a030c02010e01050912030403020a0e0c0403150615091503090f260f0301090b06030c1602030102300f091b0102070b 70
    0x9004d4403c581c000e8100c1c00007484040003008191004045901c400c8080200c104510054040301304040e0160a4140880c6c102d05140202c000e029881148118a0142c221039514070200b42c0000035083d801d0780a08082007050000d4004a42c2ea10414050961207160199111800725000006d41f0a03244240c840d0400903840e0b117080301400c00104c45400c0d84104c108824070000c0c107003140d120f280807403c40012078181e44450343c040c0361002c0c9400c241c3c00241c142a003000301000485052181c0300e0705044c20008000300c1e4443c98915440b11303038007410895201501d00d40c05408102c1d02c0e040d09045685558940711310407000b0075a0342c001e10820507114200207080c1200c1c07800c1c030220380c05110800d501741c3c0761034854540440862401d040a1380d02d95428000348404007c100c0080090384021407103011020f500d001001401030000e803060b18114031070401c20100c1940018000c6003a00c2e46120882e80c41d00c0f190040389040415041070300d00c030402040c2e080a07100b00b440d1030282864404000799010f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 690028057 1250 690026807 690026833
    0xf0b0301051e01141302030705070213110702060f040807030b0405240610030e010c0c020405150603060d050703080a0e1008160513090c0c0507060c0f0204023009 71
    0x21602d0407900d0541c649008010010348000f100084060709014201c800300a202c49400c0d400c0b40c004803443c1011800c0061007008600d024088188074201c001c1e03080150106803810f030100390103446002800343d240011101d40c0c440c01501511300a007200c0b0304580005840b480c0c603002c0200103490403941da00c502000582030804c01900352a89242c0841904203581d105010400c052103240942024550703101542c1001c0103003030081000c084401c0e01ca0484200d8039105200c22107400030720441d96400000e044000544d2030f4400c6070341044040300d01d0011500281055424425550700040c518000001e17503601160704402da40c07002c40d04c00c80790021280b8100c9402d40b0444012145901c402c224182c80c01e140c0c43c0103001405800c44001b105012890300c40e0741140440703c5071040c80000c20b40c030f1016001000801c04c203450281145182401340f10760f46c0d43c0d68240048000c00c0c020302c5640c0100e540298000324151405a11910300440070056240c0603009161003002d5a04803218040da80c102040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 690029307 1250 690028057 690028081
    0x15020c130507120c1b0321181101050408150a1a0d0204052d04050f07080d050a0c0209040b0702120a080a09140307060c090603180b06060408010f0b030105 68
    0x400c4400d80c0b036101001c044200f00800400134101040d06202c150708819050042c0300c0c0d260941e01c0c0c400d07190a02648082c1225081c01d42c10212840303041814018408410300104042860155010540300004500c03400180e8040c01207070005003861082c1c504c0042c0d42042d03a041940510f06c0801c08000ca00c02c0c020101c841e4022071007a15820008052043c4010700b0540d204581c0186001e058442038141a0101e9408500f16503000e02030074058820b020511000b4005000b18000174030050030070071702e0000748a071074000203031280d004c1c40000303d65910b0260060004911039540240700403042d10b0b040c03511080900040ea2584014804e2110041020742550215003403010142c4400c0b145030303907604a80e4050f0491a40440318108080c0c0300003c0340900708060716050b485a000442d280344500802481d020840c2c2c0103400701400d00e454820080202e962210311207400001e04102540ca440115041d84620b81c071416031580f8106220600409591000402900490080c0400c0e1a10309206030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 690030557 1250 690029307 690029311
    0x61815150207150503041205071a0a02161b09050601090b07060b0607050307061401060c260c06011a0301050904060e010617010204090b0d020a150c0b0a05040506070810061815020c1305 81
    0x10f8040ac4034403e5041240940950364480788041004d0700e420b40080c09031071120350585085408401140c8001c54019010038140040c084061007040703d45030000000340342c41d500e0b00c41c496100300001540c400f4000643c0102e040202c0c080c0c140e550340c600b149011a5203030f100c6101170750f8103854410141520707613055003082d040721a01d41ea41d4691190702e48410780d0004941c914240965000c0c0d4045d40d41c0d5012001500b1340190b42c9010f44119817400f08000e203c10007210060300300c60404c000500c42c0d556240041d0350010f401203c00181c001080c4031160041a0f00d400541c00014110b40048640005400070400d441d00898148030300c1d412603051144c03400040f24029803014101c8401c0c00032032011010300316048000e01d0103200700d149640701c0881d803005c15038091044649600821060000c00c0000b0340d08035095107070501d01c514091002a503404450f0140c1410090740342d10341c001283c00f0f140b030b070000fa040802c0b01116034611004040c0d030744d810088440d070040010700c000141031078107441128 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 690031807 1250 690030557 690030563
    0xf110a0f110c010f020a020a0902040302120a15090501140903030709050a03170309120301260f0d27080106050418150c030e01090606181515020715050304120507 71
    0x5240e2142d0001500d801c4070480c0c01e01c08600c14800310b0009641c400e005280100a03200340181d8460450050026450040e003001c016688180102000583c1280900d0010b000c2d1a0380000ca07003071945000d07405041e0f211000101c0203169818009000c0020005500540d000e0722107018156850050144110907032001403d400141e0034064024110bc80c02103a0000790201a04c5c03150340c0b9001c0303118454000b81c104000d07040b14400f04400c0f01c49100002104504044018800c1c440f413002819a50b580040b03058041100640d0720940468807185040c08608020208089a139140d240c214000c2c01c0c184100d5110300c0c105114404119110040c44207036035000702a003a9410400c45800000d00740c1900712104140d920310002c00000c07400e20903c0c4041c0c0c41040302042142c50f158440a0400360304101050380c034078001c03410b0803078005200f0040403038082130703520b41c1b08510500059090401c51340c40104014402209106000da01034001c511840c402e0009070410b50184404035501d005441c001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 690033057 1250 690031807 690031813
    0x60e030a062310050310050112060b01030e0f0604050111090a17031e090117010b1806090a060f0f0906080f0a0b13090201081321030f110a0f11 63
    0x7040c0c598201d42046601c0660485840c1c0b03020490224a50045800f60f00c0c01c2d0030110b0900c15451709000c0c107095019260414130447d41420716011440341c05210060459a89118a1025900941200b00618104000d945d007956030078903101d80302da4044408654a510b03080d500e070a115604410707264451f0020b000510f405050989000380c40281350b960484905c01845004c40c0c00b0203404030280c40c032491a60084d102d100020002d440984250310034140702441b0360040c0150201c1d01c050364000050f558081d40c240703c9100102d074040c403d00e080325800040c4d003100800c5081c0c11a00c0c40051035920359074880e56800c00e4804a441c80c03418040d5030001841e56001ca9420304041c0b100035040081180c000038a040e482d00003c0b16034203030b07072040103001c0d0300e50407400150341c0c01204840c1c0c003540f042600c1c040c0a16598441c07000108554081d1500064154280703a210320941c040714565801400c1004a8544000110900d8100d812035000141814661070700007403051200001101d000001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 690034307 1250 690033057 690033073
    0x10213051f0c080d090203030d09120309020f0d020402070602131802132303161a04080c011b0602030a0515120a12141204030e0901030503030a15180b0307060e03 71
    0x1e030f1072a640154400005180c807000110050b94003071004041031110101c0000d80703040d0500c2c150400c070070030180715810300d890031901e080561138120482443c0c4404840c48150802ca0b031001070024003504a0107000b030341c8081501072141e0399042200c410f48080405500407804114890001ea1040803c1382c514a5014030040020064150641503504c4100c0040c840841c0c2c0034011a00c0c0502c2842c2e0300a02040c40c2000b04208a40c110000c0401d22000711490f190034100518556a441e540c001d0034100480b20715203820140b405072080305206d43c0940d0940d030b01d0a10a0100010b4030301602d103404800c804401414452420b904280c0c3d8070145040500081000c5442c3d01e61403040c0d0160703510501c40010900c40228030444001d0115080c000960300d01402d244c28001c0400600e03000e000c1c000d9401c0e200601c0454070000940c0d900640c220004100159200c071302203803403015584102290303c81b1311034101c24100c242e000303031501c01f85c10340444d00c0d425621101224001c1c1580c2c0083d4047e000394907 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 690035557 1250 690034307 690034313
    0x3021e030408121f1e170c010801080d020a120513030501270519051905070f0801060303090b160f0609020f0a0b0403060f06050306040803010e1b03010504090212010213051f0c 77
    0x3542d1741c03440003070310203d104995495851000100c00b500000c1074907041450401104e60704510380d0340c09001c80340c00600484502d100040c0d5a48030904010300720b460841e0800038241d118004807044011101c4808604513540c0c42d20034060211071490300d4842c05021246110b4007808070103d4035490300b04009040e010754004500c1000c16842d201a00c03140145810101100700b2214981b8001c0d1140000340680e62070400345c080380c6840c80d08950481e034105034040000c83c0d030001410f02aa8400380b02c040da6001c95a400394a14250710200521400324108520284152540081c060900039104034a40c0c41c145400c00912000602501048280a02080c004240650702034400841001c0c0d000504a45410000b8a002c10450f800c503540e00001005010750751101c80c0395a000391403070702e0703040c5d0080104a60302881e0105014150107250303110800400d40d500d00c040084000d446000841d0750310615005a01034850a0042901070120b546002c0780103002d003c1121a0715511b603a810414596a903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 690036807 1250 690035557 690035579
    0x4212030c0b060307091803080c0f27150c0d020c13021e120106110102190c0807060c0e0a05010908150402030f0303010909140c010c0303021e030408121f 67
    0x24080541602c10b81030081105d101c1c92050b400b2850320400b50145010340c03840e000b004008020503d0070300e000180f0030828165102e0069030300811880700e020006c0d004c990007001a2001c2c00002c01d600010300306c1410001105a001800e485d000003090384d04195444000366604e03081c203a00341e900b0a81c0398041400e0030280f540540544040c4803140006a9001140d16000703170031403400542500b214034010403240d600268520b8416020307000039414038030f046211013403109012080a044c8200452854100320001c01141c0007142e11860030400c0d0845400c0080105001d50307000e0f4080c203009580881c880d03000d80c505100726410034000702000440d0005401501d00080c0080341c05104050404100003400c2c00518040d02412000042042481c01d20070301002c03207840c0d01c0d4101c3e00a0013035450a640e00c201400340b5540c050030301598030b0118a504018030026400c3c0213080c0708000c800c0c0400c1002c11350003000c1e560081c6d0007403011a110200110001c2c6401e044526828800807800c00c562404c0d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 690038057 1250 690036807 690036811
    0x150906090a0b0102030705070b0901020601061b080d090602120f060a1406070c0e010605130e090316080903120d0f060506031b0409050408071a13064212030c0b 70
    0x61050381c6c20005a65185858020315400c4010799800115192445507810850783d40104103500e4004040c0050341201896007551004c043c02c000c10014441c00c40040a0300040300c01a40b000e030440d5903003c1c4035145840344101740c449425218800d004502d4600d00020134030240c41d12003140d002c0e10300c0d95030700304142940469400c58131f8108610740025a210181d004600030882c1c0d440c2c040e50703010b118150650103c201e40007942c810aa101c02d1118a080003c1a0382281c404002000508400c50401005500a6880041e858400c10095400b03050914026040b08545c4940c00e03c075009001c00351a0590391350780100c5402100a1000510481c1782c2c4021407100c4440d903002c203240030348411860b000d491040328240c0d200500041c03428200800c4c41041c1c15008840300842c005130619145078040b02501030400340c2065150700c050200110703018059188407035441c031209010000f0700f0f0401d200e0100504106154081b0044c0003401c022010585202a54140d4a5500083c203e030b81340c129401c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 690039307 1250 690038057 690038059
    0xc0e0f09130f0b0f09030711101e09030b0a0c0c0308130c06200604020a050420070b040308100e18011e0b0a09110d1d03070b150906090a0b 61
    0x18140715800304800c00070240c220b07400b9040590103031a01c0780e00c855032248090180b074070710f034070400c81c0002140c00c1030055102c00307a080f51a9010300d074105070b04a5101111140014800000141d81000c5e00d0700303d40220202c03403207500c0740c011940e554414503048564441307060020031f11a1916100003031040316110361000402c02c1c45200c02c0d60f00d40b9104d021030303c0c1d504200d01180031000380e2051040d040740340a03030342102c000080205103880d03400b06801c1c18007445894015a00c41e03036912600c4010302c885070a01901e2800181d194405410141c1aa01082d00c0540c0440c0c1c0101c007190702c20281c000b0f008180c1d11081d000d20f00c13503250140100b45014603141c141c00607559414030032192842c5c01c1d9407210f40742029100030401c009014100316039100d95601480312245020f44026001c0310807019a548640b81c5400050140c995070150340e480a0f070280300951502000078400b003000a91151940600c080f80c1d80250741040c400705001c040381055494951005841001445541c03281d0804144810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 690040557 1250 690039307 690039331
    0x503030606070f0b0916081f1a061329040303050d0204030f03090512031c0f020702060a230703020a060f061d040b0a061a0a03140a020702040c0e0f09 66
    0x48644404044c080107031412405604001e03103201c084c0c5400318200c009400250090705950945401000e10320f415141040451600c401d60340a006081e03400e004441e5002030701032079a40080c0d20410704034104500840b1511004241c071130700d05054484643d000311010310105803815007151000e1720303c1d4001c11848000103408110100004045c03510ba100581d20a8a4140303103103062008001018040c40701500083d8001d00800b2100ca403200c074031181d040a10f039000508801419501c8010340715220300650010000104020f1903540700ca17009080c1da0318500320010444031005940007500c1440700240040c2d03c40320b000d00105070740d80c0c400041c8e1618454001129544c403032034a8914086801c00d01d075005019001c00052008000300c1541c00f02c0c1c0359804200e071504246502034080e8200c0f1a1502104d00440e010080d1406588030b142e03000b4044041000c0c624100070041c020f9400900124015810224002c824074058000d00080e00b00091118100320703200d0301405400500205906610b030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 690041807 1250 690040557 690040583
    0x30a110a050a23010513060c050f01020307050301090606050a0923090a02090a05090103080301150e0d0609050d2307060b060c0d090f03331506030c0309050303060607 73
    0x39035403001c0303480200881d003001074203620311040d030000c5401c0f075000c058140302c0c042145031700e8515172481c0081580c02c05e040c00c01c2280303150300740240340094801140b25a036100109102e100c980100c0070b141205d40101c801e119482d280c60044800d400b40c5126400400d0414105000006140d1a14031180038000d15802d40c1c0c1042d64001504011b05945031031034107a000a40e294039041074207400c80030789000c6c0c0e10b80045525541c0e0f0200076100501c95440d40c448152001c52116102e0000580e81c0d49005044032036500940c103280e802014060b408465a21440168040e403e000d4011110411909000442102840c41e4281020ba000c500102c6e0150780d620f48500007540c40001030240c1c0710b00103004002c480030520000c2e103440340581002050500124041000540200a100507000e40707800300c1070082c400405c0401c6030754801d00d50b2078010341015503440d040015080706d00d04448065605000000501800f64120742d0401c901528580040000401505010006111f01445051001209 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 690043057 1250 690041807 690041809
    0xf0706020d0e040b0910091404120305090f06151e0a03120504030609060203010f0614030a0c2d0e0609060706090f2a0605211b0a1808070302030a110a05 67
    0x7864101d070201c445c406402d2007401480d00c1f901c90000c004e44210542e500c0f0742841d8403203450004a21001908041e10380c0002008030b0000d0114000c0d5591510485039039090000079501080e080420040c0507003160384003002002c41c00c0b4042066040080c00d1007079464110b894030310b00c003200c507450141032220410000000501500c0b4081009015507401601c0e54100282c00b80a505594805010031452000448201c5002e200702c07900030060b4400014941020340c0150f85050f913100c0d044424100803082c900110b07030103000d1404e030350f04980d507441850901481080424010170078081d4202100303220030310004405602c0018201d000b207950184813801a039991163b44180310b003500000f50620704aa1005600100c11009050b080c1020350401c0b51740b00340203180d0031714401803110403d12000404d074031a00d60f0882064016188511a9030fa030b1000501800e20000d07040d8094029032082c00c0060208000b241141c10f0b00d5004000d486420001e03119070105031102c43c5215070081d5021000145 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 690044307 1250 690043057 690043069
    0xc0201080a24050a05040b061b010b040c030c08010501020d05042303030f1b07180c03090203031306090b04050303030408030a0e07060801081b0924040603060902030f0706020d0e040b 80
    0x369040b991001004500302428001d07404603960045000320308210311482c1c913955010a0302d01c0302c800b400200c840c0d003202d40e6040d0301505040141a070001d1a00c024607079182e85c55000440c100798682c079410000c0c1d90b10801240e9400c01d05040030001303041440288100b02444560121105c00c800240807110b000b980040d0440d8808044840d407000d000504801c030b80d40d0903000e0510441c048020708829881e0910100500d080c0c101501c43c02540d48500c1c0c540603020f03a2207160707450b40141c103d0342c072001500400341d0045140d0081e0004144138400000700910400d04903402d0300c00240240d400c0d074550ba031380d015494002900b0b481d034554461100032001c2108104000040209542c2c031401035242c15811800c0510f01c1d414404e814040c0e091855250f16114582604103403014541d5000800c0381001c1d04020720f152908a910a04004c17001080c003015401201040780202c055902d158020b6500941d41c61b950322440c00960440314a1002140c0221081c10b45585d001e000482c140c5400c03000070301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 690045557 1250 690044307 690044351
    0x100c02150f160905030a08070f06050424020c100b0102120c01060e2a0d06030b010b09010206242403090601060e011706100c05070602060f0c09010c0201080a 69
    0x15054010400d040d00342409920000402c1e080c0250341038148800b0a456105900011700418400203d0384201300c800c60800600b00e420090800c29400c2c40d2a00405040c504640c15802c203134400032800c140b45052088400006144006200c0130500100444c098081140d04a0560040c1842918400d50001c01021026520000055681c0c00d00a803000c0b0781402902409405031440d00c88601c0d06a010f194010950300c9528290f100d6a85000b0800a4007940d00000c1c050000b0400004004020310b001e850800001d0b02900e0295403828100c0e030340c068290903125520b400d1100718101c0d0b810300c52540c1d0500328401e05501466400030040286e581d005030703010416503002c6401044607a5001034603218000382440c00305642c0b40200624003200c000903005510502d81d01c540344001c103025180301c050403940b0500740ea0070240d4400303000e922580308842e00744c22502000300140000c90000c1c212062104140c6400c95417107510340044030350100060040c201c5a5656a40760b500300c0a07215102c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 690046807 1250 690045557 690045571
    0x30b060303040f1401021603020607021318080d0b0105120415021b0d02070e1e1302040c0903030206060105040b0a2712050c04060803030f090102040b0a03020d1d100c0215 75
    0x303c036410389a0002490032004681004c00c00c1f03007003942400142d60b00003c48801980403176020003460f1502404ca03006101d50040d8a1806815041050030041e690000d066400c03074500003007000707054140054a10f84552900b044802002c40c001400203111081e00001d00c0300b08082c01401c0c800010300b01c46004450300300c0d900b4a90701c08021901840c0e0304010a40107002c2c40300e03a0b48624141400c0e41112009225500086115000c00107240070b81e10941003266190010f2051040c440003010152080106000035801030040100080c207550143d0200d030100c03154034000515209103802c04403072811100d514a482c8401c0300012504605a00100348041c101c82c4003a002442104c0c82c2851401c001c24103c28022400d0030020004924007100303407a400b0b4401c08d040345440d41c82284050092080f600030300740114000c24071120305070f815030260565000d9a00c0c2000340d00302c0d94510000304035510f1801d1041d54008940d886955545401c82040f07a40d4900440c0c8180f03003038000003000503a088420f4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 690048057 1250 690046807 690046829
    0x15060d06090207082703060a09020102150a200304030207180209150a0f020105090307031103070605160909090b31060b03010510060801060c14031c0f1104030b060303040f 75
    0x69661144200c500744103076448171404515800e00940440d440d20f40c010b04030b1240554030340200307095900034010b0084c0e078804810b01078090300c5e0040102004080d002c080d00b1000200715510441d0642c0070084a0245806400410a003450042500f4940074a01580c0004039000d00205100f51114007008101c840c00c42106c41d19005070b100f0081090103095207440071681001300340301c60410007004450040d41c0516146242c1c62580c0e001a1079441030400081c041c610302001c010b42d8121180e807140070400c41c2c0e0350b004e01d9590b80f08400820340300150f40c050003403481c1c4008141c8400c000000c504075000c0c0c244454004101891115000b9421100c2c2520b02584071100d032072480c036081c400c8070782c401040820380e0041405e0400090100105000d00310900ca8801074a005000c0a5003842d4164525881200d03500d0300304800d5204004900380311003036020305160001408280501450100b0b075801d080c41c50506156440b01c80b2a400c1c09000e464040c00304000c0400c2e0a502800303003070013520181041c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 690049307 1250 690048057 690048067
    0x15051902131703040e06040b01021c0c03080708040b0f18010c0306031205030412030c020109020904060e100e120306040b030d0c030801050402031003024e0615060d0609020708 77
    0x142c0e040a4042c08840c0b40740d410410091280007030032026503800c203100b03860004044100000603071078881409905484030f420800240c60040d40410f0700180640300782d072054282d072240c54041e036202d50203840003000200d140340000c00c035101c1c2d01d44207035003d0700c1091243d001c400005191070031900510848000643c0350401403060100900509100612034a0031030300c4c51400e41c88a0080701e6000005000b095202c040002c2010b2007504555141c50700282a000b090405240103c001c107203c1e5180c564500915030f424401c06940c0c8188080c160031800501030600e40f045002200b544014009075115994158800b0341e03031020804210b400411313450b50011a4018107010305260b81c140e1203103104600402c10080c100000900700e030100d0354166902030002d0140901ca60420700a0654034042901a8003402c1c0aa41e0800f02d0f154154041590380a001c0d980d851002d403070b22021991009540ca40380f2507009030303081540c010100d41c0f100910008925440d4a0508241c1e03000c90001d40c0c0400003c03131 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 690050557 1250 690049307 690049319
    0x1110309100b03030a050901050309030409061203030b010305093d0203061f0f0e01110a150b09100509061212090a050d0b150307090f02030403020607020a1505190213 73
    0xb1803070004550490055040c0720702c1d00c0c002452840b518000303070704005011011910820701082a10302602c0b501720180500d50703da112091000c1010001a00060300b0194602c40c1c0d07500030711031540a01c000c20054010380900d00c2c0300080e900300700c1ca0120030484500001d610207040d0320f02d0000310300704003203005a66820300a04001c8805005410300840d595003092503030700300381c00c0321252140210504080c010b40445c8001650304011540c3c10701c4803406201c1103c6c0c2007024000b0006e084111100301040b40000e00ca092154016003251000907034000d01d402071003286440035155501200003003605c2c1901d140c0c081a1400c2014420310894a00c0010034000d20b9485c26400000150409807985105861140c13110708401c81c1c0a00385403000c140d50720050060703460501403040544034444040c801c00d06149164070095000300d5080c0e005008100201e0441031011940da44201d400414148800300c842509070014940940b218540e03000b0480611407010150015203a28441031a00360342c0d1a02d005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 690051807 1250 690050557 690050561
    0xb04060506120708060a05070c0f050705030d090b030402040504020d020307090b0a060309031e0207090e03030a47120a051e0d11010e191203060b07030807020111030910 74
    0x40b103181c9260300f065000b480030040004903142c0c841141900440c690302c94a000341c03404035803074501501c2195901ea041d800d0090010f004000c9920607421554120b0100b1000c03207030402e00b03024a03180300e0000c00200700035241a030401c50f003250008040000304000c42d400a49400150f42c07241501e90340780c0e14060164549403007094010305007404d045c0100d0601d40d400a010306840c40402880c907502000401040d4803c000315005070514000070004911a0607995680e40c208640b0300e0b02031030400365449036140401c1d1480880300c2222106000c45500c807002095a4542800c650034003101c0c42c080310000b40d071000001c0020030041400741c13008400900f01182888150081c00c001c56000d0010004002070026002c0c0c41c160790f0f468041070450704100243e0140561700364001c81e038480d10f20304980c414842d6401c20b610350710034016022207106400f801d0f001d07102540f040440300e003400d000c01130101e80140c40b00c03540f1801c540700015411600c401451030b550002c0d10209016481143e802d00c2c440214 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 690053057 1250 690051807 690051829
    0xe0a020d231b0405070813230309090901060501020a021005120c0c1b030705010e06130603230103020108010302010827030c0d090e0c2b0903090923130b04060506 71
    0x83d0380500c80392038400e40183c4a000080e1020040c0c01c4c000007400c05200d4445030400c09143c03a07503c82c0c1422a9143d542541d6504121913180c8604181c102180c2c00a00511909046030810b80240095600d540c0811007200566003509060001c00c21402d4101c8581c89003061041b8000c04200343c4807040d800003985022401596a602e58640d4031a0a8655800054450031614240b03080d02d40380e1320884c0031441c1c0e401003801c00252a000208040b512a4054204403049062032210480322078200f290702c50019000e1002038042621040180f01552281c000244c0c0a81c0040c035015107e45251110400d50780503200c508890f40002c254100840018090042c9c005814a403500f01c00741021606440e400d0301400039a0540c10020300c10b500804113100941d581900c0085410351820305d1000c5501411480790200c000644244001c14100554841d070b90030800b00f0717880c14005400d1066042e00c19613014051480140d00384900100103a080d407031103403085224600201d814100102802200d42403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 690054307 1250 690053057 690053059
    0xb0622180506031f0e15060108063708030a090504150305030405060c01060f1806061b02130e01060303120605040504020105370203070b0108010e0a020d231b 69
    0x748000c2c88015500080c00809203401c01c40d50000c4100a51514801040840003440f01c0f8090341c01041c40740c00715210b03410310400702030300c2d410700e55a118000c0100c3e030f521044020214031404041000003480e102c0a00c01030030001c1c650340f81000d0b10741d0350b001e1440d08041404000039240400600090506004401e00c5005043c07510b40030904545c2d1f103d840c2c6c001d50242c06e0040e030b004a28251840025001100244608014805c1c81501d030351030640c1440388001120041d0b4100703040040ca80e8403601400000b24800035002c81030444540c200404044143d00c0701807880e88800003a07044080a104d803c0065209071660b000014a258010056911b2070303005c144030300d02c0c1400704000b40c0d80020813210204804c114002103c00d40e1100380d00e4180303c610007e034844203080101d03070426030004010400705010712100202f0b80e981c0d1031582d0030380300c1040d90103a10340c114004440041c1812040e10b408984204003410203061400c01446038141c5651120320581c1c031645109103d140740074480049800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 690055557 1250 690054307 690054311
    0x5270703021818070515030c07021906030b010e09061c080313050708030c0307030c051501090914060c04150201060b1912060e01051219060c0905010c020901090b062218 74
    0x2290030700144991b1000210010701080c000b0000b801c081c0071000711456260700810b00c51840703042c240003c3d10079501c0d000d56000300f860600d00c440b056000d90840c004951f00100103080d40d698030000d0100b81080702d007002003040e40d40840000025154401b86105002088540c0300c00c000d0b50a0042c03924070a40d000b107255810030080c8150880000c8210f41c0c115415003030004d600d81c40fa1034030a1070701f080b503100d6924401030f2070004200c1101c1900804142e50089582d400b41011080381a600c40c18191486d018520080008004880884014145120031030000103041569420815040d82c840703000d240c0221110001000910780091805528013103502c020403c6a06007a04041289030601130039200f60141181e401e01c10f5020800202141751000e1080250980e5103402805842e00380c2070358000c01d9802070049025480b5481040c10703160000c0407118264a0084070400400f4242c20300707908a03004100082c80c4407004401000300300a03101044a00c02d1425259800e00c090b05804007400d54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 690056807 1250 690055557 690055559
    0x1b090d11032509050c03070c14060a02031506090306061903020d050307170a0504050120030a0806030f0a051b030c12070e0106030204060c200d080d050a0527070302181807 75
    0x4a00d45c0540e1342c44011400c0000b50000da5041030281141561294120303441000d040104200c880d07000b42d4010701600200d4044641003404010f25030080620854156220900082d0380d860701460034281c00076802c0840c03020688030b07004505c4001c1030520603a4603500c0042d030001000280c10402d07100000c540100c5003004260000180107109611034541013204003e80d0f659400b070207003141e400c1d52200381c04a950f134030107041c0d000d401060112413051282c085c411400b424031780041000411292300401a0401481e1004201d020490001030281c0600c00d0780991580364460032480c0d0b440c0070429000300051860021910a2004140c012a0805006020412986401c54000700c80349622a9106e21003030960a00d200501d9404425a6800700d8040d040701c062080180017007460300301d0580c00780b03c182c1e00c00309044161081501c021464031a019050392104180f0200e00c6a004000700a0395591740c0d90342c001901c03815100401c0000d5a81c06014050017060300310201c1c0e56009040041e060507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 690058057 1250 690056807 690056821
    0x90f040506010b030a0f0204060e03010c0e031e01020408071707061b12170c0c062a0c0f01050f07020c0307080607200d09030b1b090d1103250905 64
    0x100c03010f2192034540a000320208491070f4041d00700d8807003401c2d030100464450b5624040103002580b960041400f9501e48003107811218400c44110031103c5025000f40480105020080b001010a00c810244c40d5820300c00826201c00c140712150013070560b40c00c081d9001014220039400c00e00c203a4403000503c00070700015000264010040b180c16a0494550604803040f403105803560080c0d8092140c1c0c5110b0082007050300e04600d00948207411001e811924a0fa07a0f0200d508040036a16902445200301c0521b5010403455110050546840da4020740e40c0400030b5840310b87c2550301c2a00c015098440d503e04218009904010061440108030010310050f803600d1107071a11500060700590802c50340c54104d1045116022108030840103083c22038510b0581284000d00c00076040c041281d10004071400f2a1030294400c084500b00040d500030303185000134110401c10074035501d1500321210700800116640b03a41e1b0030700840c100b0703a40281d056000e19890000201c00942650000d00d191480e00c4144140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 690059307 1250 690058057 690058063
    0xa09090c0e011d0a060f02150112080a14040e01090c0f0e0910080307120318050c1009050d05010f0b0105070803011419080f0c120a0605151003020306090f0405 70
    0x540c1030282481100c1c00318160040e14202c0c501d1600d19000301d100d0000258580d4000c50004c0c80502d140e081e180d94501c01440546010710070f03c5540711003481c152b0040003042c100c400500c008072150820703010300b500c0005160b0090700b044d800f6007000079244004000b400500d020700c80384080c81c4d2810400c19441c0f840081c20850b4091035550260b10101c0014a21040412051005d0400340080300d88620711031030203025021840290000080c24544003184241e6004403664015910502801c1c10b102c040042c0f201515030b80302d180003080311425000506032140100b40100d1030280001251540300d01c2e00b041e003559000300d019030400c10300b00400030208004c00c2c00d803415200e8200103440c00110030b0780090700382d412080007070703030000c0312000000b07103089001510b0502d0440000949000a07500c1041004100c0b24680d5a07105800185459000669540c407050b4803a805401001501550202141c04520760140660109034000300f8804140340c4145081e60100000c0e0380c00d002c500d0103558240d2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 690060557 1250 690059307 690059327
    0x705040f09031d12070308130608010308070b0720030c0607020c1e03070b03090717150106030e010f0e0102040f050d020d02210d031b300b04110a09090c 67
    0x3454200c0c0d00c0c1c0c9070440d5942550001d01c04c02e44400c4450080c2c1346c0c00d00c01203a52090b8459181c0c0702407200e00003441401100038504880e0010120340c10f01c90241c8407500480c07802002d000030480e0f80540340710079280c0308000020924501c4021078441b03400315544d1780340400250103d002d540c041180c1c94910381e02d00039001849480c210141242e10410030100c1e24151641d00305201444c40402000b586490002e8078504648010200d01d041009142000381c59040348807010900c07100c021b00511509009800c0341d090300c00d6100000443d0014941503008172511074090b00c031240d4001a04001b414004051320001d001c0c111407c1000c01029070000f203030600b00080080c05502580f000d40030228601121a6414858000740c03405503940000003401400850750354500e0b030303e403c8102081c00b40b18280d2581440881145820500c3c0c0340603226030000e14420300758031040d85410005401d501c0d60b0050b807108054000d07246d6102c0000380b00103002c2601540140c0006458801c605181c0c0b5480450f081d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 690061807 1250 690060557 690060587
    0xf0705120304030210050f0a1a151306091d070c0b0412110f0a110a0b0408011409030a02100e070803070b0709050d0f0206070206040909051c020a0c05300705040f0903 73
    0x14984007488e160180441d2742840c8654880510000d00c2d03000c141c014000c00800f200f2002400c1c40703645a40b8152082c50060064641209441c01d4041c0a0b20700e0044094002100c3d0614142222090f65202c000d0403044404541e07803c05682c030f403000d8a412501504c17042141001800c4140401041c543c5d07590040d02001e8000b038003901482141c0d0b1a90342400024002d0601480c0e501e90b110741025000e0311401902c1c140b0b01194400080c0481ea0100c00d64680d0700c140d03800780085040ca1802c403000303080a00301c450f126019142c400502020b04000820105109405006080c40c2c806c00191156050741d10050007000006002070004d50202450008a036044a460f9100c40070303400410110b01941d0041c05800e4039201001080c004006951440305084500c1402001e03181c1c10201c3e1070b2244580c004144460613103080c082c5103045540c84070007801036405040d880484410072340104141c0d0754504c01581041405204504050154000fa800519020b0040401d01d43d0006c26021035000c000e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 690063057 1250 690061807 690061811
    0x30213120311370c0e0103060b0a090501060c0b0711030c0c0f01020c0d06020315060f0c0c060f0a05071401050f191a0d020a0b180108060d0f02060f0705120304030210050f0a 76
    0x801004414442c130005407103d6604050070390303101d00d0a80d00400306a403c0511030242101c2c0098002c00c9405000e050712015600c4000b25041c50b540c80969500240400c02407080c0140350741c40e520405c0000d040f20740c054034000c1031400141020701618031403080c0340074115044400c201030a0b40715100d044c107481d035201000581e641d43d0f654001d800400f446540aa00481c000381811178038025102400014074014181c49214030b4132030400109100b1418401d100105c10310800c0c0c40c203800f5030702420354140a141c081e4411440404040e0031118126140b10402ca4142c0510891108184005010f100c3c0c02204200c8400074072211051211100030040c85410030b85411320854a4240c0c03040000d142a025880c2c45001804031080013085815180740050354000000e07240c0c0c503042071002038854200d944042044869000c0c0901a840002e0381d8480301410020040050000c0100b159845003c0c0c145c0c1d5124106850006d040448540d0140c1c000c03400c0600303000340301e98004286070300300c00342d4080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 690064307 1250 690063057 690063163
    0x7031e051605153f0f061807140f04032a0603020903160b0703020d050703021b060d0504060b010e0a0f030f0813030b15010c05060c0c01090503040803040807050102060c0307030213120311 82
    0x40710b100014212506104101251031100907810ac4060800d69114407840c0424000d2800c040c20002010140c500c100c502400f020000c9a0080e401031801e40e03000341c00d8541c80b0714610041804e0003d268010000c0341b900150010a0681c14020001e4141052034141d1608070141c80007540d030101038406031b940d060b42058817191542c4110031180507112460050285d450a4103010004000b440034003030100e00b00020342c030000d01c2d0000014050715001c5100010890541c3c454100c48083c0070070444401e0f0342048040444a0301105a2004502c180c1d440d12144c905820706009910300013000c00c5c144903840c003400001640124000707a04c01c025103034141c0c60302d08109200307014005a04000e813030b501000030041030748100880248255140c034001c9410542d0b41d2001240e546400f299004040101440480c200f80d00c20b40080060b0b01344030744040c1a05071100c140a01240c42e5420403004070301d0240d60086210402e200303002d10350120380c42070110443c22180b60b100820401d40d1f0400c5407501c1d224 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 690065557 1250 690064307 690064321
    0x329072c04050703090302010509030f07060b12100c0215090a060e1623030607020303010909060603021e040609050c09060304020307031e051605153f0f0618 69
    0x104240c84900040090010381003114000d402010050401d074019400d000c0021060980003045031810382240c2034040c5031a085441d000c00500d2150b8641c3d9201000d508102d241d00000c200e01d201c510009400000d50700c10904000c1d18284803800040019129082000b203040360108200f0a00d940204001c034803ca84940305904000750442034405000300c080020944d04035269003c1c1c1c92280d0300390307081b190751442401c150780c42d0300444444c00147c1c4200014019900742e5042074541900ca4000810015140d60008036150a0424800c0c0c3c0034281d00111140c41c909805894020225040104000d080a481e020b403584914075685009620001c04a021500c08001c81c0000303640004080c54100c20b1004428001c0054210589840c0b2030031010f08890445004c0038011920010a0314402024082d032114603030708003d004064050401d00d42e000340c03620000c115000c0c040c0e0038041c402400c0e01010303e080c4074000034000390351741150001005102e4861100f05420318000c400800310f555280d0b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 690066807 1250 690065557 690065627
    0x504030803090c0405090c031e06062407060f05250f1206090219020303010501080610030e0d050408070609032d05010c17090c010e1e03010204032907 66
    0x800f00340d0014031701404c01c0402003001c500c0e0410002d080b01078507144ca080715801e800c02c80b018454150140c00c52404140185002d004810042c5c424001900f101d003525492558940c10070701080e5000e0b51120380c6d202d5003510602c1041d031b2000d04a0541c4021030454000003241d52800d907003080502860801c0300030030501581611b1142100144c0a00c551515048800d002c1e410443c4d80e5201c11171a61155003500380084180d80c1a02c8043c4d6580c2d00e03d23500d07070302040684006040c81301c050542e11491250504401e000042c1461402c2c0c8540c0d030b80d0351400340c0e02490804298485002c00042d02c00520015020f0f41710903c15150f100c442c0d082307001c19100e5541a4030107003040200590700e005005120641c01542e8080e400d051032400e00015a284568592a2500700095500060350040032655500e440d403001d1822000a2480a410754444000700f404c90703001e80c0040d240b0000e00e0744800c02000064550703111f0900108030985650030600c501030600d9840100c0c402d11002100c04122040481c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 690068057 1250 690066807 690066823
    0x50a0807180326040b1210180902010c0b0901150801060e01052103040f0f05060c1e0c0301140105040e010b0d030c1505010e0603060604020a0e010818070e25050403080309 75
    0xb4600070750303110361780ea29070602c56019100d00d2003003042850010300585425074180b41200c22030410040c0402490840c1d02c01030441c203100300c0c10701582400c0741c3c01003109140003e100345880d20001807021421250382c2c0307001040c0c0e4010f090071782c10044184400507040054904403281524100310503003108030401030040d0f400c02003000a200c0840c001803401d5004000c201281c41ca00466a071036a207800c1030005500c036021500d68580c0c0300a03c609804045c03600c0c180955100714042c2c4100d40104000079082d5400250307030f4005040e41d14014483c0345131070300c40c12520502e840c00801030b400414022590222480074042d00384140301e00b001040c8000c0c500c140e0340c40421510704001c95a107a00c5a0802e40100b84c40c9903010744244400682181058422502007070119260324020744038040044810400003840052401c0035441000d03450307441001075001410130070342c141503c4d00c0d020711071410201100480b070803020f03181134001c68a6074101044a0903690043d600940d650f82d8215803600e00070f44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 690069307 1250 690068057 690068123
    0x50d05040816050d18050a0b071403040f03060e010b0d0b040609050d0302071b0e061504030501020d02070516060816030b0d060e21030606070f05010507050a08071803 73
    0x259a4050300300a001300e050319000e60b182c0c44a13006881400074000f41c204180c050941c0145684009100609101010b04072a0f84200d50486140020794030321800d581180e03215201c3c00352028020f00401000d8090641e00c1c05182c2e000700300d40b03090100060201a142d0002809103206c0340089404d228480e00451b01c0140c2000484807100c4200c10020b00a500c0301c101a2100c0d440064250201c01d59180c603007045448180100c0603a0711030708100f14502d14003c400080d4990100300000000d07070207001820600740f45440068a0b00c89900b801800d006040429401d5103640e640140540368000314655001400904c1150a019901b0025401004001c86031640039a19440c0daa0400600340c00502c0d4884440055440034a409070391b0560301092043c1c0300c140e282c020300018049041010241c807889010b0a18041c07100180d480e00b87c00c403003060307030036200051000464005441d045403196400500070700d04800c104410440a601c1c0b0411800020030540c81e020740049500d41003002851440b40c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 690070557 1250 690069307 690069337
    0x6050313080c0703030f0815090a06030b040602130f08030706020306040e1e07090b010801120501230f060609030c09040c05060d02030a1401051305040f06061508010801020a050d050408 81
    0x2520600381c0f5681c0c2d00ca480101c002030040c041801c0d40a100791501c0d4010000407a00e000c00c010b02e40104005450002e1502c02e0f0156281c0380000454103040d511801207001c5c050059440e80c4415550094240702c0d00440f1012007001c0040007090000400c4454940c1c0003a001031316070300d410740054041c201d9206410194480e6060b0104202100c103000e4440304528011203048603a102d50792820742d0a40e1000a000c030310410300400404e0080440301120303030320400000481404101015003500a8400048800c2050501f0001c1c103101a0b881d035030f0000c07400c039001404e1a1107400041d80d43e0020203c014060b60b1100c001c10304104030080e182010f0000242525152612210020020740003182d4001c0e01c0ca0070010b400748640b05100345681a41d40c081d1401406a418004110103000c01500803540101c0c850940c0011814030b00c640c60203800451208044034210382c1b03004000e028183c010912507441003240142250300b140417a0a01c4c132001d0070210b01039445090a006601174503e0b00d9918030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 690071807 1250 690070557 690070567
    0x6141207030f0e0115050d0804080f030403061401030c141302030702010c0305010e0103030816091806080609011a0d03050706050f1f0b040303031127010210020903070605031308 78
    0x40d4040c1c0081c107182e00c514000b0855840c10215040c00c1e00c000c0046058414104c1c5010b0021303003012a24074440e20300500c42549056501c0d44c01e02d19040000c681848590001b08041c42084000d029a802d4501860b0340328809504580b03030f400b14070396039100c1c405040303a103549694950b407100d0300d18404118940c58211340741e180c180e20190280102d182c2c0d01c1c0010b0f141c0302c0049030000c80e02030840d042e84d8040c0c1d035042565440d628440c1009480f170185105111580a00180c580ca400000c0303509180142c1c8045940c5140000072498048050500a5282d05018030a001c90720261003e002c141000c86411400c00c0c07403800e007901d1603c600e41028010301c0c10102000203000c0c540d4505400390f26000d0566985102038101841c1450440c0501004d440c410001000403030700caa040850524005103940d40350400c43e91008204000f013000c6190f10042229849406680501004001c52000325040d46060035280000b030b110740140c0511014080d000c030201e8035203407a03244144001540514445c0c0d0310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 690073057 1250 690071807 690071821
    0xb030708070f0803190e010512040c030311060708040201050d020418020301032f010305270f0c03030f120a02070803040f0b0c2d09100e0901080313061412 68
    0x60300040c0901642c1481c00d10000480c1c03100001140d00c9040319000c9103801680501c011160101d4a42c016070400a0500c901c000b0340350001107050107103100c4d1402080c00c518618000c1d00180d41c00714602e40c0c5030014000c021403150800c0c01c0030b40c03040d82482c0c8140d031128040c02140c001d0059411503540044060b0300b81880d201e45900650613a8040d144610040c2110030302d505110260f41081190003011900100340b6502079040540c1040c074803401e0a0122510000d4941c07081081680350401ea0300c0180704134100c0d00207002c0031103c01c600350083c0d07140c4800741c402080c4030b20403a11780040005040001450320701d815030503550b02d03a902445560b900e08040c181a441d060081109844482c400c102240c0c40000c04000c495003580404003501003942c4042030404040814107851131184401c0204850369a0384207080300c005400c0d41c403503072034803200d4206000703d8050580281e4040d40c030400062041c0351078110004116621032508801c4850070402e10300c013600485804c46950710480090201c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 690074307 1250 690073057 690073063
    0x140415020307021207080718060e0c030411040c050f0d06120807050c06070f080306030106090f020d05010803070302060c250303020304020f19121b030b04170f0a050a02010b030708 79
    0x80b0364001c40d41801482c0d114010750707407198072612035101da59101c8801041800b68036080601210b880346800240d0990700d958013000280100d521500c511000410007080000010088400c110142ca04014203400640c001c0c0c081d104d20106004551000305110680d0601c0b0b030841d0300600024203104107100d1403450400000c1d081700c07170101c03018011200d0401d0701c4d0816400f65600340b508681c0140000c1855140c00c0041d03400035040d0f0350155256800400c10300b000e0f015500703090001682c01643c48000c40b009404803901a003146425800400c080303004a540040c1c0e258212010f428102d60350040c00740c560070b1443da186001801265010045e40c01e1641503400b5500c254000d0f540c1c8140b803180c010402414910304584c0e0700f82e0402403001404002210501d03002d00d60f1282c80802200c1581603c0001c08028980c0105d4144481c00200010000104c6114946450040c401400d2038180038050303981d8055a03589208114000c140f0a004030b1003500f0038010030300e015043e125025182c89145403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 690075557 1250 690074307 690074317
    0x9110c070e0609010602060c0a050d0207021818060112020622080304240f0e0102011503060b04060e1302041e15080606010504060813020f1005040e130b04031404150203 74
    0x200c2443d0100002a0981c004a1054806c03901e42c0b080030f1030450318039002e680315000650800d890ba5402d101c2c40d0016250110324034070070680c07a6419415071078002c00d03511824002c02d940c0000390304500e004102007086001c650110550482e08a51503005060b482c920300441c0c42c1ca0004400c00c50f9500080d942800300080c000d4900c5000984112500c02080c81485000000e403180020f15029510409620072000b00303c0100051002140c2503a03042c03179101c00780b900c3d600709960075642c4031010b41c0c5514182c411000282043d035494403491800d0b03e00040203c218000c040d00585d240c03444450845280038503603845180c441000c10045071041c0d2980201091070040300c00300e1007103e020440c04e40c001e5081d41e00b16203407580c070703503645540300fa0821003825a840c404981045451802440320713600d820400381e41c007915a55240c1c44070320b843c440500540c00034000308203640e0b80700100000b00d03001110107035002da00350400d0070030180c0000481c5500d11841c1d000203c48400c004a42900e40ea01200400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 690076807 1250 690075557 690075559
    0xa0b1801060e241b0c0607050c040c020c130c0e04110706060506030c0d2415022a1e040509240c04060f021501090207230709110c070e06 60
    0x1c42000200285480618400c407044103020340e0500451a5000d400ca442c3c6092800d244d003900d40800d05980800d001740c03c1a542110740d6000103144940d036092602c244042e182c0c84d8401407a48212010124183c1074408400c0d118203921003011641d458002c60344a4404c41014008224900c072070040d8180c603400c0440d0445100c0d0800c40b000030140f8010040c3c90042d005980d4082c40c0c004801c180750020007800741f540c03002210500805002201d0f040040004000c040305401320702015410003410900c0040c00341c50820b0b0048145100c580c1950f19405803040c0a454107241c00d040d61030000c10701215000c000c0e0b40302d03060500304424440081000702c0d6155090448581c0180000701c0c10310224021070361361010410500c4100b0690780b00380c0e20001c00c82050b005072008184600361100c1d100000342c0280d000c00e0740000322541048400c00d035841040382d05074100c01d0114840440e0310b454441070701c02d00c1b0405803a01200c030f009001c903000f11440d40e25503c080b551080c0d500d0f8403c00120700111452 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 690078057 1250 690076807 690076819
    0x40b0703020f0607210608100902190f030309060504030c14031603060c020d020a0209061c060614130b0102070e0c0903061e090a03140d06181a010509090a0b1801060e 73
    0x105e146524003928080d02d40d1341f0050400c40c81e007001c3c02001042d040c0d42c00e030b070f0083d2441421195419202d000002908103510544103a07400c60401914402060b440f050030007000b0401080072481d5401810f0591348034034010409045243e00180c6040c0f0000e102d0b240c1440003e00000c2000100d501c100da0a201e0354098034108217080c9816a26601c581402940000f07019002408619103400d000c2031801141184601c95a455203e4600321151904040524110500080040d1519004219401d0900402802084000b4000030749420251040d405002c00a1000c07803412200e00c01a1354059402808031540e6180a01c0e80154002c44401c00200d228110008551121404901c00040c41d03019202c0c588010170a941c1e11075242d0210310748500c044d07510003010943ca54024040d2401c42e01c00300021076014000d203800c91006000d50701c1030b418094100f0401c55507171a190301d40c9522540c1b0308000200d0011101c00f26004000403081c0a401250b07840000c01c10f142c1002d0200750074030050b119 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 690079307 1250 690078057 690078107
    0x8010c09030b10120f08040b0318060f0405032d070b04060b010503010506040e0a1e0e1e0c01031a0d051612020a030618061a040e06010b040b0703020f0607 68
    0x400c03484903456009203411130490545080100f400d01c0503c12210b80b00c1c014692901d90303920480d48280d0810303207804180025402111840e0001000107079008051007151600a082c1940d409940388100c3c00d2207500840c621202800c0400c1c2c92115003445858007142c6640c4661070f11700081035050403a000c4941c1890241c1103041c6501c60741c1620b0503201c3c09044180740c5414101d0b4140510170082a013040c0c15210355100704808140c3d010540703807401d500b00104401d45004c0405041016505c030713440d60b581c1c0711701c4201c038122000524107500660a080010307015030305000f0407101d87d588140346c41d00413100c2030040e0108030780058094a100c40703450700c1903440d07603d41d490000b0141e40171401940c0800c00030401e10214095500030441224008485035203c3e40c1c50307451500355020038070010034a41c14220200694140790103004441501c51020b004203604268403008036021b540200356800b40080f840008160080105008401c41d07441200c4444c504140010240500c200c01c03141c1c402c0003250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 690080557 1250 690079307 690079321
    0x3030415021009021c08090414040639050408060708100902161509020d05100c050403020901270e100b0103021602120a0b13050105011a040315020408010c09030b 71
    0x81412200c0c2c1e03000707088401c600241140d000c010407682c41c046c0c130000c0040190441994a601c50a4001341489021038071a1402d41400c0c002c403000000e6940c00e546503140200c08006101803d04110070b04540343c1e8059401a0000701c0d843e014541259095110b031805120701a074000d0488c44c45a40e203c00c52007042c680b2441d05405034040c0000809141c2080303000b43d00040c44102d420040c010071150005080802c58001030469080814151950b402c5080c00c2e140d120170030b0142114242e01d50030043e20f01861540412a0707040140302e1340f00c1150f190744066506104084280c1400ca01b9074005001c0c040c00b06c00019260710351640640b04003803074102500b040394040e0003520100030b8400b00c9812007000c43d400340b241c42412000780344110301405a040c8005801451918013501d03e80d00903448054144ca0403070308480c0103070030140a4255081c01c0741c0020348420105e40c10307aa4055800000f10780c03443d88032800b034015604003c0c0300d942040110702c0c030f00d5400342400301182d000742009081d54640c25 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 690081807 1250 690080557 690080561
    0x7150605060a0503010b09062a0d091406031e0406060623180109080a060204030b0f010f1401090509011404050109020f04120f0b040812150906091005030304150210 72
    0x28840742c00b05400740700401005003070f00c029080d803400143c1250310b080304140c0854100e10f0805001d07505146044000c20b00040200095458060981441d580460420121800d49104443c51030701c90b0310000001480f4410115080d83c60f8100e002140220b400c0901d0a030026142034060326000580090161017019113a00143d480c40c19a0306e46141b401c13a504030340d10403003039035041004d041c003100d082c001421b020108920b000c094040d01005884034190315200c0c80014000c3d09140210782010018003011501045190413030781e050310f6181601031f8580044c4d54014640e4012036000c11994000500488085008081d1000c221400c20030350f078071694160200d024084640c011000144000d20807440700700112032640e800b0316a1440c0c250400d6440103286072045038119107a01010814a400001c1481400d41010b003046400ca894602e500101e010900c00920341313449084100082000800c0168002e4041c000207010760707907199222140f600c1407003000c083c081c1c010310990740044820b60720740c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 690083057 1250 690081807 690081817
    0x1150302070804050904030c02060a09090b043e030a06052e18180903110a08120402240307020c0f0913150f0b0414040308011a0705030715060506 64
    0x28142c1800c060030801032043c01c0400800460038414807010b52000751342c820000d0080800c00340c0c0d4001a15082c0341e00c44040c1c0d5910f092079070103141003c40c4005501c10309007280200c0d40d0154100850124100c004c0e0320545844540e1050581d0004207001c01000942c2205003070329000c4c2c0b020320403036522202c00c050201a40042e50b440704a00000140c0a40c0304141c45501c101c00c050181c00300540318030803c22405142102500042d903912248000c054000503003407400101800606034600e01501c41c402e242c80360700b440c01c80c040101070025046507941c2c2025580c1d82484210121924180114816180d00c250348150252080007601d188a10f0010038100820401a00201043e102c02007502c051078064942154203040380b40c400180011103105008540c1c6070000d011031102141c009202c116401540714a03c0040c001040001194218291904551f002c2c1d0f101540720442c041244590700404c0b2000388140000a01c41040c801002c8800344004c000150402005076984104030720ba2240c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 690084307 1250 690083057 690083063
    0x50f041d160c1a0a0e07080a02030c220209060f070c05040f020f0405090a020c0f0606010810050916030b0310020301030605010e011a130e01061805011407020f21060115030207 77
    0x81d1001444190b0703589003d0b58008101c0d01c0301044e08260303030506508082258204039466400030200906500d070801c164666594182c801550380c001e03051041000c020704818041305903400184841c051749540003216800158140c05030303180c0000d450007103103a054501c1a64455824100700c1c0c00a40214421601c02e1110450708510b000d03d0f000a0060f000f00050040020755420701402070000c205019414409008501800c400e182000000d0310100028009038810204050140243e486880201c1c0c0c000d08500c1041350303000ca40641c210054618440e440c1c4d05809200e07048404050160083e5050f00c0c810b94050005a88038012610050403d20440701c4608203000426041e8119a000344400d440d01d000720520907443e48908a0320302000c0c6d10410005e121541c5802c1501c16a45c0100b014280920f0881d52403410403014241c00c0c050000040d10030721030445102003998407820300c500c3c80b00e43c0e41c82240d55481c144503401c2c0c03500001d12424801011103040c010304076110740300306d03500e05078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 690085557 1250 690084307 690084323
    0x606090a0603050606130b1207090e0f040c030c080d110307050c010507151404060f11041802280909060614090f040e0115060519050f041d160c 63
    0x110309072003100545005004c00303400100c00c0108042c0d0307400c0d04e007000d0094200041d000c0c0d41e40d11519002619002c1c020311140410049010071300c104c018244559421155130f4103014042c1e00c0c0d80c109119030100360f074002890201c001000268106001c41e9402c114040c50b12025500c0c00109419901ca00c14400020200e4010019480140d0300407400742c103a0354001c030315100001c03825104039001c03101c0c05440341f985850060100b00802074540620110842d40c1c100921010840b407070b0b440715a0040d40102d610486090400000040140d810344104000022141901d00d01c0900c0001030000b002515900180840802007014440d80c0502e07400c40b802d0307940e42c4110320800b0b4901040c940018842e2b90340005080401410b580d980d0144081e50168030000040308080482880e2407800286e1205050010a00885041d0212140d41d2311707000500f401c28558070903282c4588140c0c0c1c410f41c1c01c650760044100c1c0005002c401c0d41c40c0960301c0740000020891200328544400e83d010f0700c4012004218031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 690086807 1250 690085557 690085559
    0x51009061d09120706060504180c0306020906161a0f160e0109031b051f0203070204020a021c03020a030513050c010f030627051303121e02070602030f0606090a 70
    0x2003a444466032020150b4240d89805050102407a0180e20003c000d40b109034841c00c0a004905c0c0c141315583c400364402c4688000920140e4402019410303e100140420f98045111000c039280c1c1c8003107820200461f4101c100c6094546021060032010080030104113141200041940c0c074003c1010340544e1000001800328100424110741e0400030031040c50400c4030b0b841002001030400c14021010500c0410b442c5102806c10f024400c00c0d5540c41d004800c1c990724030218043c69600401212019034054402507900c00a428060386400010030800c130510400241101c03005525502801d80700e0999502482161101520b690600901040c003030310f25002505841525801032080d581c05060301d08000c94410358a0319584441c0c00058540c0b948400020451102e0362044c0c419070340c0c060b207110100e11094503a030f1001440002d40704480c1803410354800140851103800da81d5003800180310002507540740401d142c002d02940060300c0d1000004408000300e400c0340341280984008604c094401248a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 690088057 1250 690086807 690086849
    0x1020a0206091b091f0905070f020d020106050612130f030203030a0b01031e050709050310061703040b0f0c0a02100e010e1f05160f0c0501090b0301140d02040e06090105100906 77
    0x10700040031704145094211100015146440c0c0109840746c1c00a4440e0f041802d904a0042e0408441001c4842107902d061030600c015076410060714000d101c0c541170481c166031540b002070004000c2030805004200c0c8002c000741050750002c0118031130080d080c002c2c408020741e000194240c81240039002c80c028803560350f082c00304002d5400a94003012506c0c1684201d80c1d1080806c1c10001c10b103910881c0103880e1201400b032039148440007010b042020004500d40b0b4603240401e61107000350b0781d00480c0510002865130500c07504000c59610590000c140e948070400400010702000e40008420340801e13000305801c803030351820181e10030003040401c00d00d0b8505004071404680d141d01078000e04440d5003104c85440081000c0002c0401210312a070fa01d4900c40c3d06003170000d0601c00781c40d88806c00c1e0290810043c0a9220882d10480c0c502800751036200c1d400390b89100007806403510040d1180d6a2003071404000c4401c005401403402465240d036840340d065101d02d0341005a0300039008106426042c1a29412a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 690089307 1250 690088057 690088081
    0x1030203071a1204030e041401051e0619030504120809250f0b0d1113030602030c04091a0f060c1509210c0d0e010c121101020a0206091b09 61
    0x914040702d0200e078644042d2030030f003038003107a0b081d00d0640000354103a200c800e25003042d22501c4c044401801e824405589000c0000b58580d03024120205080c10114040b41a81c4580042d529004551a0000202000018002c00400b402c8034152840e01c000740460244234080ca00d031030b01404005024080300001426802202d513862000c0a032040c40f143d900103103180c100401c0b0009050034a08139503480027450000010381d400540e00701107191040040030240b4200c444010101da610034809622030341d8079050741a042c0141d50040062606081c1094051802002c00d150250401c0310390200c06500d10040c000980940c120507402540000c2c081c1d9156202400c4083d40426080121507070103007048900f04500c0b070381003000d01181d40049241e030070019003403110806e60026807600381301d9000800c00007409480f03502800f070016071000c40c02201140c85030150f666208510030080d0350310b0440c05002540c80004039810300250082140c0035400d103080d189a02c1c402000140203060310340b02c001040700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 690090557 1250 690089307 690089339
    0x2101713020604090c11010b18040b04060b120115230f041b121a01090303080703060f080d02330a0207060614121606140f070602030714030103020307 66
    0x6070002c01400f000900c510a801072801c00c004903501d10300511011103009082d641c2c001103035803103158040c14050341c444864503845e030b02a070041d00390385035621141000b000801c030345541c0b943c0044035030703074001d5609134150040944200c544000c1d0321000c1e43d40702c0700c3e4030180c00014621001020ba030920300c050b2400c0e48048076054801030002400f21103104400d06049441d4800348041407107070a81c00b000f00560321484030b8148022002807100800400003c0428406010007418030040360041240980b003a4402c0001c1d10300150840d080039100c0d01080d03030304d000c0c40140d00014400c0315140c81c100e84085298214688140c580040d2440e01e020f07504005403001051319460b01ea0a20451b004503070310340180f40c003c01103105030f03400e81400c030400e000c0080d5041d9914600303680044a5030340207582c42c07141d40f0f04442151910388a074090322400c0a440d031256150070940c1800c04501101404541e500440c0509000e460302403c0c8420314404800a000910029515070000c080412000e040106103070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 690091807 1250 690090557 690090559
    0xc05152203050c1015060503091504030c0b0106110d020a08040303050a0c0b0c07020a121a0601090b0316030605010212031315090b062d0f0103061d040210171302 71
    0x6040c094858000c41c60580d90744c1110b03c03529190115400c01c8024080821701405403460700926501c1e106101540d03890104072030b281300c1c400950001d010302d031044885680895200c1080007055075100401004500c20f0310f00f00849018502c282c0c40e40900005044065036403100107181031a280d52816a40c6400411466080c41503610060000400c0c030501d2a00c07907140072000340c0e2a40454018010100c03200c0c2c00c0a0324105c10109820003295810804180e8101555003460a60780c500004a640307a02c15407204c44a10404003e001004941008088140d035040c2e600300241c40c0c1d00c0703004981c2c4460a03c82040454001c0002c56030b184001500e0303d05440c0501c43c2c14403166041480e060846404180a80701a8040030502c0620710b840440c4a40c040c11076081c5554440e0010101d05c08003040d80d443c1441602004070700c031001d9000707030010001003402c400e02a5103000c0c0016684900781013100d04921455501b04a04220f500900700c04071304030303000704008100359144401041842c0c03d420043e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 690093057 1250 690091807 690091817
    0x1210090501020c160e0f0403170a020f070c030212031318020f0403110f040218010c111c05060a0203010e06060d0f1118040207020d0312140103030c05152203 69
    0x8000c000e00c200244c403200d0074104602e0820b60701d407141510b03606101800081c400780d0140148004690300040c1c80c040d2401c1c21144a49c07503201d9100210082c811070280f650306001c0440d10340280517803c22074404807402511400c0301027240c601026200c1c450020000c6002010280512040e01d0080c2c10350310503100542d0040c948504404407001e0351300144c3c42220380328810722001300c1030b00300340004400740b2070103403030030360800030101c2400c050401c0d8901c0d8070b410031942d01940000d0190000c0558050900640741001440c2005c0305603440040071f55040c0c4861190342d0100da0084840c2c4200d9040f10607080300c01c00705449881c20000a0b82c88071b8022200783d601e5904180e071200c0c1d603114240380c40003580b10381c555800c55101280c80208007100f00b54407540c41406594090786480300c4460f00c244c0d2515050441ca10381013240c0005142142c1c5403100008600004000c040d04035020204d450700800413559a0120319255801c0560704840900001c04041d001c110310030398401000c0b07055403081c201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 690094307 1250 690093057 690093067
    0x1914030c1c021207061a0301050610050a21060806150603040b0712050f07021002040803040b160807032001051003110402071e020a050126060604052d121009050102 72
    0x201d0043c40e0030080c4150703281c50740e89080c4c1c800000101300b16905182d01340c0c003e01040c501a000140103000a41c1200144800095940b20282c8540c40001102040e6034095840441030110b0400500711406804d00d03521405000c61886e1404030307046d00039028003d06c1703113142d560765540d05051040c015000c0c00902c04510070180c503512050003601d200b519018101c9145142c5690024070b4513008003481c1c5002c502c1000b00b4010260040221800e48401d516174030fa135408901e80d400c07511610144003400d8a6808500041003552002c4c000030312998900703209114014100c8440d08940050742c002022400c1c001d820800148990950458a800100014140f841a48a110380d0031414404004002140d840e600110702d0540240400b80c0401c0c80e2040503480389000c4000c2b9100010f0801e9404060100082c0081d600d40007128058680a80000c036803032910040d825043c400550b00c1c81d21a01c0e004d0800c070302c034201401d008a08100e9140148004d5040303010202c01804100400d484d15502000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 690095557 1250 690094307 690094333
    0x60f061e1503060e1509060d150507020c492406080f1501060503010e06030a06060b0d0501050f0a03020622030c0602010e1209010f09081914030c1c02 66
    0x25013070b4411804000140c0310307641c08604100c000c010040201d0301c54075508040b400865030f40100003107d2406481c0c006500c1d200c0000a82c9062075003440c81741c1c40040c010703c6c088641c001040e1002d0180da84891182c0e03801345c480c01d4013200c194104003103207044401c01c0440042030340080c043c90300c1203c08021001d002c402c240488103540b0a40c01c10a00e0f40d012400c0c1450394101081503e60140807421400f2040d41080c1004140e440f041c4100d0007000548008101181d03024080e00c681c06910000400071181e990b0070f07401c05900444e22001c43c603440d180001846060400c00d403540c5030802848200c2c083c0c00c641c01c1110a401100002c02a4001c0000c12034801c0f005141e12000b540c002c2d18440b98107413030300794000c1c29030707011040318400c94001000c0e02c22404078010070f40f1282c05090030b101141c0d40959070110b07159a0359900c890081d1140e410704201b8400581d28079401e0760f0140a0400550450041155491040c05200d0180d5800102d00b01c2202c140310b841c20300464100d206440d0000c103018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 690096807 1250 690095557 690095579
    0x30e010513051e09010812040e04050f0a0c080c120d0c06020702032d03090a06050307020a1218060201050c12130f150e0109020a27020403060f061e150306 68
    0x26951540c03800032490502c40f1443c26850903401480c403840180002031800d0110110350149100e1452500ca0760b40110f000c0000520074119824500002c48448041c6c0c0e0500c0303610030019100f0003119004c0c0c4007150f81c2c2030401900300c91103030500314003c0240040b4040101c9490619035010390700154244421070069900b0303c042d01441600000720441414940b024003034000845141652645c0108210002c6071101940002200c04a042c5a51255160b00040c0c0c04c00140c004014400440390642c0c840e0740e0341090840d124a65074101800c405600e641040e400c9420a40b401a4400d03c2886500441c0d0001c0c2d4500d07034480d000310780c200100b480311341c2c178403600328521542158881c00c0c2041c405000d40143c0f00b100003c90907500244116031641d00810070144a5004000c5801200340000d81500c41d02c00d020412202000002c540d01d99913030602c0c000030701040d031541140500740b12001400c81d181c3d03652035045d4510301a1300d000030341c0340c020304000c45040700c5568070a044d241c24000547c40c0d494 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 690098057 1250 690096807 690096829
    0x1091a040201020105010611060a110c0604050703030807030908030615041517250e012a0204200d090201120609020c010b040204080a0f020a05030d0f0305060607030e01051305 77
    0x41800025181454400a825214160002d404115501d40d880f041c080c4000b81d03c0707801c012410000194a1062840703c0340600c11541800e070544503c6042c0003c20100007034910803680644c0d41c1f860300d0741741c2510480c192071030100d01604000e003c0c00807030241d290a280c030341010421101e04ca4640399544200303110810000118002180c0d040c14070710a048050301003a0341c00407003891850f04000e0804600c07070782c181008100e50304100d5512035181c2e60b640105600c4c885203c11021108002d900c485085114000340e01c2c1c120300541c01c21031504041100c90140100b00000402c880703041180c212402130090850300e0050381081455015454141c800388103440280c000d410f0090b079030720942000182503c0d0041005c03402a031040108104a01c004200352000c01d6000d141840102410f0002030b901850a0704056418098544d07441d401640010a080b01c2080c0d0351000c2c042550760004114803401180b001038045030b2000341c00c4000d0340c410001410b00400d01104d417480340703480c0c1c00411401524 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 690099307 1250 690098057 690098093
    0x121f060203030106030605031f0b240403021201140c03090a0c06052106010905133209010c0903032001060315270b0402060403120320090117090109 65
    0x1c000010700c8103d6250089102401094000f0100c880101c4649003500c130301041002d503490b550f10b2203802c0310f940d0b110007240c40102e011154421080614001e00c000d50043c03104070302c14524020542c1820b241030080e4001c80c648035011540356610081142d40c1c03580000d22400c1180203042212000454212010003e01507903600c590300c5503901e10101011111981c0403038901148032081054587e0f101c244e80b01555030584400f00ba00c4511307901c00c40a0308451000300320030b0040440b00c1c1c040c1e42928030320100041c3c0f0540042125121484000c7c02c0300c3d1b1028107031000901d810f50900109000c0e07a00c841c1d0070903441e00362048444505c1d10032402c40e25944c00490b107108143c0b40d0107142029a0241804414083e54200c4107682d010f9007014a0f03042500c1c3c014021402100000e040d076448209643c021500001c1d442076070052160001c00410f00403144864021250081043d514070b03200c25a0321050041c1c40c0c4000424003c5003c2e141520b00500c50042c5640312020755000440c0034011042c883d81c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 690100557 1250 690099307 690099313
    0x3090a0b0108011b03110405130b01080c0301150e01090503010c0c0201141204023a15021809090f0a0b010311060705121809010e09150c121f0602 64
    0x88600e040342454606038400d00a5a0601c4810003c0d04079440c0c2400da40b600c2400c0014110044441000c00c81c000c590020f94040e003800400513085040d9040f46003401c000341e03960040b03a5652a10500c0c0741c00300f80100040003100d901480c09181c092044440e9100050400010740c2ea5644002425244140c00c40e900080c550100e600c00c550b040781504555114803020316080000010b03060704021002000a03204910032400749600d00c40394540e040d6035500400c840c0c1c07200c91200c0d00030b01c42c9103103440c130880d205403010300b089501220a02c250b0308807080741e12600c1d0f00f80c0f00d03210400100240c060030301c00d41405150103014564a0070041c50645a1003807510503003039031440c100303092a40303902d00d4420f001d080200500c40000700d0100d003003101e110f441480c00303840e24462007080c18200b031a0417126410514110001c40d008044000707251040100f58110f9144226003070794101002c109403028034101e030f01880b6035040d805600c81400e42c0210900d09003040b007440c100c40c2a130004403581c0b140c40960 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 690101807 1250 690100557 690100573
    0x602120108030a110601051507080403080c0708100203070813050705090a0b24220509012303280611030f0405190f0803070507020301060810060e0603100c140309 71
    0x164025039001c4c02200f84e0405000c582d8500400b082e210680302210f02e001000006a40042040c00300544005d190082c1c00719032220354000c030f02980d6151500031603645106406c2c00300c00c000351310300889100d02d0301a96420030545076030002d80781c49004107800315018010104081507039181e4000091151100745008603814007a441403218110300000d18030040380180c155010b1804040040b03e0341c01114001c00c0030440800c40741014404030b076812003540529000000a4191340411140240b121305c0e5000c0d2035045104400c040d074504450041c070304183c141400249855800d003203144d074158040c4c24045007070100e01c401980542d10841d401d01d10644880140400d114080101070781c801d8110301c1020009100d40c699020404130214001c0840c1400000145110b114205847d021a03014000f0701c07a403510340c1c5000f602c07400d2008010f4803040c84c0c00000203840048109103400b81101402510401d42c0b540b440001915184014006218180a9100c4c100c20f10800031446001740c02c01400c461 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 690103057 1250 690101807 690101827
    0x807140601060e0d0b01050603041a1005040c0f020a080d1103010e010e06091b030a0b06030a09120c17030c22091a010503070c02120109060e06180a0f060212010803 72
    0x9020110f5580d80038074a075909240020710407001d0181500e104a4000c4d490b50ba83d840e1200c403a80118480d00d03106902d400c28080e0300040c044e103101c2030302e00071039041c007003030151030030489d6114041d15000e001603000f89444008954098000d0048000d822000300b0322051410401515500030b0744002d001c0340f050710041101100081c0c40d0354104c00c0031036601020381094801c0c580580000d000f20204020000081809800b013a80036000480018024680764a803844080c40101641c59003a9080d145000c0e0311505a446060b500c100030b50b01800039007041d0480c2c0f0180d40b8941004254803520340c0100182048185d44140b60414107506001c0951103030b00b400718060a4440c260300c84051003954420030846a03030000181c0c1c0c7e1014039032030001008011070000800c400011480c258441d449e218021007440040c0d001800d10914038000c4030000c0c0c5480d070320305041c0381580c0380020031600a0b016640c0000c2d50781400c0982140120005800c0800410f000b900c41c420a034000c43c07495000003580c402c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 690104307 1250 690103057 690103067
    0x180619090617013b07030b0106020a0c0512250803031303030b0301060f12051e01141302180c0915040501031a1c0302030d02040f050102160303020c0409080714060106 73
    0x1411824101d030341008110000d00740d11039010301d40c0400c4c1d1070307000003030003030420354100a814000d5410038200c00555a440401135101c0d040c0030000c3c1c3c2c40012400002c6140d00700b00201018044003a80107028480000040c0741060a0025110707022083c05480060800c0d000c00c0514010301e080c1c04c403642004114640035088030484240703e802a410481c0c208081e0b228000303a00211a108217454200340307060302e011410082c00090a002c80c0d40250004003103520305605c55450b607000d280042030152201407130100c80c1d00002a0080d40001580d92044140381021550b682012a00100c2400d08140000007800c4403416000c0d000905800701d0200b00c5503906000c1c0d4124010300009041c191002c200200d07103450784c403482407490a030940369000c003014030030002c0f100f52440030782e811900c59884980d4400c4a40b41885030710b0040c4605c05103004032070141401603040340d906070028070300300149030305100240180c190f0903210100300b4050300012540c0c0b104802d00919128000d00306c030f0b606100b0040c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 690105557 1250 690104307 690104321
    0x2011e021e19020d0807020d031d0604050603270a2603070e0609180906010302090108190201261609060309050a0209060d02062718061909061701 64
    0x108aa012402e118856000310b02c0209486405680c004ca40c1e20303950900b400c95118a210094200394003986200c24180e00a405410f02e01c0f40d2201108100c040d0010804940913601900368021010000300c0d08101159005440c07450381c0701d20521941880c07012b2a41040b0700c00e042560030b040703030800703518003614a042281d03003070790810000031b045041c03032403005040b0609151641e010b0100014680003507038500c10180d00030490060071880502d0070000341c585901c401e2008a0140c034200c4000705008401003072040d490480e0100c01000d4080e90b40045440da6141405142408030004040140501e050412071142c1500b440742d40c0c00102804d00100202c0c010f41c8003204251074610ba4000140001c2481e08641c1e80440c1c11040035100c0d240040c841d2040c45600075404031000680a10404241922000c0d26081185100c2030003600010303c401d80040c0700f05d12a1988517580002c5262422001c0c0500c031402c3d409401060360380700c16004003101d03d583c1008103a2098455007042c03c03002401260 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 690106807 1250 690105557 690105613
    0xb0910030c0c0321090609060b0a0b03040f02041407020d110d050406030506120109390b0c010f050a0b0f0a0602030405010c0302010f020a05030a0f0504030e060702011e02 75
    0xc0600c0034407900604102003004001c040000e07640703003003403401e0006091002c04040c0c0c1c0410030400c40320b86800740007040c5000086480d1030030b00c0d03d0000329217850350041c0c040391040c2d40c00c82e10715581c550f910082120000d108a90056442808480304c0c110b02c2c100511035079241c0c00815400c1034002c006090071409041c800c480b0340c03000040c03100d00307a4042c003038404a818500340810241c8410000500c20407800e100b4140c55840c112480313051010320164403072150001c1c90030580c04541e21030418000402c501c5d2000501243d8003040213024111402400f0a5044000015401041c06001c070180d80c2d094a600c6d4486840b040c43c07509030328003100c034207204d06003c8541c200c030940f4000003c0c1d100d005502c90b142c1400301e03040b02c0e00203241c001c2d003081d0340c041c18074002190b617003404200150140c0c00558a11a10341d01d01511604200380e0751140b2800b40d60540c07525a03208000d0010070107954025003089040260045191410301104144c0f2a825011600640394542d0100d882c9000b0301840034203d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 690107913 1106 690106807 690106811
    0x2070f12051e0f0403030806031603060b01030e0604020d1707150501180b030c04020f0c011e0c080112030c0303090b07030509010e3906040b091003 65
    0x10701c1c03681c100390b10798026080140400c64241c06003030f1002c0c005040070081480480d001c5c20000343c4c01a002012612100c1018545940c030050039842201e01c03584401c043c18956800d0302035a841419000000c045038070701500010300040d9141405800c0890b00303a0f200b40d90704200d408170342030300780c1015140c60404581c83e18440200024407500482107031131850301c10b15100c42d0040c40038006008004000c001c68142c04c01000b513006400320341101008100c0c20716521300078052100b041c84040700030f000125000c44028242c0f51400200020003100c04010b012000840012444543e01441c280b8040c203440c0c501a8020b15002c03902405121780b880c10401980e605402c024490f0004100a10240040d080303001d5480c2c04081d040d5070b000710300030000780c51119080b074400c0c200c03140308595040c1ca141180226035581d002d600614100540000d810415080c10059140b00e0445442d007 = true := by decide +kernel

theorem cover : BRFrame.Cov 689928057 690107913 := by
  have h0 := BRFrame.cov_init 689928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 689928057 ≤ n) (h2 : n < 690107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
