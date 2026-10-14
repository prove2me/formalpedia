-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1356
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:32:42.39861+00:00
-- url     : https://prove2.me/submissions/b5a4f890-7cc8-4693-9b32-3030b1ef4e4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 243705035 ≤ n < 243884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 243706285 1250 243705035 243705041
    0x60d0216060b1c05030a030509030c0f0f01050709150e1f020f010c05040807060804060e03030916120f0602092e0e0306010302060f0d020d15061b11060c070305060a 72
    0x840ea901c62408404904043d1082d40314890364a548040914900441d00f2400d600900d000f50201e0001d00c02440800c00b800410408215032081c4074000301880002c90403d00d0a460006000034200300c43c0840030010b98000f00581c210042003410254000c20300702e004034001d42e01c5030f0364044c042103140c591004519008101c14456821a5009116001e1138071001e99891046214034125680910001c001c42d610440d0219041032080001044010800407180e203507400c00e580c59803040d04540506441c0124000c0350400801d1035298800c041042a101d0b200030f41200c039409010a070300003d404070540d4801403603510703d080c5c00d0064085001c40041103042520f4035038814002c54140d520384c055070714000421504a07540141a6071901c1c0c0c121034000c0307041d081800c8420009400380310b911207580345c3d402041d280005040e40140c0f001d280500086c01e1018480c648165061516109408590041c16440c14070030203540e05c9544805101256241640e2584040c0840c0510400c0c0a010080d80e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 243707535 1250 243706285 243706301
    0x50d054209060a050603030a0302070602120108011b170705030603150906060a0b0304080712110703030e10030218010e0d06060323070e041104093203040302060405060d021606 77
    0x803003112003507501d0f4022001182d20596803290315a00c244106144d1500c69002405500d11410003d030901007520300a02c4402400e030030512403032751120030802c246100100c42c11504000c51820300d00f8404c0c2826829064a8083d203000e08000300040042c045450800204083d005a00a068500c1c03520210298031840c0a071100791042502d24030001da00c00345402540c0c001c0303402a00343c40c07400c4203607580d5501c072010204000b8284407840c4855814001c09002040083d4040d86600e41c5000341081000041842c14441009052040c400160340d81003440d04802500705c00e083c4902d012092000041c0440b0f0684001000b090418002100700980100004003102498142900b0082c1c0a510745407541320b980190800d1a190030b0005020035035030415205050806040002c0040143c3c8130086000303505e2031701d010580d402484035070800c0021548103060102c09005981401e0655000840a1007a849174910460b4080750800c449681641100c0b41904200c407000c0800d9100c1c580352000d000c240c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 243708785 1250 243707535 243707551
    0x1171f080d0e03010c030c050906070c0803040b09040b010c0b060d05011104090f110702030a0b06040609050a020307091a1e040e01180e030a0c08071703090a0c050d0542 74
    0x808554846540a0f000e08004501c4503140c2c5820000e01d8802c0c0700ac0e607001044103849062003500002103510003800180041c1008803410f87d1351300d141c80140010303102906040741c100490002000089295007401c1c1e034000703104456980000f01c885c2000790150030003000c092680303840058000b8204d00c482c3e01112400503200001e2180d4800519602640c4c011705a0281d09908000c511000042c000c1e1060b640c4003030300410009890f6252820781040398400c07501849465400400e00001c0c5804c030303120f0002003180300002400c440020003010003d02683c10701e941d0f0f42d0280742100003c08425002e0b01d01030305035004010003a60b9910000d00b00b00480d03a083d0317240c2d5850841c0207a030003400402160100f9146d5143d441504607e607444a0030b80e0302002c0152103200c06092552000e440c20ba00841c0600e130114004c0140c031100e401c040b0711360358060384002d10404641e000540000e00100301d820340480440d034809008800c07920340c070042c500380340800e64045104600a01440310288183c0b8040c5c1c01c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 243710035 1250 243708785 243708791
    0x60409090b1b0a111903030605120106030c060e032416110d050a030e07030606090c022b14030f100503030901021506240c010b01171f080d0e0301 64
    0x1180c850840c04040c018aa82c2c40d41c0782006a54021130058a6941203c0d804504664a0241c0c807107109580104070b550403000643c0722082045036203006040d044050203604004c010386451656404405030702032140f0810710103074005100e104c1d602404000039814801c0110080305403200d0003a031004c1e508903800b000500c1c1d50200c1510885c8608101d40d0720424040040080703c41104050365140c00c4038941c9001c158813040c150041c0b000901050700103610802001c00c6003400c021021084c2c9461080c104219800a0b1514007100034191000d01d1044a40c6046031100c400311500300c1e07a00a449070b1101100000100740501511f554161510800801c500c0100068031981015124840e003060980141d20800c00022007560001519030484002000c5262405010003e1000d841c41007042d0202c1d0480031500c280b03152000e000b6000030758400d1030115a2000c86686640d031404010740b40520b1401c1e0b00550101c031602e1103481c04041e09824013211151249814001c0c1050603241440e400f80d42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 243711285 1250 243710035 243710041
    0x21018050a050c041d190c08010c0e1507020105181203030906040b0630010f06060e120303041a090a15051006020601081e03090d0507080c0f210c060409090b 69
    0x5c2194041042081400900014802448a0f8202800c1c280003039451900240c0c1c001600082407080d07500c0302d411502c0d00320002c51110308014503009107900500e8108000c008001c0103030391142c110740b00200080071070f0b0a01000b980200d510041c0b00c010300301d140d10001003030052501d00040d42c04d03c07075807040b004124150703101c00500440f50203825841d0300340803c100f401283d0082100c1c5c042600c400c07610002460860321907111090b00c3e04e980c8501c010442246080400d0b0030031034440c0322002c0c00c1ca402940385003429030381c0f41800c0d02c52014484517040140d01190410740c042c030802804503000b54201d8501480702d03040c90001d000541c1d00161101c1410b10018000d4008a0124102c9201c0c80150200c100702141d00b01c0d000009020400c030a00003001140900d98031170010004050048000302038860400c2c20325840d080510002d1362069180c1d03225505150b40e22880d0042c1d25054911990101101240d01c2c0d00e40002c42c040558024000b24020544004c0c40e40105038a500030311003000607072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 243712535 1250 243711285 243711311
    0x6060b0406080109020a1116090e010b010c030c050a0813090e013602090708040308100b04090c12090803100605030f0a09141c091401021018050a050c04 67
    0x21250307114080c0812200001001900441e80c068220388200d800c0092450020b8092281411021100104414441203040c81014100c0c85044080d40e2900e008001052100d4006040308084810080400800d21240c108021b070a110044206a00c030480549403481c6809c1203034005641d02462251520b0800e02c080d580301c050140c01404036050032134030440035883c0301c21001c42c1800d0b01c19490b078064001381000180c80d0f0491146c0300e15044d5031380703070110304141c5001040c10002a1072224800c500369820b0001c61103080c2144d00326401110005080600c070402600c55108800c4060320242c9000d640405002211008522800c00700300a110aa61601810384d0f25010555101464000c868005081040103170301c40c07002d04d801030000d1003010703c0c0a104146810009814810801200e00030400f03081e410a4249010b06000e800c800070b9603110200007581c8442082d1010f001d25161684188114008801805c15039040000d42d0721f210319a00303000e0390f44c4103908040c9004a2034110054103003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 243713785 1250 243712535 243712537
    0x150f012c040e0d0e01050d060f0e04020a061110020a03140717070207031a1005030307050a0515040305072003030714100203061806010e090f0603060610170a060306051306060b 77
    0x3c09807a16840b6a07080d01070300448458000d0703c013100c017540d640e07000801c502c20310f03101030070041101c60078400c03141ca001c0c41404000300f070702d51207103040c40402c40a80752110f0340072480140c0008100001a02c45048208c00c44c0900002417082034500e844805000c48150300c030a902420240720341d450301480d100c100c004c82c1c0d1a03c9030309c009019901342404100398143c8280d81ca5421040441542e102992140006030441d8010300c001c44403680080b0940b01040802d12202d1384000305c026080c211413070103490103040c52207419802000100d0404001402485c1425045181207000e0100c5e5210f1400380340800d000390f003062044d410313480340001c8454004a03a0089a2140201914100c5071a80c01408034120030800b40841b41806002d501c40c01094175407070340345407240c840c10141f02860700741030017803509145001d003000f8040c04840c0d4420341d100303030094409640300704a0803811413581e42c0c1c0d0f0302003c0100402d0b00010f1480d03081005000d64226900d20070008540aa5001c0016680d545880402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 243715035 1250 243713785 243713803
    0x50d05070906050a030e070e01230d080a1209050706050c1006150807052101050405091b0d0f0f0b06010206150a090b010c020a0f060f020105150f012c040e 68
    0x200f00300b00000d030b924880c3d0402103183c4000380880304120740320f21004100c00400d80002403003000300160980400520101400012004d94424101603455160044140309170044a000e008039007444900000c0c0540c80b1090a1b90094282c400c2d913502c1d810002c2c62540080303030042c0c192150071643c400181e4140320700400c6525195003c01c0c100c4201c102038a401c0001080b604c18008248170504848411003045600c00703281d1110054190305000c104011983d014041005076800401c4c55070707204150964a41c001402294200780c03140f002d1401c03400010f0301800042920341074180c14030404c1074101e5214080c0b0f1090702652216601c4411822510100c0e041040e030241405104010515095002405801c0107160001184003181c000c1112580c540c1d100c8101e801103090b00708545a03000301d105110351841d01c000e015a00b4220300704030442e400341c032841c1c2c4140903104802c1d40c1c60b0f010b00f0806a089000b60403d100e84600c11300d080040c0750000241342e01980c103080c18001010404a0100c030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 243716285 1250 243715035 243715037
    0x1201060f030f03090915050a060203070c172a24030a020d110c0a060b010c0503030411040b090f0702060f0103030203030a0b0616060501050a05060c1c03021603050d05070906 76
    0x965480c50b103480c80300c049148002c2e0103100c0030300000300319031007207000d002e004050322201414114500814003c1442c00359104134219041800008000303491680e2640480d00111303402403a0380c80e46003281d4100030060060481c0d501382024580340307014240d2001c800004d01100c00c0245c40c1204030f003003c0644460323141768042c00e000700f00140c2c900c0b00d0b03980a00b00c014104600041c212800810042085d4032900c00300d0039660218414004001c00ea010341c0d05800c0c0286000451010785580d12541e81c0005000209003144c02c0c000480b4036200c030703030141c009004d00a2002d1301f0f6007010010302c01c1c982c1c0203840380fa005000307130800101428110001d0344c2c100c0768194015840d59691750510b50052650050f4144d0000d410000c08800e41c00b5010312009450103030b8000641545081e0400803007100a50029000b060148040040b00070042191005800902086540d000c0303a00000c400a1043c54944640d000c0c1c0d000039007041c581d005010704400840d0300c10030802c07512909410f80f0a00d9a43c0701d254 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 243717535 1250 243716285 243716309
    0x60c050a0305390115050109030f0f06060e01030521030a1e050703020a020f01110a0c030311070b0a0b01030506090c0705011103090606030706050408030711190303030b120106 77
    0x200028401d030000c0280c10034284100c2c440d0441d03d540c0e5001030400e03052442076482c1a01e641c4500c0340b020722408055403005000c881005141c040068421100c0d48805030449408102020070701543c1194018544c1c0d000e602000610f403200310303e00c0c07814820700041e00c2e503100c1e6004c55070344503000b107514040104444021506655901071716502a0851b00e02c00d0100298a100f00b010304000c03801580e02034081a2809610780a0541000b0b21f002d010450a0815030704224611842e10700c010100c4100044600c0c051206050030300b802e80181005102450060000140b090f050240c7c07006458040c2031084810f001c01940a001102030791001d44000b0f501c81401800305c8d04000300c00b4028058144290000b10b2000c06041e036030003154004580b000c0098000f41e0410140e86400c0c0300345000f07003503282003190070103080c207094907a68000c808000341400c004402450041c1e803140c1c0700e0b040050800e1248007030340d61a46001000380c580f651a5034040d0307548202502c20b0380d0040c040c80054800300300802d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 243718785 1250 243717535 243717553
    0x2070c120f051204091a0a14031c03050105040b090402090a0c020f100c0207080a05030406080403121b110706080a0f180308060a09050f0402150d021c06060c05 70
    0x603000c00ca0111411501440303452590380c00a0028841c2c0c00452810108031a00c0b0352624444000b5210825001003040ba640441220140c1d64028054291054184103802d5550840007092405000460520f1284000c1c1c4606049035410782003903041c0c0348207950a00c9074280c44c100348921240165030080d4401140400a201550550300046043d151072040f6a00c1e12513160009040c4032072403090381c2c2c1c0162110065150030390100a03200040240f0001407844019986410381c60780203a02030314042101c6540454180b500c40c408580c00d008540d4810400300c80c4d07641c1c803502c0d220b43d4010340c3c001041401070110300c080404100142201e11646500c0788554840e42c01e04010b2090b14443c0907010b03076801d490f030030046250021144407031290f06d40181c1400c14a080200050207580001140d034100000c000313448084800300390708039070b0594180c0240c00b03501d0000582e602490b820490750901c0428041e50f88010403411025a40f0700040800800b502c035842200d0500d1110300240c02e5500010751 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 243720035 1250 243718785 243718799
    0x20a15020d0329012001090605010803071509022e0e01110d05030a060305010204060903031e0c230105100611010b0306061201060e160206070201151e0e07031401080102070c 76
    0x2000c80b0b074010524003041000d01c56901100398018103001c5c241d403a992900341004102c0184540ca014144440056050044590714031200c1d03280442c1e2040d0030740d100e000200464a84a00c4080d91010814aa1003246440300030300041401e100800300c00504080c45540c029400791b404003800084000c050321180c00d04000c1910180e00180400d000c83d50381e484000040f410a101038009048155100107a06142d402c004107440780300c0950200e034010501d4014001d0350009080341403981e0240007501c0c80040020607141c1005110140c1c1180d508200c104072064500740c10f10001c4d1841505c4166080c00900800380c00c8419402da4a0b801d80d000c4d201007842071515002c0002e11310303501000807400c2e41d01c4a8020400d400c054031202071001104500122140e0107118642d4050214802007214007601d1521245c091243d00c81e80d0680b02e480d00014404440321082c01001c1c041100c442ea046003802500207008103003403102e5503048900400003003000c0c0c030103000300c40c000349e0449601c2ca40e00d802c2c23142c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 243721285 1250 243720035 243720101
    0x613020f070f05030301030b0c0301080a021c06090302071e0807140d060213240206040b090708060108060f0106090b040902091f080f01050105090328020a15020d03 72
    0x4040e20301800c00d01000001807a016014850b1500c00c401554070382d40345203040e40408901900400303891805100620808600003140c08000340c0440c0d104010084d00100fa44003c2941800a80083c3c01c01481e001815000601c5104a80300c02c55045c80403603c101544190690034040c5640a4024400c20000080c07404a1080c00c5200180510340c4c0032103550340d9208070780c0552200c005044011204001c11182d5a00c00b21560b1049409540d440301004030007902c0e000010310080085d6138540224441c44401c02041001d400c100c0c2c00c860403546c407501840e81e41c1c1411183c0700c0d20708400c88008210244035140d040d0482e0800c100940c281030034500003030301a4215150310b540140c004011000d00d425105100042412903851707244003402c10281c45120408140c00c20340c1030140c10003c040103904d000808404c04e203260182e60280e00c80060115000c0e45850001a42c002800540400c1004189105882d0504940c086a10580b08480700360140c0303542015006141d2042103c526190440315 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 243722535 1250 243721285 243721297
    0x60e01030b1c020111030d06060818030306130b0d05010905010f0b030601151814010306150c0816060903320403020607141b090609270f0316060b09061302 68
    0x1050400e030700804c003200e551854000c1d01c1f03c0702e00e182d103031036042040e03603002805140c000f401317090b01a1200c01e24040d025074900c40a086103010b1407041c02c0c804820f64443d41301881307030040240500806550341c100180070b04100881510b59519104007110030340d00c0c5100351070f100c01020300900703000d80c40d040019009115a02c0d0000a20000581402204420034000ca02610124022580a040d014001011903e4503085138020b20f038010044990075400074440340c2606c1d0300808a5548200000000b160b0224000c0010b0005d428410300c4000c1603040080c651709650045130400d6100345482d4070000b40c000d0444582c540040420080c4058208000205501d1b80984041e842020023840c0007840c00446040d80f52159105034500502e0389095006c00d03401810841e0200e00c903041807264042c1180b84000c0d409540c005107101c8490901082c003103241592586000d8948484040241c0c0c96600007034202140e80c240380c01d90041c494540b4010b0b0174055040640741040c0c130524000100020340c489 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 243723785 1250 243722535 243722537
    0x70b18030c030a0f020d08240118080312090a020a050f0105070b090c040e010608032a01090b0414060f040605070201090b0c0a140c0a080d060306050a06060e01030b1c0201 75
    0x1c0159a044803420001041c1c41c410030b5590010080d918400241411007000710641006408024003c142481000405500212a603010021a01c41d001640d8040340031940301d41c101d60b60a40001c0160000c80680720310117481c00c901c452641c9011030b841d200c1084c0d5400039440182c0403000d04c118140204403101506042c144946001c81540399400f040a00301e0300820a540100a202c0740e03410a80542d0f0010000e840081c0050340c01c00204a449004003040307a01074400e4030135480e0040303441c4d0300380c0d00001c42c03054000c12488289080c12901c10100b180c0075500d41401100082140000180d0144200d2030001070301299116a5074400240c4000ba0407542150340341c0c883e80c004281080000c500514004459070b990310b11008020b4a80714880e6404164443c0c07d05c248500c101c8041400c00c2180e9020b14030700eaa078215809004001d01e00c80e0000740280c2d14000401110344201c1d0710035020741c0d03500e4441c0445021907600441c103a440032200c03581c000d0b4220100003401004040c1c401c2d4400c0c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 243725035 1250 243723785 243723787
    0xa030305040213180212030405010912051212160c0b040209091c0806030615011b060f060303021615090504051003050102030c03040b2a030907030203010c02071802070b1803 76
    0x1010080d041955001c811902896136203100c100110f29118400c10f03d851003103000780d8113152504001030f0410169100303200700c0300c80d411520010020203008ca102c1c021a04003059840f007040c00000c40c1080c0c3c085481061204610900e100e2440c0208070200441d0f03480a0562115a1282d0901c43d24a401130b21240c45440343c5840d1086050380c045a1003440300403a6030300301161606004040c5403a4019142c0000484030340c05551450344e21040007400d0242044941c01294510300d0f000c0c000701414408806090310303203100841090b5020807440d4840d9040c03c001d0400700c0e01d0303070580181044c3d400c104801282c0003a03410040d034100b03500155440304c090034520700170550700d850307403400d80e070080311080040c01c3c3c00801c10040000315821950011078139180b10700c908450001e011044a4440440981c220000c40080c1c1d14240c1040850055136000e4000e000110080e20080c0d6189114041e1803107100d25100168603220079482542d101039009928400b0f6512514100d05004000b10022952400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 243726285 1250 243725035 243725059
    0xc030c07031806031505061317071a09030d171b0d020a0e180c25020a090608150618090a1b030605091b04110412061d030703020a0303050402 62
    0x5a10b4100710000c1a554a01040f44060101c01034000820b58000d5441002c0500a800c24020050f0300c1c0c1c420303543d0044110314145a5105143d281043c03984c0441050000c0107012406086008058144208150100c580c00385985005884504200000c111032241100010b01704021490aa10700080c1400040380b41800803807003941641e001c140c000c0049594021714454a007820141c4114070105600c14050754106440044024400c2221006441c0003070305080d101c8007000101002a5680185150f511590325110a0702410740da11569440703000340181c907407060103c0c505080c450f180007412002c1000101c42166003011f409003000145203d041d81031070028a11201095801140415416005145281900a460004002030644c0d08200c02400f822813000a0820000000b100d02180400e900012906503008941c0400d1500a048102a081c00700030f9001c10b0b894403400c040c1c10f140d90318060585075248543e04004006034010184180824840d501c0707107800c5840101050a440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 243727535 1250 243726285 243726317
    0xc010221040b12160c0302150a0e0a050d022a1018090e060a0b061912090b0103020a060206010302010212030a02040b07081903180b0903090405101505030c030c0703 72
    0xd04143d881d400801942c4041c8600e2007a00581051951110300c1c0841c104822170740e009445e00e5072035042024101180001c6619081c042d0003503089540344008551103a84142032413580c034500c1c00603480140c000c102c0d100000004000903148400c02d6030407101401644002030002c014829134000041050240324002c042414050301d03001400c4030314003c900c0f014034010f50341c00e0840c0980030b49280d61411100040b162541002e8a000d02d20340c0c1e1194056a0344820140c6410710354140c2841e01a03d17001c1c41104001c01003200c00d041e60b00980d011002640c580e2800c0e40e40c2e540a01002e80035034400900c0c0244134140000441d880b00e69444054249643c1c1c0400c0201904040421034a8120204a0702d6103940e00c038846200b643c3c0503150510090350303124552114032040d00400740c4900c80791800501c046100304203d50f40e401020740f080002c1e150005882c1941415405950044443c028405000a2140c419240103031400044140703161213044172081c40354803010049050043d207010011f140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 243728785 1250 243727535 243727537
    0x503060408030108010c0e090411031501060918050408090607050703080a0f1710150504030c03111002010207080a2109050c0111150403030b21011407020c010221040b 73
    0x40e88640d0340940c80f075051910b001e017900c09220190081105250081d0069aa00344480e40c0280d0400c440204800c03002010030305204d0460280c1c0c0c1100003483c0001411980103954104076112210706000c140c900548880c141d403015100a004e2003810b0081c4101032900200410003144144125022a07a5a07990840b903500320507808000300e001d4009a00341d081e0014001c0f09003c45d1113620400317030318211b0703a440d901054a000e0703400f4a00345250900004c1d8081d900301d502840d081800e80e00c20540d40c0c035150b5441c810040c4cc0710f00800c9444102078010307005000384c1c0c441d0f6500c14603244c2840e1001104488404a01c64a400c4160700702e01555810f03203051280c6019180600041c1c100001c200001415210fa40300c00030813645d02c0b04140301c4a212086001d40d403ca81d01d85800700740c0b40b802800240c045403290354010b100001854030722010398415071110107044d2003910922016600c8035810303620780c1d03841110f2a015030017080c6000300380078001e204003c041d041403061500306919007404200c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 243730035 1250 243728785 243728791
    0x906060706050f0402040b1f03020a141603031103040b0f0604020d09030903020a0f0513020a110709061a0301080307030807050f0c15010b03040302100903020106030602030420030c010c031206050306 87
    0x9145034803c10301c0194105070081c42034202d000d641c20002d04560044e9840f1030040181040d00f05607011603103203103d52140300b4510313104050a03811600d60f42d012201001e005501001100803078500640e0100c0488154180c9200c0da40003aa07510040c0d9400c0820300990500401c03540d40294200201c0d003003c0c08038031030180f01d24000d58400010901714814070000c01040d07000404121407581e4104069030b24145c0e00581d00384140f40240c1c8030580088141c40b202804445061280600640401c40055641c400030171181c641c03142c44403200e01250a00d19901c000e0090580b2504100407900102c0d00039000c2c1608485289052460202a0000c1d0801c5811400300004c43e40c0090001501102141c0700140c054001d0410151a41c1010380d00130756030300c120040c800700083d101c02c1034205150007940104025030b0005400e550320b00d400e142440e05851941c404840710b204a90301c0001c00d04000610340100d40e0107031100426252181c40565602c01c010300004d41c07007901c0f408042031a071400d201b1980 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 243731285 1250 243730035 243730051
    0x4090b0c07050c0406050f010e040923120906040302060c070e0114010809010c0203070228170f01060303120f0f06060f0f020a02011b03111506010e01090311090606070605 75
    0xa1100100e10b0418100090007218503c103506155003880155210101c00b2041c4000742022030070aa42c0034041000b802400c4070141c001c00e03801400761450008031540545200b00306060f41c0d0b5a40340c00200b000f0500860540b2500180c1c14001800141400c00c014207002c00c421302140c004940c0d4480c2d058400409070020400e041103981c400031596000340c059a0403840f0350000307010b43c81040754025901d00a080f00a843b4902000c03801c21503000201140d4152009040e0001ca4103480f810707480f20b40c00c0c8203000601f89108800413902c094506104401c03d503581551128804c08a0342e400b80301502090390802e07203d0340e0300e080c03c1c0002c40580c03003000010295500c460681c803000240140540340050032490654201140304030040c0e1740101228640030070001e140540c0c03500c0d0704084449003142680c880f0385108034219000c59142c480d150b944200c4003662041072039010f4600446082c50720b07210040210303500c0240a105403603c40132a561100c80903203064104901501c925060740c82c00d8030040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 243732535 1250 243731285 243731287
    0x40501020c0103110f091c0303020414010509030d110c0616020405060d0b0a1a06070b040203070b0403030206011505160c18020901020a0b0a0204120305130602010e030a0e04090b0c 79
    0x15540c051080c1080900e00742000c212000440411644900c680319881462102c0001c40300100d43e943d25040c101c070599112001d026100c1890080c00940c407034052035103050036802081d4030039071180c0111490010003501400482c50f440702c05403503c100c0509800d003203008440303020070580c4900b800b421a07861048501500b0105e64018041191000791405001c0d4200641403800708503a0102c032500404c0d08440040c034010b0244030702009802041386c90707a00c60350014100b003d0100800c0c041780954002c0342030302d5095540740c0030000c540c4940c0c803004000da00203100400864014607060b075694425410658a00b0101c45040201c1500b034002c101e07441124101c0074070502400b192000b4803006050750840c0b03091046030010750b07181a12600101491407240000302c081600b038056a00400c24041030b030482140c5407901a1241d0481d0300803c0304a440a4000242213105002d4074010301400c40c050740c90700850354400c46d60026100d0070150850389907140da10000d46141c8049108007103455402e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 243733785 1250 243732535 243732539
    0x180421170a2703050f040b09041d0c0f0d05011b02060618010302040f0e0607090305190c1203090e190b100801120606051002150f070e090414011104 65
    0xc01240340081c1c0020061482d0500c00100800341c8141d22070072442220708000c1848951504a07004d2041301001005c501d8003084c000391440e040c1d0050009448111428041c0300d040d5484048040543d50240c10300703500015580d840d9040040106400c41c60261290f05076004545405003911044040030320621000ba41c0f01412f60b9060000381c0c0c02503400c803440e00c00d038140b030961070840301410700010b0b2140366100482c002a20056100d44000599070098514900d0001c4019107100500d01c8165450b0040350360100464112040900030075900c86182150103060031490b6910702d00061044061140b141070100d075800050900e075106e1180620f1505107008416142000d494801d440304d40180e04008441401c0703a0442c0c0303090305455911140d000200c4250804030003400f2554400e64000400d070b1400c594040d408610808072030315034600c240c081d40302c4021040194404940300400149910540211407a100c0d0126030024003c0c0021940c01440740c40c401e003150184510040601400502 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 243735035 1250 243733785 243733817
    0x1d030a020607050403150506041b03020a090f03020303040e061306141315060e1309050d03110f03070f0903050f100609060f0510090e0705090f0d02180421 68
    0x20203500c1440c03890018205855035841080c9150848003221101d902c5200123006900c2d00d610800c43c02c151400e84200042e0004405030003076100c1c00360500092082040424624118050301c0300f1603601400071840c01e80b50014201b00c09102a00e242da22040f0341e099442490010300820340503002203100340d1012060b1004202c103d0f5807051074810081e00302480b140100b075200124804581260401e40311a1400328001804210f44142d0103a00c00d01d4400120140907002881e8100410760342c604100c0320304c0444546515005510710203008003c10000900390394483d40303d03252040750318145100602d80b640c0da602d061440400b1944038552190491030b071242501c1c00381c04010b2a07018001c01015090003ca02c0c400d820078010203008070112000325022602ca14030701e00040c40100e01300301050030049030042c602e41c41084042d1080b0742441050750b0714604800c0c15015581d00a1103194448103000c5041c0c4500c6004000340c400f008003644400b038101024088610b5044241e4030b0719207820718882 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 243736285 1250 243735035 243735043
    0xc06070b07020118020907030c1e050409050109182a0b09210a08070813060f090801050c0409090609060c0e0901080a0809010c0c120c0303021c050d0f1d030a02 70
    0x4070811382420007010000143e100c5410b51a040211450003043c802206041074450342c003841100c203840644c041400c580350340e1220242040c1c5885072000d02199988084105c01d440c01603190707841f45200031003120b002540320220070710f20340d104510b03840078030003100102414210283d1010320452030000b001d060601c2c040050204862005001088002c55100011344d10814001d00a00c41d540c0000d07201d0900410105954104e00e608580c4c10090351034001c0201030a06004141c004034466880105510106005083c46288112900c600b080d20f024401d0001c3c0c0303080d0000790b50301517540600341d01103010741c00740000c3d060603030312443d4910000703000f4006030400590192907107070060240940043c194038200c54920300f0920307040c030151403542003046501c44107500c9405102c0440b810f6408000c680c040200880e0f020fa002d03141003104405110120f081422680703000114200a802d40e00d540c075a01102c41d00400c0c100015074608500c80c95040000240c01c490318640c40801c1030320741103074104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 243737535 1250 243736285 243736301
    0x903030b0f0915041a030105131203020423010e180711070b0405060a051308060a0f152304150e1003080304060513051603060f06060c0809030c06070b070201 69
    0xa55030014510f420000240080c400310b03070240c8220f4a82c1d0314001c4039528407480701142c03500200200150300b000c090000c0c181404000848504202c403100410f0706c0d0080c400e40f01120a00070849e00c89085130b6040070072030f07541d02c0080c506100301e058010ba400d4443c20103511403e401002e403007242e81007004000e824422a115950a5039003d003000f8003030340c0100301c180c4040300e000703441640d140e81003218191040c2c0100009454071030b04917140001c191700009001400790201290030000121410400d905031001030564200030011306008120814400a0502004641e031403045e00c40d0300114000f6007600c0d110242d202203881140d809101c1016042c001a4016940306280d546081c039550f038144160100a0000e4040c80d502c20008039040358000100c00c00550050641d015170b40e0901200642030340700d000c15280c1515100c01584400664850031003920020384418201c1e11565560106941c05600940e0701070140890044041c0c032030740050440c5500c18500340819241c000002404c5604070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 243738785 1250 243737535 243737539
    0x1605010e03010c0c0213140a020405040507172a04060201060f0501020f1906060e010603020d050105190302090417030702030406020d030606050f03041a070c0302010b061216120903030b0f 82
    0x10050103c00d45411104040c001581541d141e4607082800111030000e00c070300140b0600d400b03105d00c10041100045d038018003d07101d0440e0104016203c03040122444500329a0948a90881402042c0c0400c60030084091860704407040d28030014009813603070540d400070b80c89000983e4603980700340903000075030303510394040c00c8203200030010508180031382c83da1036003041015041012072001100500206c2e8000c0c201a024105103003c680d40e540e14001d00075801804610106854600041b80500d8007030111581250100f00f45038010b030a50302005006400500200e804080300345110044484c0180a03500c9a120b075000f95444510303140019050481d40e030000d004140c41c002c410300c04c054200060f181e203c050001d1094603941c0320f140826103507140c811131010445030442081040c560160710744000314481d500a00042654106002c010300407000e001541803c0d5070005030040020002102d00b1071650b00d0030f08007003000f041c403140403621303184002d0f00020b8440c5ca51410500b01a03c605100c4842 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 243740035 1250 243738785 243738791
    0xc060a14030405120a0801030201110a050601050f030f0a1208010e07091202060d060b030a060605090904080c150f071b03090b092e020c0306040c05010309030507051605010e0301 78
    0x8440010318800800346044041100400418203000c2c0800c0784514045030a4802075890920039000b030040c100074070040780010000d0590403c140d90102c1c0490380a5403083c01415183d0900d81040044d00c4142034458152080810300c680c4104100000761071540242580c20000281c4c000050590f08144c200d602c40035108400d1015090f4807000803802c40d8403003150320751050302c00c2c07000032950b22540c2c903840e49503410a20003244005035100214081d1121200030483d035a5200d07002d45071400b0300c101d10b50b44055240b0000380031503000303402041060500c20580b900421040d1381d40c3d02902e0107484032551254200204083d40e13801080c2004c40804282203000980c00c0c0341d070000c02130280ca024900800d180401c030445c0a4840303039441c0b8a00c0c40c2101c805040030803a200c817800a101220504001803241021a114609012802500403034200340302c00c090342d04000055000d8030300f081c021810000204240c401055023031000d0480c80c8420b010f03901340e141c6410001001d56030240380b1076100303901d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 243741285 1250 243740035 243740047
    0x60414040f0b0601050c0105070305070914010206010e10053606030309010f02070504020c100f090f0f05070b0f0304110603090304210611030a140f040b060f03010f0e0c06 75
    0x76400c60340c880026844001c200e250740d40c0000403511030043c48088200d0f03608200170700c0006609034014a00c10b090381d41e02c0c400c9035640d580b007600600310414801400340e048040103000c050102542035070b00207151110881c0030365aa01c08540d00e0503190320381d00c12901041c079045000352112076040e15203107521240c9005c2414150300203622403042215180c144506141d00c5180c850080c030a074402050010011502d039000081c20b603840310061f039203082c55989403103a0103800307000b02d100e808540e03900301800102c42040c565960040104a000a40310fa100b441c40c0012901018002800d0305640108015200e042c6803400303c002695124016100d00310078420400382c0d0748004240c400302d4200111000102019885070b0031a0b00001e82d01414580c1007908007000c40c01d284000318014030290f0000c020070600b040454561001c150b9640226251800100f008103c00b8240d0302d400ca080100854000d003007800c0044d08403806417200c00b09098481d01c180c030020740b007440200e110f43e0003a641546080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 243742535 1250 243741285 243741293
    0x70c0806010f1401020a02090709031416030813050d0303091104090809061e0c0303010f06020a02011b0614250c0f17040909061508030a02072102060d0506041404 71
    0x602c0c42c05407181c00a0300c2406100d880c0e10070807080c0328440d005000c60b070107800d080c0d50040c9a01c1c8940000e4907a012031800c484440c1c2da00060b410103288000900d0641c0341c0c03c541d500103842e40013400504140e450b03004041110754604010b4204e0703c0c46520005801c98a61502003140c000001c08640300d945010700030000301e0000d01c1169090001142d580e0390720820365203290b900d418140d81c10744848001081594024000000942c10790b12121515043e0759510303202240d58004c8140300900180301e450b410406000c01005200036144904800325040e101410101c0141d20700300e995000007115a150010851460300c61001d0150b0607203048544141103840e0142e03500c00480008101001948003201240840d8007074070060000d500045c030020a030380c280b01c40a03080c220305080f036804101c08000f0706c0710030000448000c03800740e0300a401c503145400e203c0800010f040442c0c8206c0041030700700d900140c0d16207004103403801c1010030001d031a06044090104850f040054040380f03c0d60a004c0c00081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 243743785 1250 243742535 243742559
    0x3062215150e040506060112151706090607020d0309031106100306050a020f03011406160f020f01090302011e180306050a15050904080a030b0d0506061503070f0318021203070c080601 80
    0x14001c2c01c108d4000103014048000070500100c01c00300401840c203001c900095104e5120056202c50422140203858111100d038840000342c54990243e84000b11003d032050091300964980b40c000e080c0801841030245489082440848162100a000300000d0080013450f10501e500804034010031800e014208034410300c0c3e0300c41030040700b50340b18201e510b10540b0754500e8112001c810028480e00f0030031802e850541000e14202e030080344030f08401007100015521071010340080b41d40507901d00459070880500380f2412504440c420b001c205222a0103040714643c12807240c020b500c580000103052410a100e5411540020250068060582001c014550358031224507045900600080d550700c1950500390010001d036030389680c0140420b0140014000302146582c0725800590781c0d102c075aa9103152100c40c2d0320044604c0303c08a0754000c01c541c1d21600c13030f5102c03052175940c800c401d41390340e00342d50001171500d0007100c120384560340000740146c10044462203070070040c08040003c06007035040041c100c0321 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 243745035 1250 243743785 243743791
    0x90d110c1e1c0b190b0f090423070602120f0406121503110f0f01020616020316050102130f080c06070609120801090c0c0203062215150e040506 63
    0x1684004400189035034500001505181d002c080b121a00a0a07160001c082c2404403940340d01510080c02ea5100c40c0981d00480a8511001b030019000e07884c002c003084800d24024200b903030f000c511300c920031340b003460085401c0310005081c1005101051804000a15040180030350452080007442500d403000c0085003520151812814200c490040d41290340f0010613003103120040c1070340c03449400428403420600b90200c500040da5421010041e85080c0070410000780d00040c016403065000850f008144d004100560b82c140c4156480d009010140006040d2100d130141c1e5165400204128901c00382220b45004010001e5100c00e064500039480d601c078611280118011a80080c80030104001039010b10300c4554000e4100315000c4000100811000003402042100d5240224844035540185000083c0c90390003802001c0d190303038034003080410021600032a034a41c1580501e510001ea0044039401950004480006000352016411504a0560760088a541c42c0e81010322000c9080407540c654 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 243746285 1250 243745035 243745069
    0x1f150f06030e16031a09011e0518011401060f080714130909030c05060606040e3c19111b030d0c031a090c0a0f02010212090d110c 57
    0x29030042c00031000ca0800d0b20048942d4601190101d0200400801d10030b50704d1046540b02d07007076203580e41d1100260300b00e5281d214003002210310070020340300c0703501d9076040240e01c00c0f002205100d900d8141c2c0086425100e0030b00000110310b0a11005200039680300a50105140382e601d0701b203015041040e00600124002c12404a09210000780102e9501c81140d40200625402c88100f0666156040c000d106449000c0100c4550181102281c01440d1401c180c80544a288804a069454582107861081c048030909044a5000c0741083e13640e4140891420601010740844c450900d00031b806440312001c08404000d2031407030f002c170f503003009842c41d0b013519000911404001086010000254514010700078003031540c42c18001d101c41ca540e03054001e102d124655030360604c03050b04504200911050304481d4241110020b120368441345101d800406207601c1c0c240001880c009154501400c0300303100321000c0c2095802220071940069011040c0030750f910300b09018004000ca03400000310382d0484944011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 243747535 1250 243746285 243746291
    0x304060b0d080c030c010e01020c07060e0a0e09030c0105010602010c092c09011d1902060f0c0303040c06020f0105040c060c0507170d02070b0c07050409050a02031f150f0603 76
    0x803000d032600014451259003008245403910b841d00c0300c040d0b485e4407070424411994280803c0202c415814002d6848000c08074000c6d20569042c000111a00c504840d00264042c003805400240c4219000e061170182070440091503031031000320103ea09403401a84100d046a15000d020b09440354032102d00c400b0b90f03542105282071a506101d8800c60201d81c00c410b840c0410400091001904055210724640b0080300e80405681c41c1135442d440c2c8075a00c0d00210360f81c48040a400c0b900515000006000c0411140441400e240c000c1c664a4070f550000c55003254640c80c0c0d1902841580d404004400102d00802c0091000307103070a0351000e011035050712413501440420140030007041809d10050001c0c00d9445c01e1040c14400b40c64003035554818804050000d80140e90010820000100442e91b0100140d801040c00514023014080145100d1105a0740f42c09000e800200503030741030028251140c914980070300c2001c2207d072014100c0c0c0000b0100c18540c0f030a00c3c010418604a071200380304440c8070382400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 243748785 1250 243747535 243747551
    0x81b090105060d091202030901020d050c06070f0908010c080a060e060307091802030307050601170706080712020405190303030506040905060f04080c120706060b090d02120309180f061005030406 85
    0x3c00090190041c0081c2240780c0044146442c80d800005868103071800d80c01c170751184480c0b900644080c40380a82e9805c5a030000360004034181d00454070405031000300d181c0001c032590343e181030380d085592083c035890024880c4030900c03c1089080c0100d0f005440900d4801800b81040000240e840340c4034411029015140e55134050a140004100341c500d40e0042c0035a80e07580c141e450310b1a144e04090050424840f005030b8001d03004c501c00100078050342c2c015210342c0c0840d100c2240540355654a4007040394002c0d000c11010031540c8414002c8002c04120000440ba1641503140c05401e035203004092034055860038004802158000800301c1c3c01282181042c000ca0f15182004001d600c9400050078081c840c0c00d640040e809031080042031240d0241301d08204c11038546e40d41601e6445419180c0b907128a02a20910152034032315003000350b6031420021a0300c4d0519a4001c140f00703001401100e02c0004901040022103ca03400b821540224101c5221515048000000d800d0707010103000500101c1c1d0300e1b0300c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 243750035 1250 243748785 243748807
    0x1415010305060f0402040923070f031e0608010506090603030a0f0e0a08060103050304140a120b060a09060602071403010b060f032d1e0c0301090c030209060f04081b09010506 76
    0x1800d03c100340040c0056540c0c3c1e440d00032100141000c003022403d0341c500e920440c2801c602c0300345414015200780d40c0d8100c0f50a140c2404801400b12a005200d41c19400310221000d642e041c42440010100d1600118440c90264204906071900811140c000e8100f0003800000710b5221004041010840c104403888103040804525000a01c0d0800707007151240c0400072040c040000080c0007140c0444c44041070a20503a4140310040789a88910704000040003014000510b0320398100d6030041c0058000118680d03140c1c86d40b003c0d90303c0b5038040000b50300800c40a210341846070208808821046e0001d000342c244582c0072035900e10810320003c1c0b1580e40800440c100070070000c1000c0100f0400200040c240c50542111819043c06840036070a00d0100d0040c07860800c42c01e09020700c140f50388446182103030318001c102405440d480011504144e03003042024801d5035810060150310800d296181d85a50806070300342d00d0a00008400c05050003003c001058681c1c03003e080038107485d4260b45c1c11703032035860b2081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 243751285 1250 243750035 243750049
    0x10504051f0b13090f02070b0123100e03062a130504110d020c1f05091f02040e13060e2b03140a1a060715020a0e0604031401141501030506 61
    0x10900c03042c203040d0174400c824a1600030b45013050090310000d92a0341c1c2d881591101011004d120301d50152482810500e602d4900181c039502c00290400b50f101c50300c0c01c0c001904080c0d00b251030011880100403100c6414500c4500500c800d15040d1780c092138103903204545804002e861082612468540d03650281100c091800c2d41c101206152082d51a0718034144540c0e100e408581c03c6407030054000c009604520314a004641c040c040e50340107410414207407c5c4042c40d190243c1000045241c08100000b061005c64498034460022807a0b442e01c003003200d141c034105940300114207940c0c1d40d0262585101382102081074002d021031001076425503500200056001c0c0903240252503110040704104155040141c210541544140000780e9400d010202040441c2c090344d00d020708012108125100c2c40180e40e030042c6100e0742941481007600c1d0700c0c4400140300340d00c2504200c99041d04010700800400c0309000b401d00300e0f00300032400d900034a065900041c40d4941d070f5103081e0402d0303100e13401325500c0d4461f10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 243752535 1250 243751285 243751289
    0x4080403050d0905040c1b0209040305132603070b070e0a030602121801110f0906090303040303120f050103020f040213091112062707030b0d0b010504051f0b13 70
    0x240a40742c402001d0342001d80810540e1045901940c10407410b580558468044081068810081d01651031095024441c040c1302c020130071800d03c0400c100106466242d10404401000025541c1c0c09003100d1010002c0340c040501510090303070340240070301e00006969140860f0300044502c1c00b40050205400092681890350340054032480c40019892000003041c203125100d10303c80c07032000d0b80240700c3c4030760f00d400ca660802e60844103a40500a444250206100174107034242e000b8542c0d410203e5100c006030960f800341d0310031030202c0e46003452246d05044a001d800c101c1064038008009942c0b4540100e0f8004140c0d0403000d1141c0da0014801880d0140302c824200a80302c4040100056054141c5603900c0d0345c80000c144140c42d103043c1c000382042c940922052900d000082040c0200d03541e0000010700010060000e0b4241901e60106144580f200d0802e0100d1a01440010400354901014071081300d6020742016a0715810005116a5011011841080f03400080c0e20303a03075807128950031154000e419 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 243753785 1250 243752535 243752543
    0x5030f0304151514090702060c0a03020c01020a0203070c0807050607060209040f06030c08160f120203030d0c050301030627080d09080d06031b06021203100b030f07120b090105040504080403 83
    0x4280030f01e200b014074001c4041030792140060b0b0041001c21808101031180101c40100c0141e01540c00100c2014150001d4219003070a401d016040c580c0c03070521142a60002903060005901c0441e5040501001c00c801800804150300a000c050741001c020401d0b610900f507002d003c0a8000131034404c10b40f900e0f40241030313168811341c040004c1c40d160f1410800c1d481651080410920483c1d403900c01113090410700204403110454200442840c00b000340f0551305144500f6685408140200c003000351450056600c81000765855903925819490400c003101c1c0b0061300030701c25191100c42c820200021001444000b034000b2541c0340c84298229020b409000890002003684c80045240400280c06800040c260b900c10300d08540d28041c03d0200d205e1038159032080300d005910a075902036001604200441d0800142207507910155166859000946d00c2074448070030400c0301d9020050060352001404804a0700010240110710f640f400194207464103010341480f4540d00c1d004201007026981c1164029544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 243755035 1250 243753785 243753791
    0x6060402031905091b0406050a03120504080d02030304170903060f090c1012060e040c09091e03021501060305131403070b1006080f1303080912131d0405030f030415 72
    0xa0204280c80d03421201d03850170103018003500380816140902800c016910060b2007a4000340c990344499035800c0340300c01124140201080045070003901840350000000d000c0c0c0007941d4a05051a08280c15004070201002900e000d00055891342d4001c0340558000b45449410003071030b1544040b01b41883c02c00d5552690202c18200c50801c040d40004a00102c041c1034071007040066524075021409080031500203058424484080c403401c3c0296011014050240101911403000c103031510001104400381580940c1c026000c02c10801c500d008658007401c0d6501d03090049082c0440a40c0400d020020700404494003020b2400412008000707840e015034106041002c20b0500039403075204000c50b400350030005841c5d1070000f0b011103403a102042c0103401060088032240c0003903d04a03080100a40b201c0c08500811901a800507809406800e1403500602c9845985251019041c80c0c2030402a06512031108641040080740000c015074008402143e101541d980d0741386000540c1c0343d1300781208400545 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 243756285 1250 243755035 243755041
    0x20c0f0d020718050403080c03090a060504030909150608160e030706051c02030603030a0f030b0310020a020c12070515070b0103060207020a12230a0807080c06071106060402031905 79
    0x2600003107102c02c0700c03070001c6098020446040f46605a4208481c00342c041085080420003500200c0f00842d800841c4c0c806503000d11502703503242016903074282d40c1034000420f1010144548400f40c401d000882044a052086180c54044043c1004100504034440d03818035140180c0d005026640080c008a401030039074034413544a05018115411060251a0030604d1051075880b0340c0842c800c5034020f906c010300541c2000c0002d40b0813500401c0c402c1d0340c48205900c40a40c41c1e46924200880d07140741480460142e11086402402440c0c0b1203e174540c7c03485924a603403c4551090f022031000c0680e5825a10b0b40c5120800b84001c002e02e100315980103104214100c000402d00c50954003501981d8401c4504050150f5a1929040d08020380c410141c02d902c1c1e480e101c91a040410b00300310005000c85c106582d0092480c0e1503500450300400d406032040d02c40054007907200038090150ba40c0c449114107203c6040703c4100449a0307030303c20090140d80550b80c00000f060b44032002d240b1040016501c2201401549 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 243757535 1250 243756285 243756287
    0x1e161403060105040f0e090d020318040b13051303030e0a0b04082104030906080c09180613090b06040b060c06150a050d0809010f081b09150406170106020a0c09020c0f0d 74
    0x18003c6901e407400340600a4500200c80c40401181c2f400e8820620620080c0c000100b000700802d080c04942c1da000c1400b900c40103200710036001d018440d040019048074074601c68180a401d813842400080003940050a1200c001800c01080d1a0050b130419800c40d16004890489017581c0078a503861101c140b00c090030481010351150744402a107915a490101c42c0d164913414a22501409400640c49000c2e90303007042128010004140e80f100001342001c03928079515181d0f07011121000700070340d4800586c004100d030908144c082d07032203180d0301a5041494001c2002c150b540395107000c0d00c00d1651a40665286015540b48000800035143c01040304484d8111890302d01a40c0e0310000515010426100100c1201070280207002c1c80b8a803107a411102e0303a44038050035030007588040c0032035920681c1801400700f11914107000e00040c14654a0f4403050321500342031484907100580c4103000315406046070300c001480103040ca40460702d060001684510b901400d09040c40740315041100c05104254a5079012 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 243758785 1250 243757535 243757559
    0xc01180b180c0d152d0e060609160e030d12050615040510020718020c07080307020a06030504210f0f030605031c050f031e161403060105040f 62
    0x3400d50006803410031200c002a2900c944003081031541c450002010500412a05110138090060000300041e503d60703031240404601c032849101d4404514282442d03003207880301c5d00c503100400c0030380d500400075450070100191907004001c0c03e083ca1229540600d0b1074503270190a00b05005e01c2c00030256480b051001c00000c0100f1442c1301c48951003400c0c48007003071607810034175088110340c0341d2240c40c2440c2c242860144405461101110030451045942c00035032900580074188240d020000f000d44d9801c44040402c3c50040700750030011650300100001e00c0103903101c1003030b01c04450745400c0209040d03980d401c0400b03009141001c1da4040d9004441205115030f40500c0341030002526845503103030304080c09021421034a070b9004240c3c25a01500002c1910b0f040a0950b04000070b05d8a01149401007414140103c0d40081d2240900c02135003507403070350604400100c4541d000d01c00e141c3e0254005450344000340001450162091500000400300c0c540da4894412200541403021000c0c51007547e0b84541410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 243760035 1250 243758785 243758791
    0x6070f0b0c07020901050d02031c230903070e010e0a0f06080109060506150c07032d050309270f07020f030c062703030c0f040504060602010903180b0a050c01180b 71
    0x80342952000100f11440e000d045141f00d42d0300580204205082901c8130224102c2140003101444001100e07140c0303490b501ca1f0241c0c011a50f282500351205035900c140341c502181500004804d681e040018170040300b402e01c0c19a0b20600d900c0020421407c101a000f00602c0c1c40d8000c41469402c0620400a020564100e28080c01d815030340175911b0100d400308400d15018158024049070000e100420204402c0900840c002c0f4002e410502c081210b08001103511100c000c04580c9504040750100142c6031004100600e034070000d1400d032441030400e6004425960050050900841e082d0201d0b03d114420003424035a4031042d030403a40c0d28241600301136a6031404440340e07024140c80c41a00080211803900503600f8480d0709c0015400c40e1150b801c07512858005200052044405000004040d0740d58000e210052100f9000000d0181d01350400600e111030301700108203211740c004810071002c10303000f040741d160224034a4041e841d01090704000e0f0142c200b003031103404800c045511420a21901400c6640 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 243761285 1250 243760035 243760039
    0x30525060e1e0a08030a0b1c060e06070c03030519020d06030c051009030308070e030102030a0c02011503030503060112060f0617070f200a0606080601080c01080405060606070f0b0c0702 81
    0x1203002202e0800c10b100d405402c004400342c01c140b1049000031006400f454002e4008800030568940030030100b640504d1002c0c500002e90003814541052081a11030719401c0c01c4070314003403d502e20709000c0c0034040340a100002070415a45200045c1c40e007131159103c00085103c1c1c10306540c0d074085035400002904450000744c68106d05040300180603d041c0546041200e0592900c6580d10f00d07540303040e581890001d040805118000d0015071541d5020720040d881110b8800c4000b41c80703044250002d0859040010344040e1146401c01400400d4000066035881002440c1c01c0c2c030700b000318240e000b010f40450744c40b6860500104601150050300710401e40107810622800011950780c241d8210741411a01d2080300114402d000800b18003050301d40102c0b0105400001c07900020000c1c4d507000300700c501a03400140c45400c440018003480302c003840003001a00302460700428030b05160304c48e00c0d00d606020707010f24814100051100c04220801c589680b403190020741e59890f501d05210b00074290b5001c10701c124 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 243762535 1250 243761285 243761293
    0x15050c0406110c130905030f0a090603060b03070c0816020d12080601080112200612070206010515091003060e0403020303040c0f120f05010608010603050f060901050c07030525060e 79
    0x2001c50000040c6162071000010601c410000754620113034003d0011800960b8140810880070b405890030780000c003d0101941d40b142080c0b898110000e04550258010041030b40f420010b10000c9540140d441d02401d400c0317554a507440041c581580e856012040d8001d4001074a40c0c00038003403001210120340e2140070ba4952030600ea560100441c7c10b07041c24021028820071000c0d200c2c000c68504210700442544078034000d510b106005000442c10b801140c182c800c1d0700d00b2081003003022076040c86898014807040d158030002141c8040050301da4012141000c5c00f450300c6401e20145c00744650007041c01050301c144005000d0030a428000d48a5004540a807038103020010b000a41d644406000d00480700b010510070703114800c80c3d444210b44140518140c880d90b40361100408d409100f0b1080707600440c8901d000b010000c0940c00326038100100180215203923403402080085140608007110180c40d8140707812039440c1e1281702c0860542c814086540310240f0901d44550802c600c0751b1010041d02c2000b4101c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 243763785 1250 243762535 243762557
    0x319081e0301050a1205191101200a1704120b09282003030c0a0204050a02040f0512010e0607080702011401031e020a080604030e01090e0403081315050c0406 69
    0x1540349100a100d030380c0d0850390b000002c0150005002508500754070610551700c01c905106e041200e00744007042c081c1e542e14160659402c1941e0052100c03004407240101d5035002c60800a02d0340c1e2107051607140503040ca54413000364120000d003101142e020b0300e102c05001140e03020904002c000d4031400c403450b00b520f1040d02e1100e44490b0090b5240a460a0000c105d19041c8207182e07102c100e41c0c000c0c815900807140021108102558052025100006c0840c0042110054500400040d04c0d8054440904548104070a11400c5001f1542106031003041c4ca280640420824800b07006107864844804180600c405100c402070344040168056041d960007406180c030201c42c6041440000c1c4001050800c2d070304890308040d0300030000f141c162340c00108806610390782c1e40052030600c1801c44003100000d003140143d01441d030f0044400b20240902d0009003155141c81d0307502900d505009000060304803040007070345003006508002c00d00b000c28800707010b210505040005080039001802807001290b104680 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 243765035 1250 243763785 243763837
    0x50a062405031c020307020a06030e24060d032604020f190e060a0e0f3907020f030a0302070515090a0909110d0b0a0c1715031908 57
    0xc0358065610003809800708003140100005882c119811150541c0000d0004601503a18203060382c0003420203881c04982c486407039118500305010b19030110682001c1c4018441d0341c600300d400d0b0a600180545825102441d01d04080d1348250406401840703800500c05554103007060400c4c0715010b1803090b06e000c40509541010003600c202080c2c5032800041e00c6540410081010902a0790005006022211f401d034560007032030020b460444c0c000c2e0039248070400b44806080d2700c0d01010b88943d540d400140c01c6540e81480461400c030041030315040408049600c100355a80c0d141c5440c8a54001800c81c0c21382d82551901a480740c803148070350741c407402042040c044c1c40c3c0c09410481b44040380c001e012201c514200104030001b0244017000b600c031640e00c080000c90720349642240c52031103402044014084e02c0c1580d5600e066404445980f001c000c00c40900450001606450340d4001c09100c0e03000d601000d004011910300360503003451040b95602c089050003031100d08401007100c4030f00021312906000d40520 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 243766285 1250 243765035 243765101
    0x209091615052d0c0304050a0b07020307090c050d140f0708090a1b1d040c0f030804141f18080106080d120b100e101d040b060403050a06 60
    0x100c4041182000100c1c10f405400c10b401983c001d80a490181c034610458481210360000611004e040d840000c00307120600c0c0110b030140003040e901c00c2d0346103001001d601080d1901080e1007024185900c895002030107a0181065825084001d40f04010425403000d0003c28400180c1d40c2c0f1501d0440784011843c4103119100d90762140c2c445000506201c607a03aa601c4083ca2008000c15800c074203903840108a110f00c034a044220310100c3c1103c280c03141040d082c803581195544d0310030341e0300e207850080403c0098902019281256031120400a2240d004c2010401e0f1320310307004164a40248202c0210100394100c20071060200c00101030784006503d54640500701d03009400b030540c8a601c44455281511300c00d0751005c2d0400a43c0e0710110f02e000110000c500e4070842d03a81c0e001d010805042180c4540e003440303807100c1c81c501098940854101d5844409007060b40f543d06109004580f00c1c0440b000302e44810b000c940040d5480821102c0a4a55040c817030300504c204e442d68842281c001d0400c3d4a0080c1c051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 243767535 1250 243766285 243766319
    0x61a04151a0702040e07030203060f0f0c0306060d0f060f0801110306040b0102030c0106030807022715010912060209030601051503062e020106090c0207080304150c02090916 76
    0x49486840d414811801051900e15000300e00c1424204000300041e00c0d00c0c0141e20300d85200304000c148140c11072040505228009081c0e15090341300300c0030488002010b8060940024142d2019580e9860ba40c0100b0b88610442c001c48100328189030b1411a1250181d00c890115040e60b216403140c1c03070315901c02d44c2c2a5070f10300d44c0c2408030b160140007207080791401e40c1c028195111305004403440e0011100c5110700355000d030ba2080c1c542010100d1a04107608240d411411072068422002c1c1c4004078803c10b00010750380c003400b820030b041c00da00c0b0009038990045e49040040d0803040f0454240006904c1d144001e588140480c03070180c010304000180f02c2c104201c8400c55031480ba68554259a1210103100c0d0f40d0b0b054042280b03403800801c41e0821200940046440314090b20760020480c181803c024000361441030b900b4030111350000c0420064a440030060320103480c034035400040201c2a0300340071150052410006540070007101c06103c0346081c0001c1007680d072420045142c65403566440040720402902e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 243768785 1250 243767535 243767561
    0x405100b15030610110f030703200a030c030201060f12060b10080a090203070b04060314070e03150915010b0c1203040201082710020d05010f061e020f0a061a04 70
    0x2d2000c00d889240c440c2d50503541ea8480d01c0c0841642c07000e0354481e440c04e02103d11200644d00002115420305500c041da81c01d0b800f41064031031805041443d06980d603228003407400f50811400c4118241014400c1d00040b0041ca84406401d41464270b8154200358800d480030100d900d5441d002d101c200f5420300281802c0002da5a4641c0360380b56a0301c00f8108003030044c0000407a854051140007013003c0c14040050b101500240e5800104400003c000180107540030f881d640911041c0315807410255030010b05d00c0800810940541d0345910b400700c1e072520382400601d01c1c500c0c81220324004500050810060a0720081140c11a020500c4d02da40c1060984000d0340d0217030000381d8410000d0318220960780c0030007031010700d00e10f04840303071072401c03050360a2408801e0020102c540002c0c000c4800c21060041602600c0f213042d00e03078106860603401a0494100c84000d030020032031841d41400c10740c021702c000d0a9144c0401300340c0365800071034502000284940300c1011901040c0e05128041400d152041c0c001d8a011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 243770035 1250 243768785 243768787
    0x41403062a031018020d0e12090f0103090c0e07020d0f0e10050904050c0301050a0608190c17010806071101091101140904020c03070c050d050303010905060a030b0405100b15 76
    0x8514110030660000b8903c0101030a031000c00984850a181032003810815814010380303410101100400742c90290310640801c0d4001d126655000d4540740851704a040200c50b65001102c160303006070f025141c5850040c1c110120f0000020b4041c6030710410a11443c107c1d401c2c0c4200d00c44044040d12200c103552104000250214a104018102802d0410141d55a42801c41c1800207200008050303030011100240c608601000411545c184020300e20060f0541c0e08080003640390410389801400c20300c60070502c5d12602c40088401207409a5403030301c248c0603420700000d000d40c2c50710505039803601c0030307102c2d0000100c0b0104590b4441406100c3c0c1030140c3e80c412201d0418684800c0111010002041d0203030f01101c04000d80c6030240e485100602c8d107159240e024684a02490828807031601c0540d03c002d028009241c2402c002480210449042d100030000005d05501c9450103d4140356240e0001058606418140030912400281c10320594440700b106010b0352a509042c0300840b40601904100840 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 243771285 1250 243770035 243770101
    0xc1403040c050108181915020703021504020d0b09031210050f041a040f0e100c0504030b0c1b0115050a08100519090309030c050406030b04030516020604140306 70
    0x220540c00380740c10000321484000f84c1c1e02003060700c03410300304182c82d503150382e001b40840c1304104280c2e40b80b1100281a900003c5061603880d80f0081d456107400c1c58010703480d2821000040440d1b48401d07003c0307942038011a130240c1503d44580007079580e41c01101b07204048882200021420b480001030b04c0191030018013051303600b001c42400d120241c0314081409400c8180342d5484401c9488610446d20031001c2200003145200e4000c15540c20804000350b03032100f80e400c10ba429241d80360450f00700d908482c0d000d4041015079566038002c00d01805860750500102c3c1a410940c02400c02c150007178a4459504002c941c9002e40d1101003103000011131103400700d103801c045400c40c0981500c3d40b040d980700c03201c03080e4020000ca60a6500d02210100b43e4110086050690103209000c406900300c00a800300381d404001c0d80c0c1c1940c54038455580010001000c11000007411000c0d154818800540b69a01604294803580c6503020306c1890380090140c20701900c5050001490040034254500104110b442880c002d85 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 243772535 1250 243771285 243771287
    0x150702040b130e07170705060702060c03070204060b04080d0e03100b010c120f080109020c0a290109050114040b0a090b1518010806010c05060601030f0f09060c1403040c0501 76
    0xc0780301848190b104511074440b10003089140288400800c043c1e0260440c6410800c1c9141d00005902071040c0f56880540144040c1e156641150b50745501115030300c0e114000210303512328612030400c0c0290014204840003500d01c041501400543e082030342902c0e240640d102d804c560610710006920782c140d000040c0c041400d42a94000d045400040c506294606415224452901720000004000441035000d0707000c6036900c020118050701e424602545440c58212015540d035500b140068100350101c004c0180c1c8a002200c400601005070070380410540c0c0d91107220001300024401e0a5144005a81d120480c0c6010710070303529061802000d2400300d50800c03010074010460500c00503008400324404000030b145403030162640190a090050030116101c0c001800004042c0010b03051100d01c1141c00c0000c0e6000c9040c6620690030300e030000361610741d2894100588820f03030312214400d151185160030311400d40c00c0103244078542c0e2652504008a01d030300c2d8249110464001d484113a281409209035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 243773785 1250 243772535 243772541
    0x60815010e03010b0603011419030b04240e150a0b0d120302040e0406050703110403080a030c021009051b06030603030a03180c0806040c050a081b12060915010515070204 74
    0x10910150000440307104d50b2010807040d5000782c100207521040d1180c817041c0c07440d00382844d0078543d02e85234003000c25070301e0750790b800361503041c0038100902070080410144c54000c2007805511110814100c1484521808035000ba02c2c0d04d1200c0011061201c4040001d200c10680d00a1000640000e066442003860545440c200b6605050002080540070040040c0f09a80341e40e0b0140110700400e40040c03039040070f410150071510b060141c4c0c01116424001000418064002c3c0c418600d080d080204a190f10000c08905005207048004c9040b45070404039001c0c08000503244a4410b840801d81c4159482e0700100201c07400b04031417140e81030340708202c140c6a00d0300c69003020307803401c012018005c40f4010940d00c0d00c8034203849030404070140c2c0c841c00401c01802000d190800081105446210714076040442c05500c1d00c80301c0d120203412040f890704021064070344140141d10700340e114007903507858207002c54140e8a58268258041c01410103400105241c90551040118100a21141031604000b82e0174000a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 243775035 1250 243773785 243773807
    0x1f02090301020909040318051c030e030c0a06051206030106080703030c0c0504090812060405060934081609051003052203020601260a0f020a0810060f06081501 70
    0xd55002d100b07040a9813641d11000e40690b00c01d465504000c48507070b107080d00d00021640414030447d06800f40c2000401e004441c0d54610750580380042e0740c5144c032004a4603103034004d44425005079500000107145a03025001c2d040c1c20f4482c03078003402c854891808050990304580200d0344503070489402000080d01650602900700e1164040202d4103a0310800030301141d4411005a6000b40005000000c1c00d042c03001107503001d0421030701003040f402c1500208100305d00080606a4407001c901141145e02256a401141a00c0c0155070f42c404001e0f644d4024181003094400c40d24a21540c609010010700a001f84000c0d41e4014003480c81000004004401500c805000c0c030f9556004c1c140c2c5c1858200c01d0080c07a11b05240250001c03c00340d450a40400c3e1043c0010700c64102075610341ca4a9403924102055030501305404c01021103500d0310b940006a00c000203a0f021400600c80c14040707040000d0702c1c0e0800022a1313500c0b4225000c1c0c3e80e90341403d5510f00412251424a080341f4100311109e5809580d1443e6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 243776285 1250 243775035 243775039
    0x10090506030c0d0c0f06050a0908012a03020f0313030f051204030810080f0124241701030f02090f0403020d120612060914030412060504050102120c0901111f0209 71
    0x3e21107541710350380f1050b080940c00c01130000381c000a0300c01403103800080c1440101580402080319003c14035404250720654030980140e0f40c00c1000c0c152086100b038050b201c0d2183c00f2148641da9050a20f442010381c0102c00c0100d0125000242e81802c03180a801035426030100d0b03a090f100f960340c031541c0803140c202d801040c80030803124140011034200000c110088110310000c000113980002d44c40c00040c100d401c1d00030241c5403210818280100c10600b503078496035061001009060040484055179907e042c440c1c00184070400d50000010b11440702c0c3e082d42618000d0792004c140d03850390b00903616450710856014000d64020302010082c3c0b4804d6084002442c01c1480002d171a80d00c986044070302100c000400d070f40300c5032034a40070000e0041151400740010200f4004524103850444842d40b031000340103000e400d003540c2c1c00014051040a40446000300078480c06010f2500c0c0030218580690005405180020b41c1c14202d129151000181c8240141d445401042869504800c12000e588a04141a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 243777535 1250 243776285 243776303
    0x40504051e01110c0102071b05030c010513170d12020f090d1704090f0509070302090609070c060906050403020c0102070f0510021c0804021512040204090204020c1510090506030c0d 79
    0x1071049215600900302d0014134a00150351240c850900002d402141c408a210a0107034003010402650000380c010540542030800c95200e01d00480400c1c40340040c6d03840810800c1060380768010b40400071a010600d8042d9880d8001e01001503401107040b4081e48d60244114102004102202c1c905400200086c510406407004000000d09103401181c01580c00ad8180b203803203441103442001c05d8003900758040704c0d64000300b040703518680002d00c10301d501401103401041140007052149126003140e443d2070b500301a041c8007800c40b91805000034002100d0540060149903c078285962010864108986201450615560504041200201e04415520203506c10312964032000003001c0c0b845001c0740d0381034a4402c803a241900501884440c60004a04510810016041c440d0161321216401540554000510000c00d1020900a11407400e4201051007401030003001542e80316a441d2046c400404c1d040e00141c0d49118003000d44d001074500a03414bc00100c24690b140c2451030419044030302400800c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 243778785 1250 243777535 243777551
    0xb03060402091008061203070b04081b0d09030606350a0c030c0611060150011b0f02040203040f0b0f07081005010c062f0414040504051e01 61
    0x78a140c024052400007140c901e80401805d880c00b10340451421402801851030010603564480380000c0040004122040c0404c8840e42c500d144440f401500310100e04452070030880341f0340900040c12600c0115a203505020001c200c03135501d410030b46d50031044001d20506140140d502c800038031113a88641c02c00c0d4806d004440740490007607401e08004600580c2084449070030282c0003052844102200001a80400010001c4201c040040c00e4041320b40307090402040114540301e44042280c0c00c0c44030a19584480304001100445241810000d0903200c10300020b10f074601c070300c06081c0540005850950861641340141c2000d40042d548103106200301e03e8400d9580d903880c25007240a40e100b00c1d030101e112041060740c940040d03410781c100810755001044149410002001c1d01c070900380c000c2003144c4446998640c01084107440b50310001880d400490b0040142d0b034108150000d101d41c2c50300c042600700d030170003a08182c8120360007650400003601b00c1e0000c0200d41030140180d04070f0810199a9001c00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 243780035 1250 243778785 243778789
    0x120f02100f06030b0708070f0c0201020c040f1d0c0d020f0a0801021c0c0e0f0f0109080d210509031209070308120f15010f0f11100b180106090b0306040209 68
    0x240d2041002222000480b142941080825540000c00304414400c041040c00f0210340c00042c034a0000e03a991900b0b01c0069401c0c40101d0604504c0141c11b50001e00706204204da210013500881542075084c030203058040c0c1e90b80440c0e59226490103040360071005442e1300801508000170b0203042105e01902c03041301140d60b4180b003422039204282c00046041e40500503091350205020307844100300c1500d0b1808103c2e0001c1c4c00200416280800309105402d00d400c1040030703900941644004240103416910440611503010380030303e01101e1203072541c47c0c45898020441a00d4480d05000d150b4100086041c51403001060001c11400340841415105140b400000501248000c0801d1032001c100d040240c2405e140700b511181e400741992075044000503404e4003a0f6400071055080c4409481c0c1071860a05001c01034030011084c0c0c64a043c24010008504001c01164210f03240340141a94841d89031a6810110548600c0a01a07040024080081041844180e0700a9900140000d000600d06012400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 243781285 1250 243780035 243780041
    0x60409020d1b0806010f080903180f030609210304080a0e0111010c020c150a08072006090c0a15080c091206191505030c060c01090813080106050607120f0210 69
    0xb4581c0c00081c00706040003559640b12042000034206400c08a10b20b041400700582c49004d00c0840156540340c0c4c82c2409256900c04040010488014050712070b0742c20807150054503284058205400441d181d0f000490b074122800840781300d0b54010082c2401d08001590484103440402c140318100980003070f50180140080c031801c90110420f80060209030410020300103403601d100741595940d00c0138401c02441076040030700e00e507001368545020540c0c0445c04080b607000c80310182040025201703400c00c120350b900300003856880e10102120490929a924903615182548039100100001c0702c40010584040240300075050300c0c00010444002035030500341080c03502000b120900002c100c410700440315400c3c2d81c420a0651000100400c2032107042c05c000c29941c09104405501424001034280d40d004004c0d84880b030250740c0b1040c205c0d03403905070544610410000c0c1c0100f1006510f403900011b82842d1001c2100d500c15442080c2e01e1442a4004042e41c400d080e02c4c1c80c1a003507003d061050201c540481c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 243782535 1250 243781285 243781331
    0x303040302060f0d06050a03030c0303050c0f070809090c09010903080307051903020a2a02090c040306110a0f090617090c100201060e2d1b0a030203010e100302060409020d 75
    0x2020f200d88903050420b4400950788150b03c0310b40240c40300382d010710110782d112008090700d64041c200400c0325182c01e0a40d0106102c1e107803656180c05004039504080100d014000c06400d242251540c03200d0b2640e1018002d144207000b01d040c04034004141c02c000141c0d03c0c83c051a80030fa654149a8100702e03003254600c3c607410140107482d0010b680061060800c0d508180203039002e00e00809110a400601c10020480d201840c002a109012190004400d2040801243c1c00743d41e00003000e01c2031804810128205400102d03520340410740c0000884100d40c49034200c90101d80b0035998107800072940341c100c0c07194000041c140c05118000c0404840503519100d034850342d14255940001251407405c2c0101070805c4000c1e021184c1041c1c054030580300d88840c2c5d42d070171200d280ca646400d88035489007182c140f501004580c5030402c1030700c04a23040200540581c06903048030000042c404455680403642c400000041c08002d50000081c00103200321941a4040c002c4511010400070b01e88111002102c00260a2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 243783785 1250 243782535 243782557
    0x7050706090c050108091b0d0203030903031201030213090309060e040b04050906011d2505041a03060a0506070b0c1b061306060f0b16030504120b06010f020f0601090506030304030206 80
    0x580c1c400c00c00fa5030300822056101050f400030300600947c40550b000718603550a40544034180c14504c040079541c05208441c3c1580e40282120743c2e81b9400c1481d211010000d11059102ea0a40e240315800d4960a010b90034042d54180da40600480c10400e06450195400200e180c0260352041b540c3d2041d22a40f0035907014071580002445190316000c46010040e214541d0103607001c891000303001d09080c054101c0e44000e00812594901100114402c41d182c2c0100d52003e03880d044801c02c40f454100e403460086018403010b071140c0a40a40740c0e024011188900000100740e031062000088410fa9000058132440860070310860075491203d0415140c01010340c1c1b4000c150882c4604031081102d60300c07d800003019501c40d55090246080c0300401907004210b00d03240c0ca881710f11000302c1014403500440d0060b1074038056801c441d04603070904d80ea5152040b1581400b00700144200c0c52500d00020301c06541020100050485a0a042079440500400792100350940b0061001000590b9044040d0031100c00b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 243785035 1250 243783785 243783803
    0xf0304110402070606090c02070807030b07020a080a08190501081b1201020c0105090c0909031c020f0703020d12020301050d2d0b0a050c03060117130203190201020705060306090f0705070609 83
    0x2042116000c640510887c14290b6120b000e0801492402144400c00c6a421850b95202e07966244020380c1089180c490041c540c080c0050100c9000b600814118046c80c0300089290240daa24100b00040710402c1c0142c0311704d0381c0441a051444008003840101d070102c043e0103a6200030102060500360b030050720394080b06035118010401010410008440020022a40210b00b030030000002034603482200d07240e403992100d4038002c1c200341d0360703e40496003000310303840c04640e0710001402c009454020207804040025846400103400e1107a9000b502e050380c800610a4103000400c1e95502080c0c0541a4084010750340d0010001c1040145036581e4a000d028810b10704142c58a0000c12040b120003c001840c001c00078801d00c01181d03800100100c4101c001446c0e40c156444941d41e4048440310020003c0d03041c0304d8902c0c00215046480c041c840418403e8086070001503d4000f0010113002c11540c41e60058a0403001070402d241d0310420396000710b031a0a09a140001c1521808143c0d04905070681c0e030915 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 243786285 1250 243785035 243785039
    0xe090c130617120306010c06060f030b04060c02060105030d39120207060c02012a1203060801090807080f270f030102030907063005091e030f0304110402070606 70
    0x82007240502ca03241005000240c9080c0f1498150f030201400b0581045000310702541046441e52086010301074450b0700021069032483c100700c0e5071100729021108a4240100705007582d00000c2d031141694001005000341e42141d034000c07206c078081d4002e0901c1c1c4440301703d0f00b100c50b600c0803100e0b20400d03071001d21117050f40142410459109000010508115072285108000e07440c1d005c04140303059a82480c2c0106904204808503200608181044d0280000d0061541c100320880c1d0100a6850311520b0900c2070f9541c41c0400ca00300c80c081c560142c01c0d502c0c104008000591220018407403003221101c150309100c0140c0c440d50f00c1d0800c0c1d4895404240380034003c4126072901081550071584109c000b50303d9850003420040d00c4040034406c1000b07000307800810440781c109a05500140f5040c0c41c04002401071007e1410f805018103444110240c001d07900348000003068940c51080e500c0041d0025890400716540000c619840180b05803010246131900c16455902d50006000c602d000329000705080f8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 243787535 1250 243786285 243786299
    0x20d080d1d0109060b0d050c0607110913030807090303120e0106080f0c0f060a05090f040e010c0c06141003030e0f060705030901140301050f0402030a02090913030f02160e090c1306 79
    0x10310b03445c2125105c0c00100c2503c038005803000400302c240b0300068402075101c015a15003800a201c18111207540304007102e04012080b0b000e00403040340e440c02981c420071203450706502601c6070301e0347d4007010300004c045007003105418556400c00d414120b03001d0000100b0903038400b201e905112810701c60719038540052811003414580702007211441041100c040f4a003c0038180041c040748550100d42e4065101c81054100d640c3d1190701030688110050700034030500010000042c024801d0708400c445562600c805030100004480c02684a81c0321140100310590561701e0a4603d046800809944400c031000c1c0411542c03a160003900304148103400139a11060310300300240501034094540d49400d28140f0040000d03546507803a03001e00c01070a036401a940d445240121001c0d10994407010b41208489091203255610705900e001c84501940e09d4041201c2450f82c126155000d142145803059600041400000030300518980c105240000b00c4d20710011001c085080440c403620414822962448100111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 243788785 1250 243787535 243787541
    0x9120d081f05060703180306020d0e06011406090603090a0c0609080c0f01020c0409030c0f08040e1501080601031d0a060501080f0c060f03100f030803150d020d080d1d010906 76
    0x10726801004101100d003081d0120707025004030000030b010048418400b45007402c1d0f0403001c1c8091504001e0940d0380704a6082c01d41d011b4608101c030029588603000000030785428007113070364810840052041d450104e00508009050f080a0100e007440c0c090740c0500e10028060350000340003042603442d03441c241c0d0b1401d00ba041c203043c142d80e0040d0081145510045e0282c0c4d01207091003407070304210381c002364010060030b00711254510100c008018400200d540c90500c03050902600c125586070002085558914440c6045141c4e0880c01d0b501050300c4c0c001281e07543d8001d8020341ca00b58480141c0400e4150f10340040c610b0700d860088140c400590715401402001c800703025064015841a00078995802d406011611510400780007104100010002c56a42c81c244100c03803008082402409929948a0804446642c0281c540b5501d1143c07801b208411410800706494400b42c000780340c405407070306a4550001952042c124060f203c1e44c3c0e140813591480d81524040c00c0424514000100708405151520803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 243790035 1250 243788785 243788821
    0x7110a05090f010e1b03010f0807060c080d1a0d0303090606050307080318041805010e15130b0c0d020a021b030106180c020703060e060709050a1203030209120d08 71
    0x4500c40002c0046000103181c0d06030448180848404541c0d48a003801602c0b289001e40f00c80d0303000000070000a411221601030815038404070241d800c8150744500a48000110300002401a40140000403c00d64540d102c07803a032404207001a00408500000114008030303c54084010075070b20070842c01806150300c0303640003410041d4002e055440c18100091f64a0251600d111041c525100960101d511580c21101604603c010801b52401c41c0c0c1c90050f001c2d1100c1102c0030200d10600003c000d690380300d80d111501960510700303607080000140c2c03101c0100110017480c91401c5401000041500b40c07052000300505002580038061040713400c4010501c0710b038920700c503610a031304101d01805000507650340030541891180380040c4611400000f42e04007541680090040342c0703006582111000d010900c0d80c400c9100e5642d0b40e40054543e4200308092116010300b085039002019002c00280c003035030040c00b110600a1a0f5071380b41e086c022000c1d00d002040210b81d070018003a9024420100b20b2048080c007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 243791285 1250 243790035 243790039
    0x120501060b031b03040f05070305030406030c020d140a090f14151809101d180a08030604090809090703090b090106050108060f1212090a080c060a080c04080307110a05 73
    0x807540c204071002e5000025150280034030383d500000854104071a011305050065070000a072141c82d9503e06090b42c80b42c000348640e1001c24208605813041601c00300d82c1086070152030302d407400700c511280b1509009400440c030810074802d002001195035400401d442001780600985110a030070604244049075a0821006480a0b824440106a028852071807032401c10b0035101d9000f01e5803000750f00700751b034030f00c0f0f42c00005c6901d107121003030320006000c02d482403085402580e484090b007601081566900828000580300745402d20102c0c40f11b24168000345a0f050080d042e903414800507000080030688d0a40c1d070070001c01c2d580c06c034003002c1010403545036030b1000c3d40300000c20001340f8001c0041e012a20040c421803003400d000e4000032165480000d066070540815003111809107001d0000c104580c000c1000921a0b28000d000040480300080c5940382c0ea84c0103070105042c401406c0d000d5a0f58880504054400002800046200b4a08001401c41c040c0981c111088844219043c4051008150003a074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 243792535 1250 243791285 243791287
    0x90203040b0406181e031e082412060f0c0711100c0609030807230414010e031006030b010b160f02040e071415190507020406050a120501060b 62
    0x202065144031401c2d40309800c40000300e41e00c41051109440d5440c5401c0080070728091307010040c101c0c4c1c000346903c0d0303682e440b0307465506070f80c10003076020348800305d01080010014052000240c41101000c0309165102c0140d1010000a000c00002030340080129415000540c00300b01005005d900c8005c11542280c030280126184c1303400b91700c4142c18042a8013840780108164100300d58032500c107a01800c11780390088420041a030240c9070040144600380d070b06000044400e00b00a4542c0c207900300804400d421007040c1e503d0645048000b4482220440301641030240e1204009040d4805100b1054094004100000e4007400d510f401402c403001a000b82d00320020600c0f41d591140344542029a0061300b01c50740f504000254070004003d000007070100a50f034011072200003020385c1042050b00c56040100ca01c1c039014076031034400c020913004001d204201c0c103d403150a44413040c003801c01001000c0c0007510204009441e01c011402d100d40c0740c1e101d104030001144824041c04020f100711400f400740e0703034407607 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 243793785 1250 243792535 243792541
    0x4050c0108240105130305030d06080303092d03040608010e0c0f0406081302061908150307060c031205010f0305011b080a1d0105090a0201120c050307050c1f0f06090203 74
    0x41116241842c10035000b02406400c006156809581030b42c40340390302c84404580641d103d00e090b0b501c0f0781160041d006801e00b0040089407100000c405e503441890400c00504101c0300d0840e540d40f58059242c60382c00d81c065540142070340203c0c140003d2018045c40e032034070006541340c07030400c031210310000300044a0502c2c2408040700c5090020201d4040742c000b854803040507122400f1000c882c1e1030041c2c000b9407006c4000fa1407895150350200030703034205019440c6d1542c180e039029040c000d00414000d5066040c0c1004c101444000c0c02079010028040c0203150141c00c8a440d900341d00d080360342c20f8211060a80c41c040c410820090240294648403184081602c2402c00d803090141102c3c1001c0c01901c049900e035401c46880c0c030348a4042c042c000f2511002804603003009a0707049d44170000d2180aa0004480800794400010180110f104c1d6500030b0ba5403d00d03544c0c2d0603100300c40d20703009048426224024144240ba852400d11a03504186818040000340413a09010140845110b036100d14900c034018410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 243795035 1250 243793785 243793801
    0x1507050609062a030117010e1e010614060910140403050a0212160b180405010b09190303020c04090303020d14010609080c0109030204020c1213180608030702011d060d020304050c0108 80
    0x1074038119284c6e4080c2e07001c42c0350500800d03800b616085400901910618071985072480910180a07030042c0703400001c001540e102c5e038071260986040441240c00034130070000e8500f01d0400010b5488843c8503807a14081610241d40c25840380e6000b035000750f685030300031344155081d0318051a03103a00351140240100a4007805583d40c0c00c11032074070722903100e10b02c0c00070030100922410303d2007007040100000c004000d950b842d200d250300c96403c00c1208600426004400403000d16407824803d0a80b0741640003400490941410400a41309161048080503024000c050804005000359001d44107009504001da6040c0380c8000d003204d40641c0041d50550240d00404c0940e608048145c0c00e5980544d005070b512808189210b1802d40403e00b4800c1405d000035841c2c0011005c92806010b0300c4100c400b40c017140e85910325442c261074250281400790f03002080420300541c003980d4851040e2260602200551404000261541d0809500074076002e4000003044100407042c0550140420242400d101b2400c2500b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 243796285 1250 243795035 243795037
    0xc240b042304140a06050108070b070b01090504020604090501061e020c0a1e0b0c0604060b030a020906210607030b01021005160807051c0608010c0804111507050609062a 74
    0x62000d00401ca2011500340411084050851a428021940c010314140707061802000248034800887c0a0300c000840e80e10120400c45500580080c59250642d0030038880100400015108036440001000001581c00b00c1e4020540200302c00d0700c44100e201480101031444002140d02102150400c0540d1a03181d5642d0039000140d4801d400da50040000d85100d65440300703820380000207001d6010071b605030800c00c00203c0c2c03841035204a5050142081c070b8800c3c5540c1c0d61044600a5001080400081181c01d080720b03204220001c100034a8035060010544a04107030007a1181400684c40c0e904822503943c040041c25504403e00d03008010b68034010583c221070510950060b010090080040785580e880780e415160980d80300443d0490345261550128018135151059403800d5081c0b1504e040594007802d0700511a5401c4104e000712040307074108021000c0a24580e401c180181404144081201000f0041c42024500d0082080b420321100e8481f04885280045400301e896161001082580c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 243797535 1250 243796285 243796331
    0x810151208220f08030304080a031814071406041d070903140604061103070207060f0311040e1f080d0e1c2d031d010c240b04 55
    0x140c04194420890310303121030703a44100b0320307101c03000804101410001c00700d80b030015088030080d0040c640d4041c0e8410329103440707000444016180305c0d018042c0000c00b50183d000000064032582c10400100f504d5510001e400d0880d1808200e55400f030030090140c81c404102d1110b070b0860403546541018079281c1d000442038000c40f8001c24816440003c104e43d60302684801c030107150b100c811400d08000240d0754039034494041b2415a01a400c0c014550314070b00340700c0c0841e07000700301c16406411100d0900380f00b81c980d034459035103e03010150365410314080b0054400180c00030708840e00c8a000142000500c01482030809020305c8009099071400300320b140c1c0009403800d003104181c1010b01e6195502400202104420520a90032043d208a01c40400240c0d030400d48182c220021407101900c0c1d600303100fa00c02c5000f0309009000c5500180c1002200802140c00110718005141c10184008290f84103044402d44404906c0d4241c0b5104c50300602c101c0500030700c421a103003658104002641c4013210462a02d401e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 243798785 1250 243797535 243797549
    0x4051501141e010e06040303031b0509010e28091509020f1e120a02070311010b0f0415080f0a0b0c092b05031909080a02090403050a2106081015 63
    0x5070111030b6074020642002e404030014201030721107070703a07081c06405821401705510b82402014010415a401607058600076030040e0768103401c48105400b400400302c0d42048c801017030b04103003105001e00c103000a04280a85075004012942c10002020f420036291144c103c01a9140103002c1107892440310740a803001311418984401c5180d03c0c0c40152031151140132601d034030204031181044003400040e0010300c000d5200f0340d900741d81e02c5500303c0c102d8201d4207d0003205a01c000e00c032545015a00c3c0942200003600e03107405052500969464205180c10020704414106810080404c0d06000c00150a076520040b0a8815841d0900380400204100c40414454a03515804005902010303120808443d2003a804000c0307030713602c00c502413a2041c414a6041000001484940c01042d43c00000c40d400c0320705507014251507003640710b80c0d0342915144c100d220610204a000791410800d9861004107003c03001e03204600140090a2440c5281406034803002ca200990a0a00c1c0c03011401c1000c0050040320b9070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 243800035 1250 243798785 243798829
    0x1d1207031b1502040b040501080a0c1d030c120d0809010204080703020409081201060e03010e0f03030708040f0804030b0703060603020a0903020415031b0e071d010c0f06050405150114 80
    0x6a07203080c0c1c0b40400400c2d00d811080d4408a404250340f458007009000ba1a401d81ba1110b0740c2d511500076406a41181d504071002402036000403152009940203d58406801026038505081c6000800d40c01a00520849819401100188506504200316940000b940c000075441d290511803616601c500a01c00240201e5403a00518140100301e820f0f44e51268129504982c02c1d65201d1004050300e0302051910300c25443d01130a80c00c0c0040024012038450030000117103095a4a200c030a44003454000d109450103101040340760700280520300204080c5201d07510071941806c01d03480080807640d0070b400c940c00b498810400762440a801c0f5200e082100d0f81103401240301c1185429804050b08594001800f40d5245255a002d0181c01820603040c0c812265039849581d41d070740e000300d6a40081186c4111f09994072050020301d5481010761400c80c07030050300074001c5110300d50340315000c84808440c1a6150b422003840d0400c0d4201080080e4010801e0401c490f4104400340c0001e4942d000c40a140a01054 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 243801285 1250 243800035 243800087
    0x1f0305120f0f03090109110f0306010e0901020f070308090c0d020603040212010b0402041202030c0301050106080a090507050603040f0606062f071e090501091a0d11041d120703 77
    0x8008088452209040d810a603c90802c400039a020b001c003407004940c10241942120b110742000148a00d44200090061006900c0d0030f220350891900a0301c00e0000c0d540802c058011881031000030080c40b442550f13402c07214540b07a0106030402002d04200c80c0700e031420f940500c01580d90402901d80103034044510640403d18185014010213100c4c41c0e168003d800440c00241c4d20303081040d00c0048030300907800d031050810508105400c0342e009001d0800810702060100d103101c0710316880080c0031031080046071103154031240003c2580d042110221903200c203099001041017014001c01c80201a41e043c040c904540d2031181e458501d1010000031691070f0682d101541011080010030002c10b58074090001d8040e02d0b401403c500700740c80c041c0c0c0550780d06200001640e80264840c0c03040385080001a45640c030a2101040304015140c0780a44400100130100701c0d256232030748a120641135920300c0071320411556080d12030a10640b8102250110800d1289801083d008805030078000ca490315080304810f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 243802535 1250 243801285 243801307
    0xa05010f0509280302041401080712080f0403150f05010303080c0a0c02060f030f07090b0d09062913270f06020301140109092018181f030512 62
    0x301e664019242d00102c50320850000034009810700044d40d00a9406000e0040100010b40b48080c0a114440c0b0315481070004101c07040b52a00111134007817041042c01e2802c0c128428105064005030400d5405403081c1c03e003914040ae142c40707201d1011000705001d0010350b1450320003502101000304407400e42c0f0700015110004030b11078080c00048990080c4615100d5000c225041c046420440d40c03005010791020100d05000d00507551705040700d0740500d58600d000740c0c8000b000701070040d021088030500c1c3c444445501d001d4021207100201da041c0c500030070010108804116201c5a525044ca620525100c0402c0003900c2030700101c0030903011960203025004a600d011107200513851405005148040004180000c541c0c052486102003603076100a5181c272180b010046610b242c0c01c0f02900c1066100c280142a40c803400f40503449240c4400c5818803104501082c0071103130715031070303142900d560404202d00403030907141c6005200894940c0d03080003800c0d41c0c1c6251760b8200320b03501c807500c040000c55802154 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 243803785 1250 243802535 243802549
    0xe0304080106090902030c030f0a030309080f0d0b1e0904080703140a05030405010c050a0507030f050405040e0304030221060114030a060e01050709081f0b03030c030406090e060a05010f0509 83
    0x51203150020800a0340c1c40c10300308000c14048808910a0003601204080341c0f400203407040d6a038111b400500440c10341c8c0e540a900400c082c03c81143d60410501981c91f0032001d080181518641c9001d0100b2081c1c098420840900050300341203510003042c2800c404551140c6504952156019903200c0e41d46641d401c6c141c4041c01a00d207001800000001c0701140c0319406000b40d80994800e000038014040c1501041c0e54034051025070300c1c0022400c1c040900403c0c8900800c1d8281559401c080d40381c1511400443c2c1030f180c44030820981d0b60700000c0d0170421410501c04041d05078a504200311302c42da882c04c0e802071300d0b04018441c00103c6a00c8ac0030b184000da601740544182c5690001c010480c0b072001e084650701030401191000040381e6400c0b00021082e20110324060f042501ca9140400c01c540a000b040007400404000303600740c4401d002201040c0010001800506199217039180584e02d4079030702d200e008000902040c040c0038058000c01144c5d800008000140321581811078a406598011a803c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 243805035 1250 243803785 243803789
    0x1903030b060717040e06090402130b010309080c0d0212030603070e2d06090703050c19050c01061e140105030115031e06080f03090904020907110111040501090905040f03030e0304 78
    0xd420036006403000f16941000040088550f0309260b84a1039840804000302030000b1500a90401200d601e2480300c03483d658880214200141000a01e42c002c40d1240017941d040781c2a0b20360b813580031410849000d80c042160b8040c0420f403c108078070b940742620119885000a10541c000c840d48038007c070389420500a007841c0c00228025000c2d0994030200307110034420100307039038050142c0040b001007200c0900c2405903034480c0750840961445c0070420984030000c004191090707810840248040118a1028010800180551008059810f0122107440450185903000c085c41d481010110a05641c125050700d044811078510442801d0140e00190080d00e84008010710610408070340c400d02e1022a0700100c140d0380602e0489a0300d0030500c1c129030f40c0348603000e1095805040e0100040052501548091340703c40e1074a00019a42c408000d8542590f0444080104111020406111559200729214002c1002c1142800743d801c1613100c240910004020150800d515951300c1118400c04204844c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 243806285 1250 243805035 243805043
    0x32802150d020c1c08040f230604050f0606090f010603050a020405220c030908030f043f050703170624130b03190c0306150806030f1903030b0607 64
    0x143c1d400d00640d51640302c41220314a00112100c0000400d0480e108101081c4101d07880420840800300c540c44000d01c201d0240510b42c80ba403110640d056644005100c01030081d80705800400546110340c0c060350410000034407050040e0101820000c100341d11503601e60440b0014200003540c1d46400011602a104a0700595001128030700081050716104c0c04160403c003801008212400000e04102c054451031400504586018404030b000c80e050041030036000362007a240c200140b000b081030f840c0390b05079402010300c841030903881010240925504240c416003007440c04525008280da006040384041c0c40065802600050000380d030b075140c000f0048415000f4a903944001001c01040c05040c0e80f002241c034614a88019001445140d49403e40380181d0400d8142c1c564600005a61401484990910030825880300d40000e1002e120740107580100318550b0324041149442414140f500c108c1c801210195800b02d4004441544400324025082c1ea1529010038042c0c1c0c120005040b40c0030f1090007034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 243807535 1250 243806285 243806287
    0x5090604030c030201180b04030201050c191d0a0f17030307090909020d020301020c100f0c0905061804290315010b0702010215010902090112020307080c22090b032802150d02 76
    0x40c0910503030b1f1640900c21352090740203001c03d69841d54604914000c408201402280c0c1d0700c01c0344440e60240c40c0c888903160140003007654103640c046c0002c291910039481280645032104003401362001d20034140f072251f460940214514140b840004000341c14a115148001d90307645d00306011580d5400c203010503142c00038029505c410a0f83d10281c0c0700c0c510303c0b4004880c58500500c3d005800d02c0c1c3e0040c058035803860f844260382203181c84144a21580a20703040c584c1d50411005581080d0383d2481154081e842000c0039a40a4040880e00b040b0b0011040086110340d216070001c0489000c4220b00790305580b0031515041d290606840184d04d02400161410b28010152001061000e220303800f40480c12400d130394000c00c00200b10101c90482c40300b520f001b0001491003000900351007516000f01251a194214070446a18481f5800a80c004c1e50f048100940e40312004288246400c10458508005400310010440c0081210321450030840e9030082c094004913043d2200007003842d099495000c01c1c0300081d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 243808785 1250 243807535 243807581
    0x10b0306090c01030b090f0a02130819060501060c0203061b071e0c0b0418051b0a02151008060a0504030512070c02031c0c141c090503060a05090604030c030201 70
    0x2103403107200000d00c1c0c5001920f03003d5645c0c01e510300003260078028401580d56070001e40b14101144081e621180c020000c60713500040c000b03152071003000214544030030783e1000a030b56590391400009854060b4480300402445250740310140c1c0c0e000c02e256030000c0c50140030f141044010f14a610440c05015006000c0103200e000d00007e1030320076410052200c0c030072024002d00700e44a880c84640c83c01b40f406441c00751456082003100382c44e020f034480e5401003084402d00010321032555081006a00282184005801c41960000a0001e40c0f0101da001003081f203804100340c4c18400e0956546800500c03810345a82c5071400b01f4240b50103042205c44012400607120002e20704000301600c8254441d000302c1c0203101d141c00d44a4443d000001315829080c19035a09014100c00d6100c001d05500d5588000c0d510340038003a03c2c4207014401c0780344a43d03100e840da03e8407030f000c901d454100741c280580200034544c068180b804006401c500410616441039040c1441c000c2c690032801d08900501c00e5102c034840444c44c280c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 243810035 1250 243808785 243808801
    0xc0e04091a0a1512050d0302070c14060d020a0e010e0114070204050604020d0c0203041505070c0e100b0309280c0303051803060708061f050f0a2f0f060c0405040c02010b0306 76
    0x20080c0f00350700650031246d010307000040071012841034420203001c60088800901000d010000f000540c61001071000d4102181e01c03110300200d038402003112000c500a0005c441055800181c42d04504c1800d08041c1503800008414005e5441040c400a114942d01d100080c40c955655058924844a0b81c90070400c2c82d441c50320295803680540208100090400e2518056034410021215001d070b008400d0704c0c165181000e00d8403013007405040f2100d60821400045154210030700a50300c105900d10041440301c07460700c01518101c00100809130400320615003500814a045030702d4007144d47c14070b4500e80e111103800814a01c040c0c41c5428a5040c05614280100719070300400582c01980203c4d00e191880c2c421901d007013250140340a80e900401c0c01840b40700c8130302c0c401102030640c5500ca0700382042c0c1c003081e8507a980d180040781e510105003a00c1c5500d946254800030403088039001303400d00c01400542081d080303c1c6070038000c501c10746100315141c00100e01454800c6d0002d501110b03000d41110305a0410f100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 243811285 1250 243810035 243810059
    0x1f03061508040308010b09030c040b03010209030a0b1005040207050309010c1401060909140c1807020a0c03120206090601120609020609130e0d020a03120c0c0b0a0c0e04091a0a15 78
    0x20300f0750014182e000086403604d21401181c41d0381070b0003130003880551052014000600085e200c02a419503090104c122103803014000406a00c4c8505405040ca00d400da2080d07010355856000680224410300051000440010490b812003900342048000e1440301c0c42c001c0e0040403000880301c0b09500300080000c103038455401418003244901030b8054103261034085281c2d42e000482c0c00c190f01074400706c03810824034202c0030a25004544e82c410760300003200c10345505c2c0990940d5401102d468900380314070f0a1166050110b0b6400c040750101511640d4035080200d44650503094004d02056a9a08140b046585810480d602c0e80000b500b520101c1d4202c2070400000d02c0384d10080754880c0990002e500c4018030120307996803120390507168040f0b0008640e20820044c0303004a104000e0080c6140d100c0049415145400c2c4504a5005c020403950103004c1c0052943d030003120094000c0303003090b071450300081c450311480c0e041503490010881f4540d11301d80244050880d920910f49070302516480401c240b00f10b49 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 243812535 1250 243811285 243811291
    0x1a16140d09051e031519020406050c0105060402071a060402071410060e01060f1404030222150e0f04230304031b030816051c03020403021008061f03061508 68
    0x54501909080403020061800210b40900758150428101780030900c44841c00035030000650a081d21444140785520400ca900940000012440114815604160034050a640440c060b1001e60030141199a07282c062480a510f000800e0000300001d49103032903036419101c401d504004c0346c11008007819466038680004403600a042030a016020901040c0214039038100c030b045a031703503100352100710380116401c0301c007841c80c1c514400c2c007080000050707a50071004040d901d13482139440301480025000310701103d112030801810019408003c000031020b0760601079200500094801e4595070320301d001c05465080084102800403250412a000c0000201a1050700d1140c20409251401c4409004401526120061258404002188120116000b841500362240040b201e0708480600e40407070400b03000c010000007a60101c1e04009501e4410315a03014a05541407119007420504080f8868001c03111071603003c511a07040310100c1c68441d510200081030704120b45100d0000240c2c004101c0791050b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 243813785 1250 243812535 243812539
    0x9020c210904052e0806150d08040f05120a110121051008150114061b15040b0c07150b030a0c0b030109050c03010803070f1502071b1a16140d0905 64
    0x1980c0c89000049202012010303501844024a1260f44080818804010700481c20342c0064030090308c5030000e84488090400b510002c0d034514000d42c18401030241002015050004946c080300c0c0749804102c40c1d900c0316030040b0342072a2104c202c61090a0211095004000f000503651401e8108030000b042201d02d4000e98424109407094031031440079841d0303500c03420300071014401d490031245682468000300401026951a15003406208400c3c81c15041c490544078181c60103a581003080100800b40e02da483e840044960325505186254907090f0300081041c10840d0782540da0011006a41c2d410000149025030200c14400d4050f01e550321128941c1013807003608080ba09010100304074054440603a0f060350348880c005d504183c52600d0b541c82140032400c0070740c3c0907001035242c940000d65038001803180302e008160b07044845840707410165000d80190300c9020b0010f000e026000d0407004440c22203400305100192003040440a00304000b00d40c1e00340d01000300e60f200384040c220020741c011389076100312442 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 243815035 1250 243813785 243813841
    0x910050705040f0b03090a05060108010b0a0504180f020316030f120801030f0326040302010914060717060f04020a1206081219030605120307060609020c21090405 71
    0x24aa400e4407503000c0d50050407030a0224080c14401c14900304040c1d9800004401250700311f100603240c0c207050000c01e070040f41d0581d45a0035801c40c0d904104541e50300a0a06460401501121407100c422008200000400404c0c80304188402d66508011410250400041ca01c1c00b003984d902d410396a103a00e2550407650715254240011140d801546c4480c100c036040440c450b450769455904613220810071550022040e440b035042809c3c03030b61084169114512a400000b0000c0e03450a01e61010044502c0e00355031944054200014168070405100c000c00c12600d01c048107440d48800219202d02c2020704a81091011600e01d40040e4040c41c0c0540109486104022061312100c259444484081010480840c2000120884c1450084001842050f0b281c0010950b803130f0800502644100b480c8401594400301b002414407080c0e110382d00051944060448c50704803602141903d540305400d21081d08144088501c10185010046034840c0324000c10401082c540601403000200500c1c44188420807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 243816285 1250 243815035 243815041
    0x14030a05030f0a120b06040302130204081b011d0310020a090506030f1b030408070f0201020a0f06020a0e0f0a1202180108010f0c05031009050601050403050f0609120403080706020702010512091005 86
    0x48074803d80100701400b40c141c1f0302c0c01d400d540078451035440c01c042c11b26485608100004154801b40109200145401c403c00740320303110003000500d40c8160b183c0000780e107141c0211400c800d03940000d403403030100f144103400b68881c180c510056903120390302c1e4060ba030080f4000040140003034801c912903100300c507404140780c0c5200c2003201c484c505000440300101b2180c1d04020072070104048445401d03525105104a4401c1403859807855038858681400710703015034011859000302c036048007400303900c6c50096419182c10714402000410851061080004c11484004500d0542d00d403001401c580701e041c0d590742d0489503076074210b02d8001c0c95140c0385025070610746a4441200ca220304120307402069070503440c094050a0ce82c01e0700051001606c0281405410840040090000e00a4034200b040c81c001800d51450718010b0182071032405071309100864800c0205000050619094514103500320034010b80710640d501c0140c1e2a8801d44541c0409a0034120400240c50000030fa01c4094841d40c00c0d0a01c003c5e2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 243817535 1250 243816285 243816317
    0x801020a1e05040605180d06052707050405090c0604060e010311040302010c140f010e010509150702030a1805060f070606090204050607030c17071202061f14030a05030f0a 75
    0x241101079400018400304410448070340701c0c8014101c500044130550f0001b081d03440005811080ca11011580f46880703004201580c0152044844e02c01c0300f21a00c4a000000541ea0035212070290190314400e90b03540c40402c907081810450810080740142080f56125281c0001420500b07105142e280001e092003124003180681078251021240d06859a007505401d540c5c59410019054055407000c3c860381c000045902000d0140d0000480342000014075410038000d21810309200241001a000c03240080c8864550700008440100f4000c1c500310004000004e50041c032412280d009551061001c1507890280c2903550051102d5845901704002c00b998444940007a800b4920480354800000c0c006c103800305c2d000711006041cad288954114a01c0740710304c4100d0340840e0801c41003a103c0707041008952000303e0301003003841d801543d000c00d048034084460603101a0b034400da01403c68030b001e20007154103030ba0320b0403c001c900c025405400e80e51100946080c01d0225000b003402c0f24002207500034140040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 243818785 1250 243817535 243817577
    0x41a0702010b0f0d0303090b01090b03070504060e0429010312080702010c0504050d03050702040f05010e070206190e0309101206050d0b060f1203030c0d0f2904020f040801020a 77
    0x4410058416080c081c6541d04000141c0c1113a9402d80038140c80705020f00001d007e034240e69000e010480400901c0d0403400d001d2500c0c01010340c20041c01030741790074400d0103201504a0200e0b40140d02c0071402081c5840381d081c0306040e40c00c22441c40d41081c0345400100400413200003000341c506031a900d40840380d5510382c040b0700f030f50030390b1400c04007180381000b05000c0d504008c002d202d8914040e0030046e19110655002c074044544045822086075074440040c40802c2c0c20501c02500710701c0d184000c081c00c0c10586841038140d4008200c042c01741e50350b1400e0208200d020b1050301d0301c812004011214503002400050130060a982074a0220303450601c011072140790150032246500e4215103500f12554401c002c0c007a4684550b00b0280c0e02c580c0050400c0146001000194410001038120903100c6c010035810400350340c1c0241d6400f00d01c0703050050180201c0c800b030242001412403986c1c1c442c0c9400514011400a2080c4e1740307501c1e41040e0024000c2200c40c0150020700c0b40088507130328600e8a08141c0d4604c104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 243820035 1250 243818785 243818801
    0xf0a0314040f080a030e0604060b040c080106090b070c09020c010b040b060c061f1e080705090903030f0601050c0a06050402100924030f0516090b0903150c12041a070201 74
    0x90800042c48500410740c00806420141c405081c001014900c00c21840e107003040c112030407100a5210405000c09080c140103100d4441d0329820001a2541091000341051a2074014403909900216041c428810800701641c01468004000c5507128140349909003e000b8411403940628200040c1940904000040b030f5a080c4119010300600e4032034048210200485100540101d19641d002046513a280072405214203084a0180361680c41c011040c2e00700407055104078441c03403140e0208203403680c021044940c0000c14040d045e449a80703007401a149401100351711030322449440048020815580c4c01b0a018600858058181250340d0b201120000b1a500882019a150703035500b1241414664040d00c05030450b003404030300c00a0a0481000f1100210341c029152010b100500c242e150300844c10700061b000000c0740502c0c020303140340030a40e80c00700c081118002d0449807001629446200045d40e4010542d184500c0060429045c0000c1c03e0b0254100510381c0ca507518007194141b401485540c007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 243821285 1250 243820035 243820043
    0x901050903031303270e09010509160308070302100f1d030a0c0b090304050d080306120106050a18060e0702010504051902011b030507060e1b0d020d0809150f0a031404 73
    0xc00c92800341e030121043c1c50440080600c07031400c03842d17101611090a03900b101420180140380030604d0000011402c1da003025009001c1c6030405814010520b605845000c1642d80025070b00741d0312002031404034a421041360b081c6650a14098800d01c540c00503400203500360308410b000e500740080d40c0e01010380300c2c4500c455030408a4428003a0f90000350b02243d0540e44040c420003503e0400303641d4804140054200002265404000001c1000620f040311510f050b0b515504020407110f0b0914000c1500a0440c1c02180202107003034105400f039030301d03d030044009071482151001407410280c00281c007070f00040c1c40c2150f243c094607489910600c0284030400c0c005405030749503403182e508403000c400519101c0c3d00940410108001000108080c0c1c000c0d80344440c1110010a20030340ca00b016030f041c048094140380c2c41050000302d01c2c0701503078500203400810b0760000211550740800900040c3c0c10004011096078015000c100068284462000707010120a1610140070004080d407011020320b1b0124ac0040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 243822535 1250 243821285 243821311
    0x509011d0c1c0c08030309012909070305091006031110140f030a02091c02031009050c040f020c1b1804021e19170d09060903080f0906070b090105090303 67
    0x4546241042503003071002d01840380840f1081d00c510295003542c1c02141c1100d801ea450f42d910307001441400b141a4a030610064442d0b01602111000980040f405001402010784560201d510303d80244080c0b8500e0001e003408001846c0e503450300d00c05100c0c20764001032181c81c1c0c2c2c0c0700c1400050b004030aa01c190511076241c10740781014580303100107aa003010303281040280d424040e8055646031a00300c0d41841c1e00e444004a40092540304141c54501302501e101e0b42c49043c0401500000c070001010305511000b264042814600000c2c040c00a002e41d110b0001c4034401c000c0c2140e40c089101e40404140d03501a5a602c1a02c18201c01080a900007610020340142c24a600c540c0c50001d000402c010401c0001d0440da00012807694039040b10703105410004200024140e88210500108110340705d04d151410040301d454545040071b00000c8091002401350400021181d021607900c1c0304a42040500400307540d00c4200c02c1c14408440e010480389010203600c1d0401048046e040082980c0c803409005001c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 243823785 1250 243822535 243822559
    0x1707120309171e0303091213050d050f011b0e010f0801050d030903081813060305060f040f080f0a030b040b090c090409021206070807030c050d0e0309040509011d0c 72
    0x2200500d000c40d240c080241c0543c2d9a08004454441c0381200c02103503c500445e280e04154a4071424200c003024030180140707040100c0c1082d0f540019200c02122000c8401d01d44042171410a039091a81d00d14028015510f0302c15028800d00a420303a00704012015528803804100745001560080041a451000301d5030ba08010005468000750101e540c84c440d15054042641d642c2d0b60180302c0d00500070200a20540143c400c00303a0900d02d0004141321100030040c0515450354450300d4654101500b016541e10110380041d040c080c4d42400002c0c05da911076003560350341448841160107500107199040c00642016074402c0b00345010f01950041c00801001940b007034071444040c6d011a0b200d01020f540060700c03000383c02c0c0560740d81d40c00b10280d01101400707400249000700f0014002c1900900801c1403501d40720443e01c2840d8131109075500c03010316000005800d5101840319145005404140d640035061130100045104d06400038090141c4080e0400c1003209044181a180c1d104001e0664001d40300700c604c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 243825035 1250 243823785 243823799
    0x80f06041a1801061517010f05040509031620010f0f05181201061a0307092123010c02010c14090a32010e030d030906060b041707120309 60
    0x1c4560014000031010b00700e0300100106500756189030344075449003c001414480b43e650000703100301d0140c40d420b1070041d0541c18130244e410203a4840c01080d0045a8903000110300704000c00403600d039501504000c940c072a960740b81c800050881c2c0c00c0702900c1d11450706254480e55024041c07103501d007030740754407000c804000d000b0084a0641100202c001c10304400d290092054898078a80044101700c40000301e4010705040d08a002100194620860784004104021081e81e00268800c01e550b50b90400074034100c01403901e5202d0001600740030b8849100c030007090404820841000c0e03407170344910b4001e204c1d28500d944107900f02c2d1070102414000c6070b170320140c2c807010400e41d20003041078031b10040c44020411745a0350f0b50408038092401c10701c400910203400c03640c00700ea00703030f0310486100d402d1800c14041074682c0c2c04251940030410800342415140c03a029001c0001c160044009014607072041510f450362428000c200c070348450441c0050303024110010852440d60135000399001c0c2c06440d0381c0c0740580b624007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 243826285 1250 243825035 243825083
    0x90d240b1c11030c04020c06270d1b0b07030e0c0415051903060e0304030c050301050115080a09081804062102060309031903021909030c05190806040309080f0604 71
    0x420b803641070140c1c4c8030b180501e030f4039840503107196100c03000244030030718002d8481c1440f00e107813441d40104a0007900301075040001c00a8840038285180c07901e1030800e44203564100382c181c600040100a00011030400000755410b9010311040d800500840c0c10b50002e10b014841100c0340050141241071501100380f100b42040003040401860070500d84640c0b59503906d5810440700c10400000075600f0003c0c041040c00400302a400c084c000c1117008100c2c035450804241140039180d0030800c10f003d10400000c4109200764807407009207402c400410707aa41a000189010001c2d043d156a00ca680703001c101054003502c036001c3d8054170320f401c100d0f00f8010719031782c00b0001103070002486400030740b004000998050340b002000e40c1c1c81c1086a180540c03039050f5604000072008280540f21304215542c00c0030404960400000c00485500745d40c01c0c144e8000905100c1404006034008444074403e00c030603c010168040c4800c03040780c000b00d0945640240c0200658cc403040c00303039009082c0d10300d010031000078204000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 243827535 1250 243826285 243826313
    0xa080601151e08010503120a050d0504060e0106090b0114090906012f030d05010b090102070b0904273513030b10060816050f090d240b1c 60
    0xb04010400078080601a144110002c2034034001903050f000410950a04200040d11240307140f40e00740c1040d003050030051060107800348180300251503001140510480340d000a5512200000920602e92603080003005448800001c60008040098503010052a0010f41c0c8510a004080715150740383c40700115445005005540b16861514480c104214400302304c110060204201941d10b84940381f10310300c101c80c0141d11901c408030040042d800944e0f408180b0000391203032243d0711503d9110b0344001c075000708040c03503a1544134907000f01c4c54040441f210450b0240544281c03d0017015002541640210001000c11002c1c4c0282d41c00481c0d4403000d403100a044000b000280c1c21100b260340352158024564162180314402d0007142c414000c2d40d0b4090050740d0b0206078605034900200c1d840704010614890550070000c064030100b207900a5540380340c495480590002c142c4410324004926502e00840500300102e8032914003034034140c0c5c0c0e040a041d00c60080401d80c181501201c6241c66244e2070040c61 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 243828785 1250 243827535 243827537
    0xb042003210306060f0307030902030d08010819060e161a09061b010213030f02040e0f0c09040c0504060b0d0c08060904112404031b0f0303050a0903050106150e0a08060115 75
    0x17800075100c0d40d5032040245120b2101d81e9404100c4015138010b0600b080303c003000c004c0170010420011701c4000030008a844c50005c0880d9a05004040c90a0080c01080b0300101c82520b40201d2042d603001b40a034a20800c15141130b1080c1000c00c10900012800fa17228000c4007c0c3c100e0024030040c1c0d080d11451240c00788004c4a034001514200900003442c0584805400894a0044c101e90003000d500b810320500b109050040c0c02800908039503011280d44d1408482c0380c5109540e4100040d00b002400800c0313900914010f0070611690ba00c80c2c8080c80c880d00401d9030a10010300d04100f06650902c9040103c1c010400504101050745480d2900140103401c2c01c07130140c102400541d00c91043c0d02c070407080e1813240d00f00142d8544881c10351030316031482414555030302d201a070a4203041c8103540101d41e004088070b41c141411952594a8002a01d24540507030000e0b085510340440061000a0340a4024070100d103980c6100d41003160504010041e041da00811820b64443d400510030b40c00200391440da50142c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 243830035 1250 243828785 243828787
    0x11a011107030507030605180f060c0d0e0708030304151a130b0907030f06090204031208040201090e010602030d06151d040b06030108151b0a18030b04200321030606 72
    0x141c1d103d99141c945164002c50b6403603a1132003000300443d0741c40760081403100a08041c00391120002c0c2900c0d07403608050101800c03143c000a0180f559090b5a000c02030042d5400d0695441554505143e9102e030030444003580c075900340b04403aa09050440c400e440e1840c42501036002c1c0c4410a0307042c481c1003d901d56100c5840d69a60f090590540d86803e0702a114100d550307004900d42d02c4910140d41991265401400d04030f0040c442800001c041c000091364401003450001c5581e55a0b000484204d07010317a001c042c0e040f68038030011817026408001070000329000007042c0a2103544e000a03203d2904d000d89101e00182c0c0c403082d842c1c000d01856110040e91800100b000c601da40d11880000c889a1080c3d201c04503035400800580100b800420a00354840280c80700d100211811442c019001e10a0001010801c5030b494606100c4101000074140511f400083c1c17800c2c0c40c0351510b400741e0340009010381e455017048259000e210030310300000c1c080508031000210066541030020700c22840d4201400b0030341d0002c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 243831285 1250 243830035 243830039
    0x604020d021201031202011503020603090a1505090d0c020102030d2a0e030f01050601140d060b03071d060c07030b1005060a020d0f0e0a0e04032007030311011a011107 73
    0x3114006440c1e01c022040145840b5403461038450361880c0e03165800020342e414004250120400e00005404a0382c06036041d650b039580307214046040801000c00140160842400508400c403103601c02407042d0440300490302000e0b4440d00c2651140c00e088002401070303000304100b01301703a402500440d40c519261042c0e0024410a06100c16080300304900c030a0005200e40b10100552a040144110620011000f0812801d210000801c040321142c00364000c0d02d000120000480b905510000c01003000030040c41c0c580c10030761030041015034910703504141d2255000c98561036240c42d00c1200c03440300c0d420004040702c038610741e41c188419100902c1004002d011200002d2142c40d01c0000b00700108440d409005202c0082001401480150150204202a0003002030381c90701c401c0d03181c0054401401842107280e90300e01d000c40c1e01859861000540009882d8058001d0400007441001d480c4645c4400c42d0f4040d04020082c201c03000358850020b4103243c1400e044255014105040c0725481010a80e5902a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 243832535 1250 243831285 243831307
    0x31605070534090b0a050607080c030a0804140d080a0e010b03030703110708030304030903080705010902130f0b0d0507030b0702160b09090a0b09010b18120c0f0303070b040b060402 79
    0x19040c291a80708010790b04074204540c00e0a07403880000c0d0203409010410801c448011602900c02c81c054240540d00018400c401e0044942c01d40d02c1600081084940e5070a0b4084000c0403035030305450480703400080f11010500746801003049a1007c0c115070754569141d0311400c3c44005070a0f02030343c41e8840d540c0e074200c41c105500d040c4010710040340243c90380048031906404403840c06915a1001c20184c10a100307200010350300c0000b5804407504240600d85985427410302900400750010b0003507000c005c8103001c501d170018a400889801e41048410000a1054414000d0070b105d212030050058100d2502400065840c0c2c4503a43c01c03550610480e1078085241c50043c19000881e0041c0d0605180402c54403400d207040203659500000340601803008019500200303243c05010700a03441032003000725040030301500381c80300c21440f0700b00100303481c488a46214030750b0785070303180e0041c001d01402000c688400b240c100002210640e950100246655030741c1c83d10b131038050b44070140c40d00e0b03409502040007130746c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 243833785 1250 243832535 243832573
    0x20307121d1c1e03110d0509010518040203090c1309110d0501020403120201050906160c1103010e0109030306030b07030608030d09050c040c0f0905030f07060c0c0f06020a170316050705 81
    0x29800341d02c00718618049404c01804206410410341200d80c08426521545a400070581d8031a40702801c010341c80f000d41c003144401c42801c042c4070f243c00a10210420401810005d00c8038204401900c181000449165019054810311034015155044031141e009440c02c021000d0419240035600050500b6100d58442d00e00a442107003810051391541d0911407650000e0125035004920100004185042000c0c00b4200c4050400d02034040d0003142400c50080e242908660461807504000304030403a580c0c5005001068072f800243e915a20020008820b18000c0c4980c100341c0d03410f00700450038092203c0140d005845551400c031424040d48480e000030303840344e02407002031000d01d84a40300b002c0701c02c001c020004101da5214a03c242e0164100070050000800c01106481e403501d05241d40d07100600300301e403030800a9800075410304c4040d80700240140d404156400ca06102d11241001d5440711030194060f40410b86100c0940b4018600c40c081e01800b40b0002d03e101d622031801d442c1c2c03948041d8408205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 243835035 1250 243833785 243833813
    0x40609060e0907121505060a0e011e091802090a0920090f0f0112110618130b1806121209040c030501030f120c050d020307121d1c 57
    0x92480c0301424050b20710402c1c02454050450000c144402c1c96868070394018140a030104085913654402c04200340d83c862454079005002003a081d5107282d65915a8103110001300a404541c0105020300070452400e60300813041c0e000c4010004804110f50358080159010b0007510380014103540d58213010006a5215011034100c001d4005064020030072410301110080050a44c00140303000800c0181c3c00c4880d4481d203065804200c2c000702001801d1828144030016400515440203011503141111302c50006a01c0581100b5074001d91000c00e200c5c06070341560980303d540341c1c0c03200b80e03c140c01c0c000d1149080d00f190b00103401403483e44034059800105003880f01c45039a218411400003207280160529004800c654200c0786401c00c0300b989940c4904510060801c0c00a20148a0b008080e41a074031961101e0a11a000340965945503c0810702a640c0c2d030103e4001c0700c02d801ca40451008071802040302000c440380840701c2c100d455400724108002c1100c584612401c0042500740000816150003900350 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 243836285 1250 243835035 243835049
    0x8060103050d080603010203070909020f0c16060905010c0302100c05041809121b080906090a060207050a0e0f1302011b08031b0705070603051302040513061b0c030e04060906 76
    0x181c0c42d9100b00800000b40100118003ea00400034051419805803101080391700382c18005880e1021007510040f94403401e1822030307661103070005140702d1a42403103118084a071302c0c2c2c851640c65555000103413410044a1005005a04050548004c0c907066401440c0d2030007640c40c080e440c280d141c4200d031a84404941024580035590342c03000303080051500c4030586d11034050904660319a81303120084048001f20304020489600407420101c85d441d290305584007403030700070b00b11100c072900c41d00c0095458465208042c815800142c0000da0100e2902c1818064421040c0c415822760b98100000e400c582080d0381203042220b000003180c0d908190f0351515110034861840c0545e2401d20080d81040f200c2c20030244045610200140c0c0005100040c0c03008c115555820049000d5803441500a0480d0001c180a50014140310401c40406111000c0d0f803100b5200350390810214407461010400d50b48088500d0740494450494a00840d0045400a810000c024800310b08103480b104402d040d00c1c80c640c0492 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 243837535 1250 243836285 243836293
    0x3041b0b030a0605010504081e01022b0f0207030e120703020402180111010605030309151c06091b0206060d081e030402030d050310030602090f150a0e1207090203070203040806010305 80
    0x480900c002e8007882c4003d110920304641060700788505142c90340b04c0545c100c2048402c00020801c0c0c104207406544040d1a4058040c01206e00d00f00c0c45002c400c0382005645510789441c1410003106114800c0d12002c94056031200800d180c120180003440441d000c4030311517881490b50000c0160b4903800113101505548a0b0303896041e24400c009400c1c240481440819641019403e0003a80c500105544c0201400c0b250189481c0640d20386a0140c4251000c0c0580b803000c46100c000304042c141c214804841c0800020403110a11300388509241941501c1140160000000304034a4582800d440ba8124080d0030004c0c035250412440003507548881e6048128040080304200540c9403e1101103402c602c0d43c20218507500d8015503038002c500c40e0780002007000d5400f007aa00d40c1a100c1c0b10038901c1300d00000d018942d080c1d150800a070300d141c110480c0a80081c0c1c10f1002e0507400e047c00c0085201510790500141551810030180c1c50280d00300600b20409c6101c24000042d80c1e501c10800d1174000d500800144c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 243838785 1250 243837535 243837541
    0xa090b280e0f030a0b040809060d0207060204050922020906040f1505030c03120d0c03020f03070305010504110a08040b330a0e06030a120908070905150102060108100203041b0b03 78
    0x11110ba42d4400c03098600c6504030300b1181340400c00341c104890380035500540c1e840d035071240200041d0850040340424000d039480881c2c503604002c40d40c4d000b80107803501110307500c1d00c49d580c040c0c1a0350001648485c80464540c916850001402c0040e07116400400003400032480d0841c0383c41100889140c5500c05a80c05080d4200300b003942000d02c446c00120350250090b0060100c00c1945588920414400258103175841500307610041c8641d040ea03060501c9611040d9803401c007120024082d02080c064944500e2078207920003d5040d582040f1408040d00382c455007455a0b0b0742c1c0310401500e00007031100340154403d800c400701e4500d0060318607541c098111003943c48406000203014096034103400c801103148203101482072590703000407200201039100f90070151640301c4180450340c1183c264007840d1948203608002c140000b49821440c41038844400d00402d000e4880012a03460b0020b204c1c01080f500b00f0790007584150382a4000790b61190182d005c602c00f4a0302d010100204201c65030114400300c0e408028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 243840035 1250 243838785 243838789
    0x4081c02190804050a09020a0c0b04052407092913050402030c070b101a070611030702030a17060d080d1103011701150605030117010605040e070302010807050a090b280e 74
    0x402034900304034218103192240c10064201040010007400104c0c9000004003084000c01c952440c40704090b0884410a0314370100184c03081054480c00042079000b44040380c065601b209000d40c4030850501182c2d44105000c0400d0302c0d502200000d040321212aa003c28103469030f000450081c0320b003954182c2c0d5051282002e014800d030140040c0c0d4018000d100411445040c844050114991180c03011340d13a51041c0381a100414030451007014011340030040020294002c00900407000382602c0307100e00e101416008032507210044901d02d600c452041c102101040f0040041e00c071084010f00001541b4051002076151074009038070100c0d03003456020284881e0f00c0280108182030402c0000f44546e2030030001c0291180c04140284604503002e42c1140740f01c5903094000c0001000d015004101c0406103d0085448620a010030b9000c5450103002c150340500c507104650360007550383c4d0f035a400d003400c044800c00f240e4000400c0e0010590b0340802800401c40013200c0c011444111346804070030655640c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 243841285 1250 243840035 243840049
    0xf160501110c070906120b180607031a04061a07030903050601080a060e0d080601110a0c080606120706090303050d060503060a0603050111040e040f02010207080307030c03090b04081c0219080405 85
    0x81302c2609414000c042090406240310158030903400440001e01eaa5400c4443c4c0071a9001051082203101d480e0a10070381903007540c4001c09055101c410712004c01c0c0c1c020248000d030307042c500c80d80d002044c0c800b00045207a400400600060b91180c5040240666207403121460703d03100380c00051403078101c00500b0b400c108192080c0c4134010764400c043c000202540d0000b508203e80181507a05100f4450410710084405221003c8020340c421310640d07a130380e144d02074156030b1720381154518010305084c0e06e41c035031650740010711200312845640d03022030880c216a4103c6540c0c1008480c40007182d2030b0500800c1c65a01404214402c802d0414005031a514500388282910303405900c00144c0710381000700340b0040d0310f4213500c2580140c01412034503203034003d0710040b07103482125845000c0a0001068050416502c2030301c1506442c025600d103441c032074139400c00031114861442000300680c4485c881811078441c80510303400000300c50068881c00710403c00e00d604d03005041003040b0b4904800080910081c0ba080e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 243842535 1250 243841285 243841289
    0x61c030819090506070e0f0d030507021203040e04150f020d0f2901080903040824070e0d0303240603060306060f03031b0507051503010e0f0405030f160501110c07 71
    0x54010711040b4041d4580d030362034200242040c0100980d10100000360745401882d950707480320240420b030030440b0300d08000b8401d030801182240301d440c080c01d0740448600000181e038162003107060555501c1d100c9944207400c40041540d5035440c26250700240020303c007513101130b0011882d0000c0101d1456010003d19040394034510f008000e0b2405020414080c1c3c054440b101e000440c2820007424030303120200501e00c0c0d03002d03503070062825204046c035010320441c4140c052555004d0040401a0b1603c1e03100068031a240c00100c0725821401c04010000441d04ca60424401d02c1000044503500c1c5503280303000a0310819580104012a07100c10041042184900c52000240700710b10b0743d80b03040b50556800510b00c0c0c0a000b410210b5401c910302aa060010a2200b240146002444102c00d50700d811281d14494009101c1c070131110f1413100003c0c008248480380c0710b200d9944440918944183c060022405800c00b0380040d0900d803465004800044c000d00c40d172010f207088140b2150303c42c3c9190000d00e16002141d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 243843785 1250 243842535 243842581
    0x30215040503030a0e0c040606030c080c0406020607030b0609030d0806120c090106200d0309021002010504150e0f03070501150503071404090f150c080a0221061c0308 73
    0x4901004003085020080d83d8014a180002041c0e0a0716502c049141c1182c1d4810550301510301800020b050341c15911110705003945442d42d1481c5e40d11000c088455015510030400507800420000c0c044a00c2540191202e05000f01050b0524070042c0200786080300711101030000c280280188409458114800c1c910403038854000d00012058001090180c441881a50b00384044c10301500c01c43c0c0c6640800200d0316840d641102c40e20844240c0003005018490b00981c0500e10280461510500c10301401d0700c900e030030051204802c00010142801485000401f4809025403072003070091000030310080c14a240148004a0255892010400c10101c1548018800e51050104000d22510708440011003003044500045c8101142820301d03525034001001424558003800044240002d5482a944003140750303500c1020755683e610340c3c0c080380700e1007081d0b400100e510204c40c1c041e0f05540520561051000d0444030495a00101c0640402c040c058200d0114207100100042c100310306100035590100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 243845035 1250 243843785 243843823
    0x10c0f120902031906061802130e040203060f0a061502031309060e0a091a070f0909020306010507020906120313030b06010507080f0d1b050d0f0603020a150c0206070f0302 75
    0x11580000d940f00b10940e20001120483c4144c00c05014a0340d00600c001d1000325204007450b00d07100c8080e4001d50005e2201d0210654003a008150110088296441036601400400340798488525220170f0010080c0481c14090f141c0c580030400d407050329803074200654150015500c0e52502d00054400c1440c41d0030909909150520400440a081d245a80c110b0075031400011801c54a09109031181e40301c01048900f0003084040c09003165001211402c0e05007103a4410780190340301c9a1a205070700c02642c07500e00041050007154050320304102020381004004200850851b600c4590500703640200c5420031180b020070f9003c101b0b110071070352960b520003030928109190450941d508103143c0142001e1510519020400ca6228195035010710400c0c01c80000e4091040700014001307007140d00000c00c41c6030b101d0400c0000c4440080500800d026242c0c0205611740d901e0600c42d112030000745004204040048801d01c600140c0ca4040081001c14005d00c0f19402c070314840e00700a0700e4864180751148a20364 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 243846285 1250 243845035 243845051
    0x50108090309181801060605071202071503020c07031a0108060c0903030304030507241506090815100b0d0902010e180402010807050904020408100b01110a061805010c0f12 75
    0x103a03485410b52403c1156294861a84610340714403001c030030044030000150f280007404603a103074010000e0030509200d281240c12000c8a0300c400c0340c4070b590a1042c041611059001c40240703a00a07000782503111101c0048501d51a80c81d00c2c1d81c40601012800c003083e074200d101c010321400314203101080d88030301c036040300301e2410b419100801d81d2448010030290411601080e54410003070b80318080b41102014003082285a07203e82c50410080c001511b40300100703110380ca00003c8540c01341c00880300322510040582021002e100c0240c0f540c8500500190500b140c940002c00c65040c8100501250f100c2c1010014100f1010b100150498501041103882044511503a00b404049003485591099080c0b80101d01030700c0303011050300c1754024282c800c3c0e405400403c02095040e8002462008403090003c1400316203c0741d4019680d41902182d0481c55401005e51003001c0b070b20540100c40050405401091140c40c580c45880c00c40e542006648001001c50705c0380c0604950045072485110640c88003000302a03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 243847535 1250 243846285 243846289
    0xc07051c0504060e040204120b0a050a0b0906152502130524030f0a110406060c020315090a0c1203091e030b040501020d021201170a030906121508010204050108090309 73
    0xb0045115100030050401c4001030325407226010703140200700c11400c0c9540d2410910300558410400c5440d0360b852032500c80018520001c030b000e40070306168080c0000c2010740301c0e5000c1c052800c180700c12540031400b08000405400801c0303540c8800320300d41004081da01800c1481040b0321043c481074a082075a0034541403020041c140c50061383c03a100364219002c26640404d020906140301c4c8080b007000390140c501a202808501218801c035101c0031030301007160b544c0f500c2e41038514044011010750103520407001c0740c600407618602c55400c400e00c4021140b2250269803001e0920b852a0840820000312140c05810107411082032030250841d003c038061441486422010301854520006e0104200756002c10203100342075045441c81a0b46c20002d540c0e039424040504002c207002c0c03061018441c1c0d41d00b0540780f84480840c0110349150b1565034144110301e0b1000840f0000340c4200035007142551410a01854448844c0c0f40c2c006019007000940c46034a80000940080c0b0700030f214052640081101717004035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 243848785 1250 243847535 243847537
    0x15010605040e070f05090d0c0312030213350a05100c0e121b060706021605150402210c0307030c080d0203182b06090209060303070209010303140c060c07051c05 70
    0x20359007d442c0e64083d00fa540c201007104810583c0054800c0118060203031405a050f002007903114000d660321000aa99180c10409501d004460141d901e001d072008240c25940c080310100d905400d000441c0c0341d130020380d101e190038543c0010191040715507602d01d07922070782c2d0000d801d00c60100044651b24810494000d01680382e01c10406409001c204101e0003a1482d41c0b404107441030342d50010001c54070341c65074009610545920240680d458860800c0717013582c0451000800348155030203081e02c20016010a000c146000e45812010382c0740c0a003c0042680381c4040100c40e00860241c00080640c0380381804040c02c0a5001c9801d00854004006144240041b801038180170801954200c54451042007200c040b40a210250340031281e02440744410302500750004405140200e03840142d64588a04242da00c2c8035881000317410544000041000c00d010b41d80804000c02d5a080c06490070a01e0b0b4005400c1420440c1c00382c2000c0c0c0702080040034031408200030b0510b0880c1040c0101409505180a401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 243850035 1250 243848785 243848797
    0x50412020a0c0303260406150506031510030f23061206042a0303021f020c0604030c11041d0d090308190207030c060f1106010f0b090315010605040e070f05 68
    0x180030404442015002c050702d56000702010b40e209040c0329086c14501070340a030000c200010807111790681d011a982c5408030803640242d085a44925800e8448002c0c40201005440c4800034076944980300c40340080b040c0a003610401402540710240907120568414409010701100d0180060302c00d0007554080001c0c1f4180c00a4100022013070442901403140c0d9482d2070442d150640703d60b5403034008200341c0c0000d40381c4840050200320340c1031440c00c40c1e4240d0490140c3c2c89000a1036004102040c0440d0050f900f00d4115801007411111b103140d420045002d0360000a15602681554220601100814481c5245c0b0346c25074581000880d18545420310940141448001807113017008141720100c0c000c000340c2c402180c1c40040c504081d17a82d800064840c00300c1c500701d440400d0074100b41e02d03103004010580505860060071030b21415401c0003c5417225800c9042000e400d0720604008801b02c2515003881c0c1e0003400c4070ba5910f5617480c100401c4810340c03900074140300107101e08581c40414060700f000c19200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 243851285 1250 243850035 243850037
    0xc090114070c030c0b0304150b061c0b061602030111090a0e090a0606031a100501050a0e04090f05010615020d0206010614120a06051c02180603030f0d050412020a0c0303 74
    0xc0c07500c000b4203103141544038962006094141069001030f02e5070030075000e5486640166520300f114144030140343c0c1610001c81c040d640c08401007140c0a002003040c2c0f0b080c21084c000c4c01c400991050a080400c3c107990046103d402c100d01c2182d900d104502e42405000c0603000908440ea003091740e06ced0082100e00004d4018814504a030030005203818a081105a031015045802031141341c2c1e40e4181542029807802c480c0c0004440040003070a055a1180030720202c40040e5903061400391501000c0351030190090b510359019444800c3c0742c0c041402d4080840e0b42d1405400001860f503e403100040440380321200310b00035034002442c4030200b550081b980380d0441c1e00504000040307662004034440b00b07200d8401401001980001032020741b0383d031a4040002e68030295000f1850345c1443c00403581040c010180254401420301c405120480d5808025030003100103000c603410401e4898100312550420844108500e65980800040c80404040b00b66001d510740058000c1e92031076201c56840d18042e002c01b0b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 243852535 1250 243851285 243851287
    0x1017010b1b0111070b0106080415050c0408160603050f010b0301030f0212010e060709062c0d0b070c020a0b190309052121070203070f02060906030a0902090c090114 72
    0x20000200c0102441c100641c0e81c030007040301d00d1443e450144583c01500c3c043e1243c41c403c0001240720383c040c0f08846c0c00385030010944110000e140402e4006043c000b000020004014800010194001c012844150720395483d0740a03030900344a4000c0c02c0700d10090110600c03c1d140c000401110344a00c1c03c59042d06e401484032a00c10005002050740d0042c405c018082070b40c81d000081a40b00c2c004581e090055000b6641e1a00c429a2840b0440e08801c01030104c0280510440c80045030340b8207030b00304002030f903009412040b4060301394031600d07402a0200c4081c40800c00c1016180b00714581b41001501904034070b511242041ca40c00d680144012448003c501496540c1c1000c00a0000070402c5030004441030180500c8030504020500d8250000788641d21301c0301c1800700182d03401a04007000d5100d01c680350b004500b8410240c40700150543ca956040c0d8010703404025441f256100c40e8000d500c0741b911070301c0202c1d0302103151040c4002e0010040446502e0b100a0141c1c05041c0c0c1d211001d4080300c0c00510000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 243853785 1250 243852535 243852547
    0x602040e07020303130803060a05090112020117061008060d060e0f070906030b040308070e0406060e040e030301060e1011060106030e0c04050601051806090907030c091202060a030e150a06051017010b 87
    0xb1270500c4ca00390304116071048821000150388071b01a1014640c2c0c901c00c0c4d90780c10402e41d045120f406280070503a12198804046000100802d205d140095800100208112542e0285888290803a21020309081068220103501e00b4504400c000303580050181c882c00f080301910351345071080c40034030103400102003011880200d8403040c0316401d03132698003100400c1000b040d070752040e01424000c0c0301c80000c1d01503410040e070031a0401010003564101d036242d490300c1c0c80418010081090f8030070703880d10000920103050f404502e03050301040f005010b0f0840d6100000c290202000f09854241441c5085100da41040102304032070764442b041d40e40f08410182d803022040030301030002e5580e010784000d003904000e102040242c0c8641c180c0141c4400b095a440b26004a03032aa00b60042482c00000041d4004070100a00e200305c510a60250b50300c20700b40c0e82a200c0320310310340300341c8240d65005981d240314158844406009a18000078041c0b4101c0c89400c2c40d130301140021031050b41043c014407800c891020003040c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 243855035 1250 243853785 243853789
    0x60c0a0807050c07090501140f0307090c02100c1d030a0c1401091208030609060604030b010501050f0d0504050f010e0c031c020f07090501140d02010804140106050604030602040e0702030313080306 86
    0x142c4280c3c010b00d00a440303020ba104c0803054002e2609201d02c90b203c8526680440c407504181410001d1090041e0290522604045401016000c040b006c2d20844c0705d0880701003526031491048410002c1166105046070054090b9012842e80da0f46400384290052403c6c00001a1882c0c0d03810700300c66040c6030a0750700c0c522400069440c0c52050748800b6a02030b00201900400c0022401540300b0f400403544042c0c5a21004180507440c096800014804405080180541c0d801407002d04082125180c030355142151a450920559206880403641a40300780e480090541c803e008000541c4a84030090440c074100700b000a6440c0984c48250b00400642d03003c88525920030701c20a00745050105c2211225903035441a100101800d10510880ca0301d000002005450300c07811407000160140c1d00c01c04107480342d48481291030400c0c103903c1c3e000d42d0380b0480002d0310344031180504000c60150b10016200d80c03070514200c402cac403030082503001190410000c2092180c410b4605c40781540c0c01114068503135a0303201c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 243856285 1250 243855035 243855037
    0x7030e03030f0a020f06070201180611070c03060f0c110703080708040801020415020d0e0603071b050d03020702040e07050109030f0c0803180102010b030a0b01050d1703040b0105030d02060c0a080705 87
    0xe65180c9080c000a642c2190f607400150040321400d400c0c0403a566039441e260220b00700c40b4140784550f00c0c2515148240081200c54116241526007038410354a0241030740d5035180b40c00c442d0b5104554103916526111303c80302d114805c046001d00541840c03141e420f001c2030419260645030000401d40d400c08640602071141c82001d96029080450003103542d143c0701c10142034109002489100184200500320084600c00c0c1d0b00d41c0e03401c4102070410b6003561903109043e24421031861040c650810031013100d8000c00c00402005244200c541c400594495050041c00b065540e021221040c2c2d60002c4410031403070360701c18050021207810203010f00040c1440d1600c02040761080d885281548000b04200c80801500c80703c400092800360002c0210020311010300d902c80d141d0000242c00d150131000100618108500040c030090300c2810002180b40c0301004540c2d00303401c141c50079104101c050005001500f810071914900308440d0004002602c1c00750b410101600c43c00b1200801c115030f80003c00c0303095006030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 243857535 1250 243856285 243856297
    0x30902150f07020a06090e071d090402010201021207120e07050a030201200106080718140a02090a0503030f030109050106090b030c07020d0203060f1501030209060906070512030f01030c170307030e0303 88
    0xf0130000440d959044001d004084c2c0c0d005a0f801c40480f2404034001c42c1c020503c845900c54406100207040354001c00304144103200901c141e05654081250ba501400100b0515102c3d90580d00d6035030072100e00114003000c1b01d0f503040352414107601c00c1d20207110f2556480e000350700322682440c00c2e20139140e10b000343c1e22038140c1282a04841d90700345100803481400129042c81a95204080e0f6848501e9400302c8030151100508211a02080740c000302c0d003901c0302e540003880403540107002c0d03102c0207507150040380c0381d9803002c00320f54684000840140500c2e100c0c0d00581c0d00510b054034291612900f003440002040c030001c0c10000380d9170800203440c401c64840d20040d002680d001815164289080314642d000130314201d035a11400d07600c1107041465523001c3c0c826980c12042c0540064100030158050080584c4241e10903289d510404150040d09241900110311840e160310b03a140fa50b525501c1c0c40c00390010550082104d0441c40087c600b0a64130010646100c10380603d802d404840c1a100424190310a42c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 243858785 1250 243857535 243857539
    0x2043e03010b0a052a060c0315010e1225060305040506130231060e091005090c030f030706060509130602070c0b0a02030c0c060301080303010312031e060305010c030902150f0702 78
    0x509034081441700718180d50b110716211070a41d51b80d0ba8a030100000c0b50720003150082a6031160981802240d403140030750300b150703280c0901132610100420342c0c018500409150447c1940006401c0c41d81d151450310b101a0040c007141c2010702060400d641d403a9110b0100a0026500b00c8110a5803800c1d5503c0d5101c80015003203070709055400c2084183d041400740f0599108403d09420b021001035121240246036100f6540b110280007200d101c40b10900180c030028058900760711a5800407410b0740d400b40300050003040c4580055688403400d29154054444907404a489101300000b048924601e4010207902c4540c0000010307580c100c035140414020115800c1000b450101040381461150000002d00700c8100e0b000440340070401000801c00588004d005441d800c0c1c01c00e000400c00a1b0030900d10b100340148500340801e0140300e0603a214400322651404c80613140e01d82404100b44603081c441c030000c0d02e0741458140305080203a004030300780803503000461180800c002250111041d65000b80d941a41d40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 243860035 1250 243858785 243858817
    0x60c0c0709020d0506121b01030c0201140708060306100803040303050a050c0111131a0f090a0b0705010c080c0c0a20061801090b0c0606040c090302043e03010b0a05 72
    0x10003040c842c000c0000700d0321306001b80a03405140d041c004e40000c1202c400032201800c82000140440110060500740359110b05542d00c48600000c481c03a080380c614130441d056030310ba8003145802d004041c0f6140002d4040701c5200700b40f1605008130b244c00300481e810359405041069a030780c0500710890b502d00c81c0e801d000785554a800311401305140705400030200f010091400310760068440c9801800065940411091103504000b4012a5103408000c0c1880d040020500c06515a68500d0318450b6030028104440c81d942d5507012205090f040345d81190046d0a10031060f081c1003038066210ba0300d1000c0c58020f8550107084a03a8804c0c5824103c101160840260515417241c8a821180c140070181000040c0410304100e00440c4800ca0302095074074400c001802002d40e0303100d6105000c01811400c0e520010084012004000340e1a580205040c6140c80201c0b8800741d4001c1d04040710008600316102c410703511502000400d000c070b120503681903404030f0071030070b5545603001e0040da018800d005041d091280 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 243861285 1250 243860035 243860047
    0x108190f05100e120a090e0901090f03080403080703090807151e15150c0b0601020307021824011d0a0515070c05150a03020a111603050f01050405060c0c070902 70
    0x400d60458101e800d004012203110125401c91940c0c4c43c0100041d42000580fa1b00d0104441e409400046400135141800000da8004130b8807040c2d004410110207902058500090004142e03001d03c101d64400042e00c0c1c108004c14140d95201150b215103c8098004110400781001c058881c0d441034121118451341e0080c0180d0501230710340a4407212581000700001d621000458118080c0070190000e001d541c0c803203c070040c0d5681d100601c44003410080c1148802c0c00b0100050311100c00300894003003501c03880c14403490a406211120300040c03040800350200c40e99000c0b0180d030000306910700c1d009038502406c0780d20041008590a26030661000782d002804141c020942c0d00c210000304400307401480247c0f4121740314400e200074083d0301d94444041d031101700141400301d803096004d402e900000d480c07c0c1080b090040c80301d03480c0205a00341d140c41e0898985041040181c01c000f001442c081c500d00030321032880d00d81c03182a11048010110200024000f81c143c00c3c1e00028410313080507151881085450740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 243862535 1250 243861285 243861313
    0x2030403030f0e1f020301050102030405011101090c03080c0d030e030d090318270204060f03022208010c020f0a05100e07090515010305070c05060a020919030f030f080108190f05 78
    0x2228410a568211071943c1c0104c00401060084906844042e001540382034a4140111090072211141c0c030400e543e903143e960001454030f40308000440c024614251074889a507083c90420700c1c80e1030000289454682c1e402c107000c0000c4290382c044d407a000400030740c0041604060310039040e2000c0b803070783c003100c0d0400201c6c52509002d140d1008031703c41c003108080301c05051416812485140500d0001c261000c10b000511403081d0001d01a40c038523042d013201000301c0c40040e00300e0388000350800030305a51505c01440203d0750420000c5014402680100803100c1180c036126150814118041400da80390303114003016280c10003100e001404500020070803407038810708000440c1400d1140900086c21300c070100d06030074800d00e031074810395400a010300b0b06074807280c0c8004000d50000400c141c00404c840302c20070b83e030070084580350700441c003c3d13688006c048410b1030001c111100160059007800b501c100184061a00020507610035131607594241141c040a08009148030b40d850801840ca20810341d14406003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 243863785 1250 243862535 243862543
    0x60f090a05040506090601081504170a0f080907030b0402060f160b01050102060f040b15210102120a060b0403060b030a02040509010b090c041409040c120b190902010c020402030403030f0e 82
    0x154000c4040e10805d86801e9220784d01c401e000e1156000d2503110390394050300304515242442c2c0048c4664280241c2c1241c011810900c2e4205070380c01c1c0c02040304007034030346c3d011600100620790280c50800a40304160865071507001455010300302a000300700209654a003000741c10101d802060440035444405011407800c202a800b003401135900602852000c52040340703441380024002c0d80c0c00030305010703a55101c8940d0002200c07500022a80003841383c4030f40c1d4414881000c1c148408200710005030740c400c100003c00030350030005000e00c1040b074078040b4100011a502001d071800ea0f9800000410403c04000010380f608030240c0000e580149000c003130140c0719005601c060900c000a8650803000c0c1c1e205c0c0f20780030361406188500c0b82e0316209402c0300069868200716090b40244503403001c0c4402030321000300107102d8504a00454000070a0014010a113117111034210003090f9600090001c400d1070380c0000d0100502c0c05009005507008030200f400c160190308804c00e1050140740400181c040d001e00c0580d9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 243865035 1250 243863785 243863791
    0x1518050604121b0506071103070509010807030614061008090102040b030c0406030c020f1903120f0203012301020703020d140d050306040e030412021507080a082502060402010305060f090a05 83
    0x2103440700c1000e200640d83c042c038001d001c50b400105201d080002a499401d5407958405045915008100011481e0390710f50340254040c0003401c0080004030705502c2d201d0112000d0001e40208004071200b0402650348020252a02242c5031515046603219080250b002e40101d81009401a001004000c4114403910243c41114800d81d01800130059290040e6281c10810080c9100e5400040c41400c1051522460041c544e119180410410b4944c14490003140c0b807901c400311060381c00000400c80d9807040804100032000082824290038174010003c6d40d00c4000c5d20000b0700a4000c01200014817007002d04006456200105030b6200c182400401040e0b540700302c0d480ba104a1030030984d500482400400d840681d40d4600f14101501c0c0d01d5020426402501d6801205080007007120000080c4070001a01c004a1143c54a4000e410700d030403030004281c040c44c42103e848260350804510305500040d00c0e80c02640a0900103101c3c0c83d46808200f40d180c4400c203143d0001c01403800d004a030101503000e03900c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 243866285 1250 243865035 243865043
    0x5100f0b040b09250c05030705070501090b0c061b190906090f0b09120f031210060804051b03010609021c060801140f06040b090415060807151805060412 67
    0xd01c000c440104403c9103003c0e103203050701c162550b141030100741010410003400343e054141480071070a15940d280c036540c003030503048803250041441007007107503048207550014000740b4002c80c2c10500480302c000d54403e40102014071008081400103078011341d00040b604000b9480c485002e0130100076401512001c503e20448000840d48040020401200525801a1100a84580c0c0380c41e0000c0c0c100040d8404410a50410f401242050f0318020010070041c01807110143c200344051a16102801c00982c3c0da0b400782041c0801c0300108000100c1c04034020130440c11410001030417207503080c003280c0100b4040d009001001c0c030015141e900c9200e0b0850010717030380c98840030030301451707880b405d500d030a0303c840121000800c40c080c404140100c4664801561011015000180340d1405200040e82c007001540c06840303030304d0300500c400780d200c926010b600d001d0700e2400e0050550514201c034110840700030146e43c50030001e500f2020300e0842e0110364a1402480c0080c590703521907446100041503a603061000300d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 243867535 1250 243866285 243866291
    0x150c031b061e020a0203040902090a1212020d02030f040e1b030702030c060901090203070612020705010204090506030d0e0f211b1804030801050d020d02281202060a0c05100f0b04 78
    0x4002d070034450086407400d00680e4051400d081c588000301c0e011350401d003046a407100302c030040072501801d114103601a8901451401c46422515070020307042c6403081c5010811900204007444441308000e00b210b0841c0c0f0314031996181030380c1d1910304191007640c16801e450460000400c1c040860f0303001018011300c0300b00200fa6219500e03800c45190885800d940d009400d03800000c02009120702901d001e40c1c60901d6004094a401116514075007281d11982103004c080e070740c42c002d200b200d060810080b1111090307030420060794034079a0300045048030856131261041441c1042001c1c0c144052002014a0030000d04503540a016107a030f010340020100f080c10300a40d21110b03007807109608085914010f42d0185c513501140c0c3d080c041030040c4032203149000d0340c104421451103401070300c81000a9205030b04138512203210125608001101408950000c0d9030403c0640790107001d030385d490044a074825100d0401714031424031890300905040c1050702c1420321a00d0180c240c0c280150326004000441c40850b010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 243868785 1250 243867535 243867581
    0x9031005180f0a080c0a050304060c0c0b0306091602010b06031305061308040506031e0403090f0f05010914120703152d09020f0d060605040e0601150c031b06 69
    0x610365401c040e10004030103a01031090200413a03070004c01045001c1003407050340d2146d035480d2034240c559071299029000080310b046c5000c0030301400341e46510161030000d10080c03031400c3c6030000506014000c2d1410040b01584c40c40b542c171140c000d501980c036a001c050130700340e12460070b8020758282403100041a9542e00400002030003070004a046841c610b43d116104030300303180c20203041c054030381c01c0100804c0e0b0103201902c001661043d0b085185124500c00d9441c55100c505143c10f40060318001d5105ea1540c401400b000e201682c0c108019509540b010740e02c80115154100000d172481820000305040b50060764030210910035103041c1c0481000781e158050205d4050902031003c03614402d0440c0f1a2050400c0000001003940e0300031900b4940010030281e0810580000142a1550904100e400380e994410411860034580902d00304a420280a0044c40d89011705000b8901d52030050b941c208144611040205809543c0303220f4196800080c1426071074040c5000e200030f082034407002111404101c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 243870035 1250 243868785 243868831
    0x2040f06030203040c060f0e09090f010c0905130f0b1504031a010e061210050106020d09080a110d0f0c14090a1e021c2307090308040509090309031005 66
    0x84a001c4c0d54080d030500300300c62801c00f003201c00c0741000c05a07404000c40c0c0140071109948280c1c0b8680216507032405007003e500c1c0500d502e8210340c8007450300800d10584400401040d40c3d0b0201c0c02040ea901d058020546100209004c001414658003044d8008140040c1c407450103070510181c01600d11800b24803420034000c0189840034082485104040721510700000c045080c42c0f4135012081d4006000c50314003455002e840740a441c2c09030400c10040e80010481c1c80791981c8010f0040051201602500e801c582d1500c40411845104030018001e0ba5500c00d114100100389664607101b6070406030f900112034a0301081c2039001d07110a04035104440395008102000070b42d1082612010181c0c500307084000b02d100d20480a50002c0d4015002c0c1601d0314880c0052600e5030083c00340414064038000448180c035600402048405000320b4100628010244000b4001030210307801e960f01211900711540d00c4490b0130f443c1d403040780304441d05400ac0c0c160b49012203000340c108070b0144045552554141801200c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 243871285 1250 243870035 243870037
    0x7050a030224070e010c0c0324021201050f210106050111030909190f05040b09010c050a09061404120308010302090105120606041512080c070e040218072102040f060302 74
    0x49800031105030702c00490b0752540541c4c0c9a010500060418080e29092902c404851a40c6948156032811884070000c1171042d41940451107a06140402c40c10010003807415043c40105008032070141030081c0f030306000c56403030003101c104825510401c00301c3d00d02a008024041c0c0464820300b4045030350114a003d03050b00200036155601c001500b400019a207550b070032480850681083c860095541c0c415072050130103030003035501c218003030202c4a450b410036007a11800c54103d4180802000300601040c240707107038804040301c100c1d001403500080490312a905110140718503403009010040c04a08039003015080300d0301604032802141c080c0c0082eaa10010310686103e503c0d0250b1082d0000b00018080303160641c894480d115203800400c44d00d5403502100900034121803411f595151300411032010072074080003c44081c040010900d034560a01c0e1380400c01d00d550610042269510300070025000520440344048040300d5203100285203481100030320001e61140c001d5020740c6c1c00a21703007c0b82c0c80c3d000740 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 243872535 1250 243871285 243871333
    0x5040609170d03050a06120302010b0f0607021f02011508160609050a0306090f02060c0624010804020d1b0915050d0812091c09092316030209030307050a0302 69
    0x10014080002c0c200344101c00030f000040200400340e0b41c5400100c0e020002d0080c504d825880382d00005050b42e113002c100318402d489484a244140c03800c201100c01a211082d41e2480c194201c0c0414190b841d00c114241d025040b051131150125441200000b23186000051207516105102c2102110340c2d02c2d003c0840d44038090f402000d40005101d4810000a441a400945c11038020604c034141c050701c5500042965120305107040795a8000c900780828403025a212030110460901e4a410115400d0300181c0f03102c0d0014000381c4140103202000c41131020034107255280245c4991101c0402d500d078450701d0b000b1b21044c59900e0aa005101000c1158103010110008107a00a0141428030501c00800b44072101c004060b244640554150349002e80140f2003094110036190700c0d01c0d44601d08007070f080002c0300c1d000114081c800e41d00160321000145201e00240d0005e2400c6150781c4030782c0031800240d019110303002d11690103220011302401406004030300150007600c00d81c00d0b41c0d4508010788034442c01607492 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 243873785 1250 243872535 243872579
    0x50d05120d1413080a0f0210060b04051305010305060f040501140c03090d020316170c0307030302030115030b13021b0604120219080a050304020f06030405060711030a020604111f05040609 82
    0x801c13514005c035004013201c2c030907001c061040700c0181412642410075914564004688510701040500161400e0210070002d070705002c030708019640c0340d0307140d15585a0010f4000c140c07110328017012405118007034101e8401e80345110141200790a00c81c20300c0c504c9620445450345d581c001d480706010080c0c4007204641a80006054641581c4019243c54800009802502001400401603028010b40500180200754080e4500680300c0d032410356860074102e085248881014075207004507806903a140c2d8548400000740c20b005849545103081f00e0200442296071100303500c2400100300812540f8842e9142c0300d440303607081d40d03400400303109010031340c482c1c1e004000c140b42806d200d004012031152029541c01400188500d030450001e80100780aa4004d803825200340d005002003011850f00029030b80840f610b950b004500e01520798200946a1002900c020140d003803500c540c50450303a5026510a5800c606851118259045000075200f58040d116501c0400c1ca03125000800c000800d401a40741020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 243875035 1250 243873785 243873787
    0xe0709080d050429120c0301031509081608090a1211030601030803010e04080d290f15130b190f0f050304062a030207110d0804050d05120d141308 64
    0x41100d0000c140c4c840142c550b842d0b00c000c1c480c8020240e4aa0303c0030b0300036407100208a540303504505100b9030085040c0030300341400f810102c045002030100402c44061203d44041094801028502031200d0300c5000c42e03203076001e2408240418604191040c0221759482017103405181c202c40c109058941300309200c042c2658900740010010310040b588015802403007130007480d02d048145994401241c07000006409003240c0500e0003c1055041811480c508504403154407407002c00900081ca1515005040641000d011035480703100c4a454440d4030180c0401d10b103450301e405418858003006160400b04200159843c180700d800e040c06414942d19200391507a88510396551610740002601c400818014400a040103040c40c240c80701c0ca0301d1034120542e56000d030755644c80b0700b000e40c480700084c1d0007188120031032246c08001940da14110360403108240da040c3d415102901b0b09508101c01c8600c21113107082c000651100e001080e9115003000012001030010035102c0c40d64000d60f00201c210000c0c51024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 243876285 1250 243875035 243875069
    0x1d010503060c0c0a06060f03140708100905010e01022206031a061b0703200102060c19090f03050105060a0e040b010924090209030c03031e0708040e0709080d0504 71
    0x4442c402045441e070110202c8410f0126079807481c0454016a215203129034020300280100500540340800c0c0300c0e101002030842c141007164950b2500070340c44852815542d00e40c103080c200035080d00304071100301c5150003c540b41e0081070b582c42480c1c1c41da000d02140000640202068560081c4035a10240820b5074071038904641c0300c2c05120706a849030344022034030300ca601d4000384074a03400c1003440003661082c409009464501400c0e041401852a034490640d009030041201c40c04010707054512203102044604c480860b401c00a5821500c4c40c1c1001000c40c05a24010081c0601500310b03038010202651071003141503940e078464007543d0703099400030f000218200040007100340c0307600040b048010800e2030201c0350030307480e800c100440101c0d400542c4042d004074010403140703003c0c0810720700d42034240c01540c9022808212515028072203001d02c142c1c48c0001c00e001d0308ac0b01104055030080c3ca40e61603490b6407400e0540d00a82200761034801c0402520032002c400300030510071350548040b00c030080503e6000c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 243877535 1250 243876285 243876301
    0x20d0f0302030415020a020c04051605070b250201020c0610140910050303072303030603061b090604060c06200a03020d020d150312020303010b1b010906020c01061d01050306 76
    0x94000382051320000603580384003407100700910080035501c00f40d03002000411050400d01054460040004514107140195003030040c2e00282181ca81c0b6620a45102481c2e44540d50b422005e56882c80144020640b00550904503070154018614858031900b15001640d03400c049502c035207450b000f481c5c44092030712821480c03410007e46c0b403034100440016054540761a50042480c40d00410000e481c0700a2923060b448074200b0003c2ea64000000001c003540c614644030f03012039954000a0143c0c11483c1c10030615000c0d564044056586044000b880c156a8940d034540007024070449080555901d80340ca050031700c440d07081c00651035034030701c0701f007412818022800c40950007900080d01890b100c1d0340802030313141030401a2044000307040b040540e2020540c114103001c500c2a9402a4038015984204014044d504999095442d0940c092103140001e0f140500380601500b81d545000300340c54000f0580d10011203044d0007100c2a42d2203034101080d04a4440c1405440840c00c2c0308858041e0401c4010880380 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 243878785 1250 243877535 243877537
    0xb150f060c010b091f050603071416050a060204060e030d0e1909110a0801060c0309050405060f09010602030d0c030b090105010503040c030b09060106110307121107031403040303020c01020d0f0302 86
    0x18241d418000510080d0900c0031900100c03007199192202c10314144081c4080d1240040b08003d010280d91300c60441c544410064004e003240c2280d024003440c00306030100c070700c072090b200041019440b00c15a094a030b6180b602c0000b07500180505030204200c1485071445041c0010703d99007a441c10313950960f650100d00c0904c60304a10307081d90060700c1540344070f0104810380300d8001d43c419003005050165071000e650400424505040e00014100090003803440086503011a0110540740c08075030005140e1251000140c070030b508081c0307450708580d44100008547e600031001e800b400c1a000c0b004d020402002008808559a07445800ea0207110070005110301d5102390040e5510070b204d802c0c20f850080d00c907240e03002041e0084880220503400440140001a40012071202a9190500450030000d260703440c1c100710616441a40700b00504080b001e01076150420564008681001e2801d044041d03016040d601c80c0d1050200750003511030b24000380f0480d44001480ba03c065102e03903c061b1060808241100a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 243880035 1250 243878785 243878797
    0xd0836010f170702160308130b0315211603030306060905010206180a080d0204050114040e1302010311070507030212030a1202130b0307030506330706150f030b150f06 73
    0x114803a207400d070170040381882104c101642c040c0c02e040d80c82c0c10805100a18400041c0c20204e20a034081c800e010307004505586c0d910312010308a900c19a1101e031489103440b07030b1710381624004007407041540c2024490310458042007501d00075641441104e854090a840e142c5d524810070740103a00040001d00c1c048102e100107404582c030281920240e1506403030b04261600980940310031903500160801288d82c0041004e10105081d403442030130185400c2a020010100808994016252000306000c41e8829070242c0c00071070f03e95008c0c548410f040d0414030b59801c02e03404224080d094902c407000410382c0000540d9030102c450341d108900f00b4110354102c0d000e500100511407000003000703004330f440f0340034002a51040a486e03500003000c1c40c082041140311a036000060203070003012900016201807020f16a00d191103c031801c11381c1d403219460101c0040c100c1c000c0c041c031138030000400400e2242610750394000306da00400040b0701503102c91f10b80150780103484030020b0b840300c1709030207924960a00c0006046 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 243881285 1250 243880035 243880037
    0x906060f080901110f0301210c05010f0324030614061c050f0601031a070e0303040522180510020414091905090d030c0e0604050d0836010f1707 63
    0x15111344c41490b0000242c0080d513917808001400b0006015415460328445280c1d00302c0c00300102c500b9440e0301d44401480c1a406040d04001d010282080c009000381c000390401140e084e511860f00a0303040c540980021940004ca44550600300346441106070b00305210700401c40100880002c0380039142080155001700f40854450140ea0340703000c900d800500059000350f0041c05c000300030140050400c0d0031018000d202070144400f140b0410203a8a0000a56041d20310680e4103202800d0214490000b085200c20f038882c16504021b8610864415500710130003991080048a28809002c0d01e6402070f40070783c0c010040001142d000040e640c0c80d07c1090f494108440d000c13210040150400081d0644000715094182d40d4440c1c00d0842607294540300b4000c4550303007441d200407203101c6803000802c0c512440c4a22441014141130304c0050000c44401c90b4980d6111144507091240b920542c201b04e001d40700002080010100c0c410308140d4051848003201c19855503840f202006000c42130b03014038a029140d50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 243882535 1250 243881285 243881291
    0x10c0c0e070c0b07030c09050907021b03031608121806060108130203011b080a1517030f070c0513020301150f02030c070b0306191a07060902040f0b09010906060f080901 74
    0x220200f481d0806880c010380080c1c0c1c01050315003811901501211031984024020601d00e810003201d40e5010449200741e814400c018001d080941000a14500810b540e91410701e00c14a00350342044040002888000005958000e0302e503520804480a14040651142c40c2e411180c00612070b0762180004680c0143c44046522078810107401203401c5900c1c0c81c051180254411090294540c2c00203c004d80c003001e0711105002403100b011000291004e244540026010840902c0c98080310034000d81e20036404071100541c4a0810781008000c60f0b009204080c010748041500ca448a0020f000f124145c629000e003100130740c00c202c44100c80300d200940001e0114013050200301c10040d0180100300060241014042c5c4a0801904000031440e519000c000106115101004040001c003517100c071655888112540320701c9030307090410191550302030096000f490300c4005229520241d1020078040c0341520a100d09a89900c20305040310507500941021440200d460480135102d070b0603e0350f102c0c3d003050000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 243883785 1250 243882535 243882557
    0x2070507091e0204120501050a0506010f0e130e070e0903161112010e0109050c0306070c1203020706020d0903122c19050109030807030b06040b0d1d1b010c0c0e07 71
    0x10003c9801030340103114a07244184021051207000d005441d00300010101c20421410001e001030f100021000da41010302c0081d030041030983d41c8800c0071801310200341c0003c1c0480c45000e41e000791500c2183c050150100340c45008250035074000820382e01a00e0304005000c08041d442e8903145044035003680340690151840f0070180c01020280216804000e00d0000031495245601c3e0042c00c01094141d1107020740d000004102e12198841304000f82141c2042a80039403101e40c11044010344911600580024000a61a80130a0326a40100d01d5140242c1d100c3e48002500100c000650b038050800e81e1140c55070f02003002034101e0180c0d078422400001012540d01e4403460799007040c0c12101d00c8050390340fa559540880d00741034200940b0b9030320022601c3c00b0055407064000282a0740110701400d146482c001c0f640320048480f03548946020310010717128800d03080c5980303aa55035509050791800c404c911882d01c00e000d2940694241034003142d0018507220a14101220072803039010042c01c03003040254801309 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 243884892 1107 243883785 243883841
    0x20c13020c03030f0c19020a0b0105030f0705040f06030b01030c141005030705070201110a051f0209030a120315030f02150c0604060c0905180a0606030207050709 71
    0x1241d40880d01e40c8200f1443e50b01400900c6d04404248074030300d94500d40c00150b40350b0f0103131150b100b103420342e83c891081c580c0381c0f034100c8044c441943c0701c0c0d0014000c03490250400c0401c0310040c480081c1c616900d0b140d0082c519400c2e0300558030342c181000240030120040d4845000d4035415542c20400a088070350017025440000d200d101041408107404045a11034a16440c036000e01104442180803607041054951601c0089003884074174481807600210001c1c02074400c0000001e010340f00d0b0b84040d0302c640d03811900703140b0110f040642e01d070305c01d410104043c2442c03070140d03000f80900501c0300400e01c10301184014003003440c5080c61062010140495001640c00d40c481d50000c0086500d03400204d0039190f4416540009902509500301c500d4020103644000384135161000c400c0c81246e503a1003094040744147c20b000780c030741c1d04038280c14030140c031207a0080820030140c002a55003002c600c0348 = true := by decide +kernel

theorem cover : BRFrame.Cov 243705035 243884892 := by
  have h0 := BRFrame.cov_init 243705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 243705035 ≤ n) (h2 : n < 243884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
