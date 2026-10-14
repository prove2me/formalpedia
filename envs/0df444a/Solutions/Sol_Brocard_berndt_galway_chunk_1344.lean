-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1344
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:29:38.629287+00:00
-- url     : https://prove2.me/submissions/c9397d67-c18b-4f02-908a-70d22408127a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 241546762 ≤ n < 241726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 241548012 1250 241546762 241546777
    0x30b010e10120e0d032a05030117030f0f030a050a1a130605040501080303090615010c03051c11030108070b030f061c0c03032105070c02040b01050904050103050105090c1005 76
    0x200715034541d004408940c0644041116483c0718002c4d084c1001245426801c00810842c04141002685032140c0210b141c0042660302000000c3c1e0510060000328201003c800043e00c00900310b9040044005168a05a0040c04024901c9202005216080b00d01d8003035030360030188503201404445d4001e042843ca2500900380f80c0c1c891044aa10b417002c20996600000c090100034006010035070f140d0401694a500076100e01c01a88581e034000780b09243e4000700224a000160354a188031480703503c0807a61500310f01e43c0180c1d0514141032144001c01c642c819180070800d44541a500e961500c8441e07414800070f9403102c2041c0750f040042000860780e144c41240c0c84141103c886400540400c40000810000b02004040900601021003816001054015040d21150b072a42c0b44030201c6805074161101039401d86c2c0071034140c0400e00014501a004020032200624040e814081c03d5000117081d90001e03441a03c1c0c595481d01403100e255828044001440c60941c1d5400c44504400300081c494480d000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 241549262 1250 241548012 241548017
    0xf060a140a0c140a0504050a0f05032a0112060b180a1205030304080c0703020909011e0606080a09081c1a060304150b1302070b150a050307170c04110a030b010e10 71
    0x113a1940114018010b8801801c00500480300b45070b2a480072065842450144510901c1040c1c40e800c075913151903524000707c0114001d10b4809207000d40040d9a0038034141104c1811986468001c100011514080e05c080e85141c80040416040d6506110b06c1c01c0c5a5041400f0300c0000b0400c030070204000004494110390300034900755a441200c1c14941c10701016410007580980d0010034800508015006a801c2c8148001240824000d0007003500450703074503100f03000200f03040500041102d100395008030b4660780684210791820404403204024150090414821280d462081c1e000034400d00071a142c5040c4103a800c940b9608064541d518480020781c103120729542c503000c09039090780715055149200382c1c281c901035440d15030714036011101c80802c03110543c24180703041740c4014524110005030708440c0c001d0050101d0310304022219000794103e98640b00c1612864244120710b880b144552402c9204541e40c042e102c0040c2940101038804c2400c00ca0304000e80c2c00f5540040b680c600081150214003070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 241550512 1250 241549262 241549267
    0xb100b04080d14120103120e0301021305010e03100c17150303030402060d0e011109033d0605130e1005041101050903010f050a0f0f110301170f060a140a0c14 69
    0x45058800500c01c5100c4d103211000014000000c00c08541030314944120903841b028002c807903803004c0c94200e001d1001301048000d1001400c12640d4092503110717000020250643d03071500810094901591150864200010004880c0950b500d0724004001c0e0410b4502d85a2a00140b2460000703030789000c0904003074414800001c00c0304d4480c01da503000040c02201c420091088102c07041007110560000d003902800703800b400040800340d1744601038810320010800da092810760700f00308038210401000d1244200340c540da2803011034550350f00f600d080207100c1c40c0000803c0315441200403600b403040c0d07041c05e0040c4600301400c2c407000400780d200080d180b41003031030400d0f1100100b8001a02401203608410351083c91314080c04409200340c1c2000d420211442000d004032603000d03507044211000d490600b03000f910140010310400402c0d040d44108031070314504a50007103031070206447c1005400e0b102025500e40c0c03044004c42d1204a0142e103544645015001c00901e004181c01070411000003044080d0340000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 241551762 1250 241550512 241550537
    0x5060115020715020705010f050903060f0a110d0f0e060708040803100b18010905031b090705040b030a020c07050609030a03030e010216060501031511070311030708070b100b04080d 79
    0x2c1082c0001801034080300031050709260b00c0691500254000d440c0015009100124081d014004541c07030032a0150046c07240c0e0b560850402000b400142c1403d8009480300d4400d00600034440162a0802101c4030000b0b036034034a45031042c120f501f009419541900484100500c0d59082216180d00030b0304028004d55a40e5801040510440560414424113001082e422a1840076684105110000f0380318520895241e004040d500c11103140300d4080490f400c0385104d01c609022014070f400a0840c00c00761304060300d503000306d1034170b0304210b41c062402d0340d002c03e10307d0442100701b21043c014201a181180707481d0314180440c2d125109a100030b0700f415200e20401908103425411034004240010640f003420000d071170408081c010a00c81906c15543e03102c51800708101610030202e91a880c0030310325150403080e58041c2d82c2c007001140315021a000912054010403910401400403620848008456240c01d502500ca4801980c000b81c03091705050009004451000406da0082041e0703040c5202210301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 241553012 1250 241551762 241551767
    0x3040b04031808030319050603030409090c050616050c010914010318051f060b090d17040b03040605160e0901090e0c0402040620010216031409030604050c0f01020a05060115 76
    0x6203040020b600141180029480f9004000b55004103800700c901884103c84042c8107080e2082a0b891035410303081000704100400c201c1c0e001d541d1941c030840d4290b04450717491000034a19004000c0c207045149a00303005a041000c01d01449100c1c00342402c000c009d0904040900d14034400344c0d0845418156074400c1701c80c1828407288007140c1e455009048800354040c4202515500c0000d040700a1120b080800208800411209445103901d0140c424001e411494036140080089601803100d0410704002c0815040301d40002544507500800c3d01003603505150740903603105000084c5090400c84070003421140da070fa607441c4050445150b0740380424800c4158480900305088060910750051000400203842904800d02c446110340040c5c50b0303641118003038015801e070300c1882080410340c10001c90311400039000d051850014000540b80904150850000c02d0dd8020300780c2d0242c07020f070320000c0c04034601d2514a100d04805002031000d0803070450303140d98040c0d813a00103000304100d001d1340070f007130005652 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 241554262 1250 241553012 241553027
    0x14040f0213090602180a080c150d0504050c090a0506090105122b021221071103070309180905120703020c06040e04020f040c0e0d052a0a0e0c03040b0403 67
    0x250341d02000c11504115103070140013580180d282e45003507100c29500d48a2440d10b42031a208465101c000342951204000800100b52204941844060740502000901e11058030840e03103c0e61042c8000c01a2403070003800c114071400010142c50080d4100740400015845010f000c0d41117502c180e64480e82d0450f60354995050000c8081c85c0f1050f0740b400314809540c41c1280145948109241e02555248421000c010000303218507130300c01400702120a2415000c216140b000e9500014500d13081a000d0704d118001030641d84512401d50000703110b0301d005d000035034020810440843c0015410010410b41d6540c51f0f8580039400d42c3c5884a0001140302c509050091104d44c00340306004044e10303642e0343c40e0202b4001d07280007518103078094418001c003111035041510840403014400e844a495071a205400c10001c040001002c941a000384204180881203030100c035211245d030b0b00400c65001c01a2800d02400550a50040070b19429070414820310302e0030441283d8100d900000303c7c4441d80d481c0d0a0a4840342c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 241555512 1250 241554262 241554289
    0xa0624030b15130510020f030a0c02042007031101020408070317070807050709050a020a0507060506010c1b0501020f03070c0b0307091809050c0a0807060509040f0509060601021014040f02 82
    0x2d000000d1569015510243c0356090310700403540d40c0180c80d07242c2002c0781d07540c0d860aa41c454980c820401465500c1c02200310030307080ca10040c00803d010500c08043c0d9032040c8100c5240d01d250102198402c10160407210103090b81107070000031030500d427030003810f560360b000c2611000d404005000e40400340001c141c8202c40c210b076002145143d50340c0462500c103584110ba813099072142403500b000310b51014818001c5074601000e5984e190300302502c2e03840b03040041c003029003100d06210310045c00000045440d0740c0003010410308408008160700d030100190500940d03404050703050304100140380000b21502010f6058850209015450369a214019036100b80f42d5041505004000503c0c2200511560400c03440c46105400b9560844000d0382030240800003400340c0f60540e00403800c1401040e12500180c9000a030040002c56410410812902205e10982d40c082d015001783d8100862960100000070043d101c44c0d004124124600561100e000c9000e00300900b01c49158402909564660070280441c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 241556762 1250 241555512 241555549
    0x7050d0e070f08060115050906031509070e1203120c090a21110d0506180a020405090d1707020d030c11010f0518070b0d230106080a0624030b 62
    0x81c42d03201e0012020400341e42c03061600d41e1080788004100640148580f058a800c10380b902401c00302c8070b400b0000540c1004110b104d0364034540c85410f205030b54551032a8020002600c031301d04802755110500105030721007a403654460b8020044542900c00400c0c1090780054001d03500d42d1035072a030200042080500da804038224800c1143c5007010b07088401860040c40e88101c000184500442c018071400048249010708140c01003130005111a49581c0401c1d0400c100308180c550070003403030340010126041a031700b071001c943c401c1040044482d04403480480c400d03650354002c0d0081c80c1003d0000d40d58032148038044d00b0580c89020440429016400d8842c010171218000e104400c0b8014050b00101401c0701c009604160721070900000a0f008141401520903203504185404004440e880107413001541c4900c03504450198000146070307848080e4081c205668a03d0540e013030811000302601c02a800650109004583c0800c2240e009034107900215140d040c08100701d270050380043c140074140c0c1c041041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 241558012 1250 241556762 241556773
    0x130207020d1a09150403120e10060b041d101a04050901030305120a0e070618050409050307050105090d1d03010f060b040501110d05040e040f0c1d1e07050d0e 69
    0x100301008404681c032030101d00c401c0304d809180110300d400c0078035016900940402d003a50380218007003003542c01c2a00030085940131605c040082e899400200c4040350301c82031580c0e40100d0705001d404652003010010304080c00c0c1d0b40c4c0a41c1481218034400c1c1100c0c0c800d41511489a89840c09103801e81c10527100280001014502c29607582d04014006500014400c0902405080042c0310106031b44038a10700c4241500041850314181071096440c0800c0d07000c02490789404c2c0d1070010b101c0c0e030380d80940703400381c0c0c402c102654840100340380040c00d480713000e001c1c0f00b00c54202520442c0c880307521840405000110105140540440e200401c0c014151607140218050520001042c44c00d484402841110001e980d03800c807a001480e107064480d0354070f0035501c00140041004201e10441c401e03a154100b0300400c001205840e00d80e40307803210014940d00100c0020710410140304611881d90080740c1c8000901c1c01440040f42004000f10403c100608170020303c24040f40741c880c018055804a0503007000d600483c0c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 241559262 1250 241558012 241558043
    0x1203090f0620121603030b0901060207140d081b2a0f0409060c020c01120e070e04050f030a0206010e06030604030c0816050105010f03050f070b0901050a031b0305061509130207020d 79
    0x10f04d288681c00540210741420300360442412300302025412900144c2c0504489410100007843c0c0e22000030000340c3c801144034102e00465000c00080108911441010181d00380721130a0743e01b006503007024001040d040b042c42d004518100142c0714510542110280b08805c4a140050000c2007824030243c0301034a0441203000b8260000307121404204242c980d40341e079901c0d001c1a2402c0c0ca0080d010b070103042d000720300c1c1040f182c98501101030f0031a00c0340342130b1281001ea03a284540b640e0001e00c00900140d0040340100700d244821006550405e0082c0d010300554901501c014228240c0031074000c04c2501c001900c1c0c0d040103561003419485640c000021310095039250301c40001501031740410b440754001d102c0c0d9040080000202482201c090030340d450f05224207100155950340042240c0c82c14503448031400c3c03501d241b41c01d00701d84001d80580c07070000d241d040480c00d00416409a000783c0d03000050401c010308195591172001c2580101e40034026a0320034151001c980100d41d0301c50020302c400b105030000c0703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 241560512 1250 241559262 241559287
    0x15030f1805010522030c02090907030209100509010f050f0d0c08010207030c060c050307091503020706020301060201020304030e040b03192904060509060402090a051008071203090f062012 82
    0x2c9010303403001800012450b00024520f02c104298084c0200484c0c907007103125005040506440741d00a17901d0080d221019641e4001c100d0010b0111000070342010f111301c3c140654039000880a0240240702500c04610742050040b0b8002c07601c1240b100e00c9401d503460a2810844406000406000c1060081d500d48800d40703070103008446c000f902140d00710304000c54914890b00c20307412350344a18455960014114581000396828004000c203040070103408006480c0030540d60f00085000b00b0302c1d60300040c1d980c0b0b00750500415480b05100c0780351180d030404038035882c0c9540025a00880e00030192040c07005a195251840036140d85580c08580d010200508103400d0201c0f00c40075100303500525041c8010340d908030350f00c0e44852046400039400300385103001c0b807801c2a5551000740d10000c4a0b4656403030340d0700e540d0610325007000781d4000404c2411300100181015402103420b00202224032100c11801c0c01e01038040c0004520070b142d0b401d081071221000c64107841c204400509082a044400d654034002000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 241561762 1250 241560512 241560521
    0x320622020d05011409060607050f01051008060603070b040b09030313030b060a0902070b010b1b070b0406120203060d080708040b030a05060a1401080402090711060f011e15030f180501 80
    0x20807031801e0b0000a1015611000e0703120054028641200c540d1031000300a065042007030155a244900c604c850310001091191501404041c0300380400245004e540c1850140002c3c1050b01a8000b88006c00040e074029040c3d8041d18101c00080740c81e491030101180c5140a00c016480c0e1005203001d001092100b8406c5031409150190f908030201c54544201c03030203a100302c4c1c10042043c510940104102000303200030300314000100c112070f0100c03030701070005516100103504008240c200028040002c0354122101c4072100c5030040042d811442c103240010001c101c1d8020141107400b0000d506410000d0740021140901480408280c40341000c0200304024407040303607400e00a20400ba0702252241e154506240200c00c140d6800a10b903031a0303402e0244001c0064030301c405100d2446404085541c0c00c0c400244581c5c449001c10341c00750300d401c6500060910015801c601c0c030710b004400348500392400f020010103c045041c08144140d0710b000c4400205001002d5140040c000341c0a6820004103420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 241563012 1250 241561762 241561777
    0x1b01170c1e0f0a050a0507060e151003020a1e080d1101110405030303040f02120304080c10080112140705090411010f081e0405030712050304050132062202 68
    0x200014880c005103207190980b05070844a5000030003840a41c08141c820001850f114074946440c5040c0515583c03a0800d4850320028000c0c940c0080e121064020146d00c405980090000c2c0340c60082031643d008150310303c2940c001e200600d02801411001c0880042800c401045120100c2e00c0c00e1284101c02024840c070650340c42c205500f8052040300d40010f88040c2c3e0191080140514515203550703452506003856010308903001340501c007114002800c00d2020b000100b5280c0081c180b03098a00003003000c02c0c40c04e006010280200e0200600c014090b0400450030319601c000100802c4a299070071b186010020b5000d50392004078001000108858500b01c180d02c0c4800783c03030700e8201003a41c0c01c094032181000c803880300c030940b46040094152045a0380140d002401401644d00d4510a900e94960807043c841e0f007840458070000030321081207424890b50004185d418608100c001c0ca5265218001031b18615180b002040c0102240c1d03990303140080b10b0b1819100c4880d0645c8011079101980c0690440c0e803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 241564262 1250 241563012 241563037
    0x108070303080618010605090a0302090109060306050105060304030806010c060b1e1e15480f0303150f09090f0d0305010812070302072c0106111b01170c 67
    0x10100f1041e080461980804040c2400c4042d203da0828004440540109402a030b20610b040c50010240e01e030003000c24040d00c0650004911941181440c000741c0314107900c22030154004000300008294000d50407a003120091a01c2044a0b1003401d0903809049594483c991280b00d212143c0000302c1420100300c01043d082d40c03501c0780a803145484c01007180e940c03c50316402501c8100c4069a1418034001400e81180154000b5102080300090b50307802c82011b4000703400c0e05e04e040d03243c1c2c140c0d4488900b2040f16640c140c0081070f0b03a20600d802e1546a0001820102e1441c0e00b2100c8102e43d0341e218a06441c0585000d0900781c424170340904a9507817400c0c04100d2415a000d02d40041c00524401d010b500c2c140d80049004180890500d6503107041540f01c0e84059085010310038020610340b650f016880b026a0081c282401c0b080b1500d0b29206a120341a4441014001030341c0301c40344105001701c0d980038000c12140760640c50b4111200161044003804901d120540b95401c104040719030300c940a03003201120300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 241565512 1250 241564262 241564277
    0xd0b0109060302100e0d0b0c121603060f14040902060f0d0504030320090904141f05010e1e07230d1109150c0c0a060e0102010b041109040e0102120108070303 69
    0x1441c10b48841d12002205c0c1c1c1c11446036220403002c11a0041c400b60040b1441092604c3c00400c01424003030068143c070414140499043c028095a034940a010054108042c0c80e880c45850b14144000320a0003a50842c0101c0e154500315040d0350352081600d0b4034496110907503035036490340113041005040490b401c80202e45440800b94441c1c465903481564509080e007a640b82541690800070340841c0240220707024004000c200d04454014000568913440c0401c0c901040b00d603000c2e01c40d050b140140c20600388062100100315458006000c00142103218110003d410b86030250205d401c080002c014410300307410300c541900401c039030348001c00c3c201103100e004005210016002904e035100b000c040c9035010b0350802240421500f0350004008403c8440c04540d44002c1c13240100d107241120707500040c04070319285003048140d42c0a0203001d8100c41c0c12074040041d0810310804010728002d40300703020700440c0c0e5040e0702c03031104600754101c801c4d0300c2021204a01c99a0b48420140c6c0d90080d40c0011800039056 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 241566762 1250 241565512 241565539
    0x7061103040302123d09020a12050d030e0c0d0321110d06080102030c0a0f0306080d090e060d080a03020a050403170a020f010c0206010e040206070c0e060102011a1804020d0b0109060302 81
    0x20707812151019815040840840170741e4960800c0a802649001d0341d20514468000550b955201951480f09104501410345001e000e400903044403491005000b1076007042c0390741c41255541100710f40d019030707050401c452a5018450821303101a0034030612089945001074000001140f040a00300c900e0003c00e00307221194480d01c00e00d09074001645d0401c46003006016800380381d8019008142c01d85074618000814036610208246000d881ca110034000c0785500c0024800c8001004c07002c0d501481c02da0301140011f200c2d556902180c0b00711a00320080650214424000c81d00c00e0084500650f00195240745c001640b0548005541c400d42514015216040030700f0a00070341030003a00f5000f1041e40140603680c0c40c040750b2400b040001482240d01c00c4081102100003095449a0700c003420301c45400d0802881d018002a0842d4128032202c904c1c80c00d0101040070aa840146407442a003132000f18004607206ca2011481d03100d642c1d100208000215000410f25507003e40c00f0800f140c0c021a440c4030255070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 241568012 1250 241566762 241566823
    0x515030106090e03030601110a210905041a12010b0603040501020c070501210b010306080615030714030a11040b0d030314061c170d0c081501030c020706110304030212 73
    0x220309100c00f21981040c00060720640c0612580c020001240c0b06984c1130b202c0f641d4860245245036040c4003000016107403010403140d8031a00c604041d00056404000c00d1541502e44040e100081042c1e62080940d44a811002030382034000f031402400203004152682003d2415034082d410041d000c0e1014840c1c04000105c5612442c07800400440d40941000d000010f814814045d01c003049015050584588000038080c1003040083c0c810488002040042c400210401d42001115800b91001511655460000c2e036404102030700b03419800314860064404407004540074142911000e50f01032181744070a810725405400440c200004484000d00a580d0746080011102841001c08804890b18100324002204003c441c0c0200d59618901418401840303114400c0d81c000045a4000450030030034400d070418060300c01d080700706003428203004280034808003e42d2807900d4495041042071803007084042403400d0040b60041e50700544001074900c40300d640c0c02d603120701c500c04d004840200380c401000280d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 241569262 1250 241568012 241568021
    0x61207290a09140f060307030218151812030304050604060501230906010e04050108030403150b01170c04090c050a1e0e0d1a0406060e100e0711010f051503010609 71
    0x500503142e2000c1e0b81e04040f041001c1828031200d00303402010040110070710b692045c0145104003081e41d005a540eaa60100001c032600c5207241e200d010f075001c2e6452640c0c41c2448c4003a5007a0503480c0520b12405141c21000a110200c9280306860900000080c8028060041082c91003035010b0007083c03040344d980325000200d528041015031281c800d000a11000707454104440e80d000441403605a8284803e60005401c881c003c0e440b03c90302c0e9000143c01c00400c0109140c6149400c0302c6107042108008003000a00102d80103540342d00d50120303240c0001c4c2145201002e4601a00b403c59007040714014051015002e41c1c002080103002c2141607100d40141c1550008070071102c0043d0f607818603241c210405020184404400c116504c41c1255031382072480003160031803440703140940c0d008a00146841c0c082d01c009480036200c1034103024800c0d014090720003161981e03078024800345420030101101140e21401070110303582c085070351400c1009002d1441c070078400003900480100c008028099072801440c0131036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 241570512 1250 241569262 241569277
    0x703020306010510030b0a0602160801140412020a0602070b100b090a0b0f0f120103031701030507030221010c080709050a030b0a020f0408070306060905010b0a080a0506120729 77
    0x40d070003540180094103001114071400c20756400c010411012040020300340205681000c1c0050740021402c0034a0520401030000511a005c020032a10014131010441448014006040a00c0501d480b00c02d961080000c7c042c01500208219207480c21860440784002e000e642d581c051402401c00440d00b81d0400301142c500d00d100030b181c031a4151600c503c18401c1e8000790071b82070750b007a800d014000c1481d01d200010000102602002c0300603604524010700440d1314014150000340016006000042e0009070030001e503901240d4603c40a1b0081b10041640c1d00c2010f2004055420701100c180c4440d00b12040f1409401c1c07541320354080645550a000d01c0d202c2e58400542011441d101046803225250700134014012800e0003103180540b6901c18270b103000c2055108941c034a5803002e0400c2841001d00c0f40030301412808944034070b802c81e1082c0003841024060321801c1c140d6980d2001c0f48040e91126903003001d0a10b9101900c28046d07070b0b08403156403a003c0c4042591444056280054490303e040c0407514803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 241571762 1250 241570512 241570519
    0x30b0a02030c2d0a05070c0603090510050a0f0e06161b0201030e0c0a0602030408010b100504151e050918060d031b050714010f0c05070902070c050603010905100602070302 75
    0x4009032000d203c029000a0030000030f601110000c25050350034150018442020161601c9540319513915048043c614268000d80c105443c0c51380c803200040b0301044401411048580c0130546071101c030f00c1c0700010708030300e219904114a0a00000c4207201c000c21894800d07220100c00c20200c00d100350301610409180140d1900007501014800010b600030740c0711403d0030b040b10045802404d480c0cbd0201e042800b40f500300d000581d0000ca02040010824010019003403000d0b200140c64044c2d0480c003820350f02403030007a401e40401d4000d00c4039100b4455101d00e003a07042c04104461942044070800b410650251840901901d41d8407000300c03141c0451454607010b40000340806400c03800c60f0304e00f100d0080300e403415940427174440380c2c0301c4002c200d04200000103418440d50200300c03080160000752813179240d06800014042d00c4003920000c9100031a4880c02c40e51412800360b5034000e01e00e003803918074000b40c200da82d0059021001084243c607070b9000b2841244041444103045440c1c031402da13500d08075032000950 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 241573012 1250 241571762 241571767
    0x6080c011701151709060103050f03090102030714010e01090606050a0603090203120702012c180f190e0304031a0105060301030f0f150e0a0c1502060a0b1804080301030b0a02030c 78
    0x880f62074840048140303060300c0c09803c0c4032241402134103109829194500c96620020060050100038080c080c51050603a0043d4a41048000081c1d100d0042c40c8020302654154200204201000c0d000652040c1051340200700307040091800d140100341500445005507502c4c40c010440c00e0181c854007101540050040048800038602c0051640c0104030490400184038058286500701404142030f00c00301903034030402c5010075004d0003d030071a440985840c1c042c4020500030102d03084e205107600f00c00c156030307120000084490040050442c41180d00b8072444001400000c3c440c00c0601404c0d04900301c8440d450700c2c4da0345c10811105010a001c00f4080c0083d044c00d0b0030015940c030111581d1240f00c0e040c82d801c1421000c030080c0c102c2e800da44140b01507400941900041280c00300b07024000c3d02c0e040e48040000314940030700030355801005110380483da5171442030803025902c982c1c2c4400e100540241fa10355601c2c0c2450844030640081c40304440786114503000c110303c800c0c1402902d1003001d08490490 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 241574262 1250 241573012 241573019
    0x20304030b0a0b1c061103190c1e08010906090204241206090f0507020d0207060e060c1608010b01050306010c0308040c080102030a020c15060a0303050a030b06040906080c011701 78
    0x8908240602041002ca542c1c050340342c1540c40b5a0f1008015408100d001c806010884c20702d601500d00c49407190810719010000c201e080800401014440c030500314000680103003810066a0500140d042d80c441c0c040d001e80941601640241c015060340c3c0b0380c00d01880311075079a61041d070582c040d50066003d00521018003040400043e08a400c01c4c03a503e1034480302c40c6004d001910b040754000d420003a90301d52982000103200078107014281e000314080c030080c034002c1c65800c0020b460700f40070f0180000b0042d0317105a0245071f5880e802901e214030039034403d03544400044040c0200d20040741c07007500c4655007001401000b48d03000308182c1e8411081a110300010310600c2d80c0c02c4440700030003001200d004112500229030540248040d5200d900b0040340141d0313030780501d001203180980680d1300e0130000c2e010508014007a2182006202103991504103d5102c0130060810340203800203456494100d08007103000100d281c6290802402c5030111810395900070500c40044841a20006000c404800080c0c01003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 241575512 1250 241574262 241574273
    0x2b0816020406050d0f031b060612020f0901151b0b0a0509070602150711010905070305011d060402060d05180609060105130b030d12020f040e091501120f1a16110c0102030403 76
    0x441502010404001d00c0450950781c51040316130030b03000301c03045c032b0005401c503002c40c1818110280d1141c0d00711446200c0b9894a62018002c40c01c500907142000f034070b450402202e11241039040505903100b6148901e034507000003440020002120340958600c2800300008480b4008240d90032802480341000c00c1c5a035941809940c07803001d803040081550b50300d0040d0302c04101c1c140f058802840c4540004a18442c2d510343c42607d0a800c100401803075004202484016a00c010443d502c03c00c02c80d40200e910ba41707581c1c902d8900030600c3d100120600602d0104440c1410100d103060607110203c0304840c1007030014401104865001d84002c2d00b42d8052010090510700840102c3c0e8256207035500503141a010300040d00d6a41c20a900c10020240c0304800c1c0503010205000c50306c17a00040824a10307140d0701d01081c0450b51250054003a01403215003045609100b0040d601c8807280300100d400b10498204680303201ea00c0e00502c480c3c0e100191480c84010010000407a280c140448142e00650405040d900c81 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 241576762 1250 241575512 241575527
    0x60a050414010f0606080c0408150a06030b0403030e0d0806240f04092009010c0f0602040e091c18230306010815010909022b0816020406050d0f03 64
    0x740e40c980100c440d8208088000d02404a2034150407001042203031030880042d0465502400300030b40c03a4028041071201c2040041c150f00c95070107480300340d41c142e112141210000e202a0300040d04440c0184200003c1c0764042e003200018080b8001200d400c1c1101c8282203a0120007034821951241e4613990100160f1100559249590b840d00000c41c507105407140860401d40c05a8003403402203231120180c189980b19a0b070001c40b0004c0f0011200c3c42e000d07880c000240000e058000c0148482d030345251f1071050082075410744010f440d212041001508001c8043c640d2210041c2d06000546640301d030400300244104040040c2040000d0030841c074030300301340790940c981d03005245208000d010f00d480c12143c2d60341000000d008000c2d18000d00119401d20b1294028080c0581101600300c0c10301000310f00585421404028060102c1915064401c0710b12002c0311000d01d52501030300480e00031400c0711041c042a51038140e498800c076000c104040c2d0b02da0a01c00c0c8142c0e8a030000e4141103152000d54086800f0b10403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 241578012 1250 241576762 241576771
    0xd06051302030a2418030809101a12070b041a09060a08011e032102030d060605041e05062b11041409130f1a010e01060e0108161b020d0506070f0c05060a05 68
    0x16100f8040d1440280000c4ad808480400c030480700c0d52140091905004000481d21103a02c405014000d003011840102e0784074a1240103480581103108001700080b020581c1d00b03082d4001c10b07665440c00300c00401040e407042800f4410644800294015000c096940018100d0340e004151203030605031500e54040071000d2540701019800204800d114150a074031401000d400c994880b55202e80c2801c5002010400c001190048481c00c24010310207542c500040d2000140c00001d607000c480021020340308c01c00382d46180041807a0810643c0d0148541100180040d6180e000d0b1072440c00c01d8440c10040e604070252142d49541004d83c1182000c20009517030030b46103a000d501c0100c4802c00a0088200300d030002d90220b5a401c031110014050180e11210386405a0300919000c81281007d0309261420001d11081901340101d8040d0b001d418104460555411a001415840180802c0c100382d038944108881000000c1c50002003919030602031507100070010381260003004141c1d10302c100c1c070703008080240c0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 241579262 1250 241578012 241578031
    0xd1a0709090207060e010506010f1d01110f0c0f040908040302040e070b03070807020c01090b0a111609021b1203040602030901020409020a021c08060d06051302030a24180308 76
    0x44021a40341d103a40001c00341180b00d200c000072404107108600d821603002611302410441303424110001c0c3c0d540305402008d00b200001b5194200c80003800142d45203020b41410860a01400281680852002c5050741a07041c040e22001d980040620801080301c208403c0180a400c09000600160070598400c0d40c41d050380604448002c0d898040c29122178104030796000004130349508021482c1d506100090b103200080c200341b0400303418103800081034060342e1042d008110042c004031110380c00030080354000c00d00400681418a03122a401340103984010039450034000000004110040e00040c0341100c101004009411503c450791208040d60018255150b50f640034000481c03030034001c1c8001c22552031190020045d81c11500d00494000045e843c6200500ca00c4004029030b680318049181c01444d88284c0000711540c81b001055419054150041d416209018240c030070032040b10712110300c0d02d0031100c40201914a20105105032804000500389072425070301100f00203409124600e82002d40803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 241580512 1250 241579262 241579277
    0xa020d11010e0f030a0e0f061611120705030f03040605070f060605131b030c0e100201180303140115020c011d130204060e030f0c010c02010507080310060305060d1a07 73
    0x51190034507003000b403d140a10b41d003001544e01403080c0c00c901c00a1407484182c5000182c100848001022400340380803000a01101807a040c04209080e1284241d405008001c844135142e445440c43c2d0b42d111034002c032406407046c90480d8410070340002c29502202c10a40d20f041c80d003046039030748817440c0c61160400c43e5119150140402d65940c0c0e0810b2940c04c143c580300000d0390040710041b005841c2c41c00031303140060528140e40080d02c00e52001030405203020685402c50503102c400f070b04900414410070300d441400346011007001015416081502e0340501c0c10340142803640c0302d55041624881c0c407484480507078410141060302e9402184000c4d1429a0706010720034012105000c90740b090700d188c40c1c9514240c0d0005050160340e0700300c0f0711070007120301c00d82c000e05d0386140c440810355a4854176100a03041c410740e900c90508580c03143e0f00b19100603a11003180c68590424a51204044542e8024280880e0500c0001041820960b2001c503c3c560003403c0d0004600b220101d21100d1038010700b80c041000120f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 241581762 1250 241580512 241580531
    0xf10020a0602040603230702060c090a0e01090207020307050111061f050603131b1406071403070b01060219020d0b0606040902160b010906080a0312150806040c0b0a020d1101 76
    0x7030300c0600018010340e1004a1001403102c2c8001800624698100a03112030006015949900040c4554000390090710180d803412100c0015210900590160707207850303d01000420154450380203825a0b07803082e0100e4003a030752520015a9101e00c030303044000481d80144001162100d04032221900b406500c40308204036901c2da40462415442166504649841588803008000034032503041a01203a16a0303024919040c4544524110207140013244141c03030111b06141400390103610700e040f642405044a5507500e09241204152109104140150050b0340d016101519070489803220f103075000f4902d05050901c4d945241d40c0800c01781080b81c00140901002c07612124900c020040311449154000043c8150318280340d40f010140c2001a03640c1c140792041094101c002000354100d80e00d4100410b085d0070f1212160001d100b0010786500c0c1d00c015510005850703d01050746c40c069401810031620603500c0f640321420314451450300c40d00503440b9810101071680720fa46901c00e030040318000411581e68 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 241583012 1250 241581762 241581773
    0x14030a090f1b08010203010b071103010f0606170702030a200a020307080f12130513391728020f1207140f0a050706110c010b0607020f10020a 62
    0x5034801c0841d40301c9074181d48030700c0d03070003080c2c41d450010540600298a190b040c020140e800303024040780240740c02020b6818004030390f029040b594010b00400401c015031665504024005100080025081c1c90342e240420300c003c0c8003004449a61a040c1c40700c540e208115075112403240040e901540180c051042e900c0010780d01401410000e007003001c010b0104030a040c1e40281428042166000c20280410541c0b0050300b03803a242c03101700c0744110748051544402010030005800b01c1c109020324807124004440140c26103407102c5a00e00d080603050100346074004403c2e41e500929200390569021020009100c0c141d40e451b010f001c4024140e4030101c00031503461380c0c0b030680c2c00541401011000200b6540075041120441607407008007482d00305220040b284244810f0310480c80c2903035010000060342c40c1003500440855113640d40c4a8000c00200c41d8842c280201c54101e4102000b00307500b4604022190b14140d0181e0341c0c129001002d481e82c0581440800000f050f1060006095000d01c0c100c0314007160 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 241584262 1250 241583012 241583033
    0xb030708010203070f02160e04080d0507031b021b040c050702060d02072105030c0a1b0302070608010b1806070201020f07090506010e0a060e0111010f06090605120d14030a09 76
    0x40104005030b00c9080c0b00c4d01c003600000e40c0080880441d4400344c1c50500000419041800b20f0f0500184444207454070304016020340f01d2801c000105606010130300c8002a810750118501c0843c00007100c0090440540c01c980b600d80700c00c01580f0f00031002c1743d059900e01d0309178400700313041c4072030b040c03c900c0c1034031960104c0c02c03039001340c00421141035011510070309218428805405500b40440100115078112202030924040a010600300140c0810200c440f580903001604000d9240118142d201c2c1c2c0c1854003d5442c0d030325005244c00a0707003020000a0411003001a41c40340e018512040a0f48942e143c240013850b00180c405904520a1410440c2c01d00000d20210000d44034030100405d40f40380c0440007404142da8848514001c0e5000c490802909074000416864102e0074600441542408001540504480d200420006180c102d00281c0049140e010038115201600d80e1800c908451703440702d4542d041e04c1c580c0c0c000700f1031790080c0c2c002000000307008541c03045200000080e201d103a51074204228 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 241585512 1250 241584262 241584269
    0x40b010e04181703010b03180c0d0501020a090e010b0405130f09120f080f04021011010c120e070501091203050706060f140a05101809140403110615010c02040b0307 72
    0x40e800c241440c4144401c2c058440410800f94203000d2a5500d054010302c5c8611000345207030710042a80d000341c07401c048103001ca807074110300c0101580390003c0700b03003801d071b00075804501c0da0004105586000114882c56031407a5040b00c0526022a0a003480c14040c09400b4042c42c0649600b070f961907003211603013690351041e85d13404c41c0a510380e035413004110480581818086603400f414460079104200c400004030002540c880d50640b075a0720781d00c0030309009480040112258807403550030900d000d006294030440c20356295411150902c803441c0c0501c181ca45454560154900091101c2c00c1408103207000c6402c001c07030724071918150345408801c5c2c07688802c40700240c001e185640038a40c02041030064500c00f1041640e42203641103402c515110000b11104c0e10369000000b0301c0721034040d50800d0031841e5549001010341c1030f018080030005581c5820513136400c44003113010441c423a68000800d10009039540c428804034040c41801410307140151042030780e04070220b80c41511a4015900c980b4188542d4004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 241586762 1250 241585512 241585541
    0xe01110115031a0c04030b0117010f050702030d140103080a050f070807080d1103090d030507121503020108070807021504020d14070e09030f0301090b24030105130b030a02040b010e04 80
    0x48621582d01c40550a101031306031444128140414400702d800741d200b6604640080b00a400c40c0070a440600d4054030044c0078200707240f86044200801180c01200801030804d000c3d02c1004001c98203506105a0035007808040d003030920520880351428003981c0200003040d814200c8905081c11303691000c400b030380308000c116110031010588800042c0640107051071844190905070551030b2103c04940e840e041010b250040580315130110b556039010320328000c1e44088d180801d00903085050340314000600c035840101e002920f010001085140b05500c0742c2e0048800b0380c040d015241000300c10703013001034010b00281c0e40001c0c10f1062100003030b074041c2c44540207400e40000c4c0c0115450410b03b5441040700404140d9aa002001580d864440c43c0703040340d040d0b5944040000b44180c6071804907003500186141400301c101182c4a607080d42c2410b0010310b0484070103c03256a862080c2002c2c540c2130302c03c1e0b0f21b00217401d5404078200000503e00f0750070500c202c41040c075144d01e03180820310020b1700780d401c25500c40c2c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 241588012 1250 241586762 241586783
    0x709140c0d0905030301080703060f0606211d15010b0909070c030509060706140c0c030702300a1101020120071b14010311070507030201050d0209040207060b0405060904030e0111011503 81
    0x300208cad40a0943e980203400e80c00c100e0b1390f140070300241440200c030803140702c10f0500e031001d41c4000c00254043c40340b120320010080241c6101180c0e159071465146003461481900000015810a01108480024601070110303031098590140c25a080484100e04400740700040c0314071079035901d6040c0070f044181e02882010466440312290603091090207802c2c83c08a00b410000600c00303080c0001283c00d51941541c01d03000f45400c114003c041c114041542164540360f1002405a102c4002600300d1b90f00e0144a4014030303101d0304001a400c983c141000343e440c104440610143c5d0304084406000d64a0040020001503415100f081801c9461504800260812007407803000c0355a06208100c014440030380441c0ca050742030b85401d5607456242c40024104034001940c1d08040070700f90140d980b4050064011f5444400e03e140107006440c40002490084d440c240010301d40d0324000d41000d0060390035840724910390705210011156801100e040000307c0d074a41204051418140095100850040300300320f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 241589262 1250 241588012 241588019
    0x1c050717060906060f0a0e0a090b090112050601030305090f0a091d030f0f070201020708100c1b15020901090302091609061706010c0c0302061206030709140c0d09050303010807 77
    0x1024210203420349000b410814100000e82c0c03101011501100e0f14040c0c800e4456414a0040321540d816540e000d030401c0301785000103084105600712804a240407246200c040c1c3e210480f1005201d880c1a0180041d444200104086406000104010702014001030074465078000805c40480d05940a00710a66907030a80001c071170762101c045528041d0311006140340018180d21002c46002c1c004610080c1e010018402046a0003000880c0080010a080d124040a1510200002c007804401e06020800042d1400c0f040c2c426283c80019141e8082442c0000c0421415180001c0d0813103c1d405040c02441000130016903901c1c11914880c50f0701e200000c54403296284002d140b0310700d990214003800294103039150340707204805545900a1080c6071440c0500142d01b490682c0c1c102550010750482c00024405000c284600f0b0801d21458050b0104c9241036920700032041250f0381d8000b00009803199001207800707002104020240c09118a038042408d40300341c4c07500c906592083c2c0c45409a540b000c0c0081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 241590512 1250 241589262 241589297
    0xb03040812180616051207110f03090a05182419080c0d0c060804080f041203020c120307080306060c0f060a0c02010c12090501060902040b0c0c0301150b1c0507 70
    0x5980076040e001c134036401013203c01014015000d4008001c141c048280001107480d44200c5124144c2e1001200300d031307122800d515101e0384aa000000560040600300f50204150030071010402c1490400070302481166640e545106804004000100c11095210b0003500c0c2980c8030181c0000307154140d42008402d0b0714000300b607840e2102c8038006c44e01a030300060049011416080c0b00310200d13012400e0411907590359103059a1680b00303409000181400115001c14440202200b00000381d00c40d03000c54070074a1001e01048400c40c0c600340410101da00410025000071005c9028580003400900103d042c01400c614903420000841d4120010340c2c07010f0100310120405020b04202c000e254002008400b862a200420002d01641807000381c1d521418441c0c2001003d500010040420030421500c45440725005206640240201c003a24803403041c01401900d418410f2035441c003400140603943d0381c5041ca04010365084a0540d2042c821103030500071a0b28401c1c056544620f18941d9001c03e90014009803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 241591762 1250 241590512 241590523
    0xf0f06063b06030a1401031101080f040507140102012003240d0b06011707020304052b030c0201021609090b071b110d0804030c08060714040b0304081218 67
    0x2002100300071440d6042070308500d90100200750310aa6107203549668000800d000b41114001c03d0051010580002061008801007640c442d9400d0340da000f036035101d0003500c2d03080032002c3d50083c1c11a009120100400020b101d2400e80020041c00041075158a800d07c50030181c240e06516000501c2c00010806103034460683c150f0109a0b20700c04901044a4074041003143c1d0390610000e012002010100703000303038000e146290b80c04046a407910110318143d030009440340c1080c42454080e82d90841480c0000c0104c4c807001c100c015070540d0700310b28400503031411562031095510030703410750080c0c0d07a80285544949034024003518916501050751001c0340703001c406c6004001d010000701b20412060394402c001c4440713460500c07504488900d61801c0313885c00050700104a1180103103400c45c001400400c0042e00200d1104440010040c3d9005a40c0c1c824203a86000400715400340c1c030001040144845a23a49002c1c68001c2d00410684c0d0405000e5100d03c01d8542e019120328501000220b14034082420400c0b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 241593012 1250 241591762 241591817
    0x12030a1407030906051e0d060626040b06010c0516030c0515090108091e1f0912050307031508010b19050d020402070206090402130305010605030a150f0f0606 69
    0xc424640000740d180106504214016681042000101c16102400203800e40948070780100c0035031390760700869070340c84000c15040c070800740030840c11210f0300c404000240300c40c1078440003034208007035658480e5142220310700300429803414490094440c10105004000585110b00c1c1004911116800d50800030246959079100501c034818070049068410091815140799100a0070f0480540d12451050b0f8104000d25401f003903007144a084148044800044000c40501905000c3c060b080c0401112400e0b130750f0f00307000907210b403a155502c400442e00c5103005540c44107840c42d00050300101c001d140790401c0038660000446a458107505d081070f25188150074600d841c0b04152002e030601d06004a103042102e00806841194041038040640d190b1400711629018020811952003640c2081c4100c3c060b00c07030100303440c60740c44d01d100412a400e001483c1074a1a070000c04184030030300d05120341009028550144424645c445829002c14555400b0326070140205885207035108240c404442e5480394080d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 241594262 1250 241593012 241593047
    0x16080c0706121104060302090a08011503060b0f0f2707051207090e0a0207031b06020c070803030103020d0f020d02210f0a0f111908060a050c031005011d12030a 70
    0x5034640308042c00d40f404c503012035019040250b01c40c20000002031180100d80c0c440380301542032010504c0d5a507440604039003a2807150030100070341d030b8006046c401742058094441e50880d0b10220302440303500d4003603141c04540902d40c21500040c20700c2090b403031100506542c20310120f100860f0000310124103c04071136200c0591300d4940007036031a002d4a02181d010140001c40c40700e0b070000329101894880c1040c0e1244107106401d608a0f06490321b0514020f60240c400c0c000fa0340252000803c0b110801b2084074100c0390010b044802c035190071380740d003820394501c034008a0703101c03008000c0940142c40c0c64803103500c0542640121000841c1d40c8012a0524142c20580a031a421407609180061701030840315401c541c21481c0c925103124100f001c508000000304d0700c42408002d102001400c180c0000b03000340f0450340c00e8801d10454981c020f03185250701068508590560700d086082c401940f0505809801200002e09618034158040200d003105204458020f2260400104e1111b6a42c004480341c1940307140c0ac = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 241595512 1250 241594262 241594271
    0x30b01030504110111030408070b25050a080f070212060a06062f07180603060b0a0302240d0f0603061d0a060c1404080d0f05160816080c070612 63
    0x1941c0b00007844003d502c0362418030a074110706800c90786080098501070a420310071624401e403504a01d00c001c2d004111610284005441803000c0c8050301e450104a8030391141c014142000c255840507000d802508400105003418003010f800759403008508024000c2417400380c0100d0030107020719015105540c02450600601c0c05070030000c4a00b9503581d2065441031070600089000f0300d80e8107410580180c0c410b400840144800e0030840940c2d9004100712441a03404101f41440750042c0b02c54000d0a12001e13500c40241c0400d40340c0100e91100d142a08520350000320702d058201d203610801c40381100f0001607003a540700f50074020440c50340b003075500f0140c038900e0303480340580700790011641c41d0a0024000e050b5038441080d0385140d40540e502030341c150960704809860325241ca54881c0e44540d100500e40000f1002c4100c280c019008404441914240303003075040556502e0348031412642c1c000345203030f54000c2e0314520b940040b99000026001210790103002d80703046403400100a144038080d0401541444c5071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 241596762 1250 241595512 241595521
    0xb0a020a111b060c07050a030c0801050703140a0b13050a02090a09060b031311030604030302180d020102031b0a060906060e0901050f0609060d062408121e13080607030b010305 77
    0x9a440e80c038990b10003190703690b40c1c1e40250813005050030155170140d908800e4a4070084108004280b5030000e0740e4915001b049160341e502d800324151888401c01c9010203031400081038080082d034101c42280032000c0c1c010074400685006c0700048640480e98408201d0340400c00030356a01e410381000005001c4141e0902046007855803041291202030402001e0700b20740c40030942004880c200c5000d03521801001d4031401c0ca4903040107406507100e04400696200c201020011914251410640300b98041c0e00550800d24516075040b80d05d4a40e071000c003c0da00ca44000e05000a415008800c2214814440418000e192907810541d0000150237032080c0e0b41020104020400c601d001198440703400c42d9204043d4580384041200d8070985580607000c1c90910030313004407004081c001d540e80c1800752030000e0501ca6681140395100c84181e601100001c80030407001074850102d000701c0400c1c110707140e0701a00e0040080144120024144d200c2070360764200c0e008010442c0e41501c22805666828242070003140741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 241598012 1250 241596762 241596793
    0x10506030a0509160e100602060f0f0a020f0f120903030415110c0a0c080d050720120a0b0103061a101103090d0309080712030f05070f0b0a020a11 64
    0x40104101c44a56035030002984480041100d106003990340701c086040320383ca8403042990418110340440310b071100400c0000c6c07040e20019410744070341c00340d0b20340a1041d29508090440000b02500000229409001d41241541c02c8001010740c01d041d0741381503581d4000d0050100c02c1150051802600c0d41041c41000301240c0454031105159058282c000f4140c580460ba04189001c1d18203a00c0c11031290550140400c4104030245c0141c9031580219142080314140480399032140b200021320741080859481071100110601d220a030800420103421820025080ca143c07154000050301d015100c0401001409240c2c4140301501e12001c817a0100b6001c0b10010440c0030782500c00503c2003042c001c040192280c000e205880b0f0641d0000c0c00c4200000090900501701949405030040701c0c01030070310001c2d070f4103480d0000b01d0075268181c4464416003040c0350103035125046a01d060781d035500b02004000028040b02c90713240c411a119840181c40c0d040c10b407001411080c2d2180c0c100c1d256440300360200e20041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 241599262 1250 241598012 241598017
    0xa0e0604060f050102060c0901230d0b030615011b021005070b010f12020f030109060609090204050609220f050102040f1e06080a09030e06030a0c120612030e010309140d0f0305010506 80
    0xc084419a5541e060030200482c3c510325200543c4501c2e0281212b0a150844000004c10358245682c4003030080c50010410941c50349400c0d0340f0325043c4080c00c88500d0309540200d4111a0004681d0344e070144611042d004950381170962541d60000840002e13130241048150348500d405410b09125251210341004c094000e07429581c02c010f40310740490b07060703900f00da80c094020031003403948200b0601001e580c5406d01000340c000e000c4100c0c812410000040c0c1c1c58181140c045200d12902c1c1d21110303015000359080d43c00900501e00c1510103402c07240910700031610900040000748503082e50815880c3ca450280703940301c1107810703c5424075240282e0800c800c95011401036041408100001044070307191406541c044c1d1001e0b20503400c018007104000740c03400c1e180d008000306146600d4840d10303000c0480c643d0381145e4031806424142c4214500c04404071b84900100383c0340050605001401c1903154030b80b4440392515100d602d0380ca40c040b00c40020000da00103880c60045140d82410301079541010001000c50 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 241600512 1250 241599262 241599271
    0x150f03050405030d06140112020f040b07150207031812170c070909060911011e1d030f07031106040b040e0901090212070608010f0311100e0a0e0604060f05010206 71
    0x15454101041c280a401d00807a08809404201002069550003030b980400240c080c0c0300c1c1c040760361900d025048d522070b402250603240710000b56520705410039640e00c84581085c0c800756070420005014036116002c40c4002e20045020b80c80d41c1c0d0300b10004902e01c00301e1409a1700305040504900d90030b0700008460900030390004d0041c403240f0b9120168241c113a4a07240140d406405020700b440b84030b405012280e880750740090f00410422122201d070900540300d0754074800b070b8480782c02c0c48050800a014410000640400e03c07040c0c3c00704030710b08031400003483d00c02510604041e0781c02c0303031000b0030401c40c41d41c5100e012904161640350409107080d04501d02405076215030540010100000b60b02044294026070406c1d83c010010456132910402d505c3d551040f80c000e16012410104c00440c02e040307500c124008481d8054088034510030020140312405c9012120b081c00c0c01038420055032a50b5450341b000d0060300d01518600c20398500902088207a0712907900880800341c503802c06005590f40400c105520 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 241601762 1250 241600512 241600517
    0x70914040c030e03040603020d0f150b03060102120d0f0608010b06040603090c03020307060f081b0901120f18030318050606011b170301180b0604090b0415030b10150f 73
    0x91490707031030080d40074240340c20042400e80000580820455016805410381c0310054504100d85042002840c0407103107090115518203500e000c080082d003502e84020b507401981031050f103d9200005d6180485900403c5a142040b5103036806c08401e00031300d20aea0002014410028000205146e02051f01841207020b8a0209902e0b554802c00380303d108a0382000855021741110302050b50788000400a14860706280001552a400b0070004401d4921030041d1321006200381d480d15514000555001c1000032021502d26281d01d190b00b0724040500c02c142c11010240c0300c440c15902a881c0041c12607208444002c00e08082d03003521404a40300040310b036844002802c00d00006200d44c00000b040c60031016000b00b404144c28100800c41400301c01440c100c4006850b11115211030000350300a41c0c06224a0980000041c801041003a0541e00410445600900300180400c8500c0e6101c03500400f50304251600d417220b00900c194030307691a80c041c2c0141000c0c100c10743e070f4010400009052130142c803c81c108 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 241603012 1250 241601762 241601771
    0xb130c200c0d030203090307120c0918020316060f051921020301120b071d0603060d0f080a090e0f150a051c0b01061403062b0809030607091404 63
    0xd0158204110380c0314200050038824006801d02e0029903a0303011007046030081c0522440080d5105000f1030b44890a58802e0f080aa414101251000100f214001c28248645403005a00140e1400d003e00304040d0200484441020304003580a450501d110848804014040181521000c140070b1991360b44441460560442c49100c100d05986070b28414982c400c0c1e6100000000e0480c444940305104140b0035001d80d0340302d40c0e40b1202612442c20700300e1030203e1901c2e28003888a261500000460f40980f00500348081c0100315110041c03541c0c00450225034041d000500e001c44035422444900050140303054011403480c04103108241c6640280002a19911200034003c481c1e484068120182c8009890024098444110502d10310421030040d40c580315004c001045031803107842d8440904a038500c0d10380c41c0d9240c16040c8034180c1c0040c0300000c14481682c40019541c4045d4880003049402960603c1d00c1c0c001800425003028070103403440c0140100d04400b0845885004903504100c0c004070390008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 241604262 1250 241603012 241603067
    0x20304020609060408010603020109060302190c050304082d0703020310050c09150d0506060a200106030c080715020c0d030c05010b0301050c0d060e0615030702030f07060b130c 77
    0x180c1c0e9005840c0190b501050205010030039080550092040724002d0fa00d1100c0141d446806500302c0c829910b10241c8040741e66240d005c11402071350842800c038852400c0320300d4641c0e0340383c0d19403d00b480d501c8841905d141100c0c4640c20403040c22808042e41e0b05100103010030628546c000703039076442d80340d80420001d41c5403030000d01c50390020810340e0407051b0080c1120000803490354200d000c940c0020030b0040c08070b01d005c010a00c0380c00c0540680c0e100c02416140d4410030900107141f0001e00e1341d00030442c940756494400200000f41c105808000030003c03000105581403e089421114481c1080c4040455001085080d101d94035010b50303821180c0c242c10b10710b25103041406c100d4003609c14500260b82642c20074090003c9411400f005001c11004540200200c944412100700000029905240c0c0114692645000b091038080115003001ea14011a8a0690314054030381507600b02210a0300c52942d19413080b00d050620700020461802294810000d008a0746030281c50501c1c40c000701c0001c10f00401d00358 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 241605512 1250 241604262 241604269
    0x50f030c0c371211090a0e30180909120f0d021b0606010318020a091515080a0507051303061d03030f040c1502060c030a090210120e0a02010c0602030402 67
    0x40d809000020f00c544020503c03800c016400d0081001864000c0c0d442c40d000400d019418411141e9444088000d00103900c80307100c80c500c10a9580640d03d280072030806001d0f00300e40602c0018405501c82000900f80c0d0104101003280f1150000c0004050750401203c80f80d8040001049425107130104d07a8482d110f0b5160b601202c000c1c00780c03078050343d02000414600004c41c0b4001411502c00c400991b0103004823a0708400c22143c2c4c6111800082d0025644941807200042c1908010b04155007103c002e5119541c0720000500f000c49038492401140000050004810703090083c00e230b00c00d640c1d0034221301d00900f410a07100403c070b00b0f1002800c900d940e00c00ca0111006058846805c40010b0310031241ca030b04100802c0c1c1d010740810b40d0708441d40f0400e00d01c0001c08990584040341c2c10000c0b600500703510340d94108545100d610090001000d1a0f45100c003000590360400f501c103407140e0715596a14101a9110200120340204441803429440810010010303a4401c08002c180c644c0213102686a46551021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 241606762 1250 241605512 241605619
    0x3180501020d06080d0215010311010e061209120702031b0a080d03050a0b03060127110a020a05072301120e0f100501140108180a050f030c0c 62
    0x20019400020b5040300c14405030444810341d0360f450259003020800c0d500580c0d580c1c1128458400f080d4013000100301044042000580995041c10080d8910102e10001b8407a0340c04042a21000740c0c13180c050100003c03003000781600d1a40071020003440c040140d0000703544c4030981403c1d03005aa4810221041d0f170f85400c1d01510090801c4000c40d46000800040a806820102c41d50703241c0c01d2601801002c0d9280000c0d034a41201d6085900a01840503441026100803038520040c0701c0075210419074521007043c6004121040c0c0c543e01070301e06002c481c544503081035003039400f40441c103801541002c00c050026485d0f009601003402c2c5640f04001e410881000382281c1d000c0118180118040310000c0e44020440d1040005040b00030002c580e00e035440c40240c044031010450000b040840060074202002c450000b00a00c0001210248035a0b540d80c1460102c5c4040401c03115000030070261950030381002049443c09048a04580c4103035401051109501001805840021041d903807000403c2840320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 241608012 1250 241606762 241606811
    0x15090c03060d230606030601290c03070c050103051003150c0908070803071a01180e03120109020418110a0e0a1503140610020705060c030f03010305070f060c050c0103 73
    0x1c03921403401c1c9460740d40ca5812401980d50b0518000c07030380045c102d4500854a28103a0314954080014504403442d05036025100b0b0f40d100c0c040103010401002c0b1154100050071182d4490034010107854200400181a903030080c00054110416600a1000401060161200c2d03040e10100080000119004464103851036028002c1e6002f5042d006c43c41010104c0100780e00b501821a141c016050900c203490949024840c40d0900b803254804120060120f42051500c04a440e084900f00803040c0c64901c046e0000782d11103d20298006401c029101647d04812542d071008201000f18044003c140c41561007884180000c01c01005d411910300da490325104005896502c0e003404c1c0c1d503c00e03004050002c102d210703680b9040364401d4002900c42e141c1444800008007190b4003800c5114030708030a20409800901443d55240800e000460003020644043c6000310300440043c50307410b10701404e0a40b030b0480342c0c1180c0c04000300d401449000c5980040c0d48034464a0a00c3e000640740c03d815182c901500d850744 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 241609262 1250 241608012 241608023
    0xa110a0f08010617030309063c090f010212010504020706110f0901021501080312090c2205010801020f04140112050403080403080106021c051b01060608010e15090c03060d 75
    0xe4000c0349240c0158004000d603541c0f81410b005050b0800310483c0da80c0000c407a00b0390940c0c13211000035002c41100f1014020701280c540310444010050b12028411065401c0d079035a0203103900d01f0000001030030001030981801008c0214685003000550381071664050045c14001c60700040d4103003c01a50781e10003a409116050f2558507050404020400c41c1d2003810b903903005125007561000d400c3d0010507860b04840340c200055140c101501d51144080200410111703185c024188000704680781c1c402074000c046c000714160340c401c56912240008a8406801210843c0e1040c080071403c4894482150107035090b00201c0e03c4010044d00040f0b40c10001d8580caa030140382404103000805030019152402030f0700c04e8454101680e281d60080b07075100740c100030031090b109160340003100c0f8038054401410004000814024805041a107460070348800b541f1040000d6801030040280c00c000c003055941019014200c0303900710021074000f980401c006005110410070000100d030050361500c1d289807286600c43c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 241610512 1250 241609262 241609289
    0x40915050303031f050a0f03110102010b0a06050a110309060403020105070c03051e010b010c0213090f0b040503031e0105030718095d14070605060a080109050a110a 72
    0x1039103021003452404d1011200440001d402281c40d150002d044001c0d2a0251000d003c045e185403641800004420072030b81c195583e402c404050b640b107503484900a09101c3c1c4034265640425140100704590101804005400c2440032800c183d561000310781c201d98091070a1615810581400d020f0410141e05c0105030b4032034000c0b843e92b1030700d00c061982201031400d4001c00000f62100010f403511180320900942c449442e2050b9aa050b205601101c41d2501543c8001e08803401692810011801500c050300e25900120810010010700c88994500c105004070b481c03c154500300210350740d540b03e40a80320303d01c4031032060a0618001580050003441d0088a500b13441c403240380600000040441c0d150040d0303100014450000c020049a11120094000c00e0302103541c1815860240b480f440d0000740200f000c00f40001c1c2d02c19200101801f0201c2c041c500003c0d850411350100580460998403803a1f040c0d0418034441d0108034042014059580c0043c070316200307034100f00009844605036411810101c2c658 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 241611762 1250 241610512 241610521
    0x60306031109060906062101032d121d031c0f020a0f0209070203070f030306090b09091e16080309040c0504050a0b09040f140f0609010b04091505030303 67
    0x1500a00116401400341c14078282030142800b1080000700e4185800c0343c03608001c0361781801c1000c01010b14a4540e100f40f0550081070341010315110f420b0b40150340030f1002c0170440f00d0030404211015141d03206010760f1025100c85a032454020f400044115091000658009401810711004c511090314000d0035694021024101c50000990810b2007000148014464500403400010240002500040391907012150341e4200442c1010040c820411070005014540020310503c01602c042803280d140031526606002040f0115510310380346a11410a42040c04010200826011a8103c030081600841140326560324a00040020504950b00807900300042c1800003102510a0000c202c809014110b09000c04484a0140d401003540c05401801c1c00c0121112040080c842c010006d44041210703902041d5540c212052402d4006a0700c00850800c01454102d41e40d980d031058044078200040d504049101c6001d00480c081d04001903681d000d0710010110317980040000300002411039907640350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 241613012 1250 241611762 241611767
    0x80d030915180b010603050601020304030204110f031003050d051c0504020a170a1502250609060501090903020f120d0e070e0a06170d0c0f080c07091a010e0d0b0403051306 75
    0x100c2d1441655a20180000460558030078000d150082c00142e0003541070605540800c030042140135985841600104034040607100103070099803140c400c801d1000c8500c0d1450500a0030104c2a4400e80b003080000c02600000e035401c4829588554541000001c3c01c1c2c2c1d461010034404200ca4025a08007661014040900d0038009000c1d4045881409100f101d0b4000500601c203a004072826403030840e0802c0f98242d202500c401480304d406016000201d500d10366901c520007120030a0300140060750b00c50b11420709054040081e079494414003001800c4d5500d0306031681003140100c3da925901c083d183c5115006450302000f0401c05011140740c1561a4207042c007131f00c0014101403241404180c610030480629940c04104500c550381e05440f00c922468440e0313204ca10307a8080750011608440140548604403c0400c100005000d1828001070032944a070141694030003078000942c104544600075610f5038a1300b201b04101c2c41e503c40711700000d6444900e420341381809840d441c880c1c0003111001c001503495 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 241614262 1250 241613012 241613051
    0x30c0c07090209030f010e0709021c0509100b010e1e010314251115060d06020a080702011a0f040b04110703180506251104020a02031c06080d030915 65
    0x190101c045800c00b81516560701e0a80324071075030701c108503003241e0809c02480400707030001c040581c1012007040704045d8040400b0102d81c400d68070400941d200100707006400d1000d1103150803180003420310b100c000c0d66407000207412614400c0800d500104a040612059000e500441009113503208842078518116102946003054a0002c021400460011082c07050003090b5080d0096160800f4000805c0e42c41043c0003002c0014014980000d400501200801c40c03d10260100030a00c4e03039500207a0612950082c00e407810320860942ca07002c107014401060399080c2d16419010340a45010400d82110ba0001d0001c11407800031040050000504070100759000580341d80d14403601044080a945980c00c1c0002802060b0840e1889000004447d2a03164036459601d002403190741b16000302c00750500811f0aa030805401c140141c0e0010500405000540040d0392408031191000c00050f850b0074803441c1e89040c0402041c0506d03135280406804d00030300803101c0031650900d1405110706010f02c2503000300c0f034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 241615512 1250 241614262 241614277
    0x60905061011030f0f1801030915050402010e091f0509070c2009010806040b010902030c0301030308040f170c0601210b07090914040302010b03010e06070e13240f0506030c030c0c070902 81
    0x18020342030004087d6009105030810280c20480040240b02e2a118080c01848054401ea0500001a03c88403060f60389500300c920401e60024bc066500d8080e051405003c0f211b504514810f00d681340c00c022003190302032a200034654000d01d50101e03580203070340134104800704030010365000030384880081949000060302c6405284612800300c41d0341e0362194007004070300083c4e502c0710b0494010001007000c20300c0303074002940280c012900301c114001d0940d100042c14a074524584c1c07003c2c4000c204408424001e1240b01c4c01080c1229149001204902282d801101c02d01c400901000301507001ca034016100700d207944060401c0720b03420030482020001c004c803030f44801c680840041d801c29014403103605040c003038040081c4a14004181c1a140c00c0702c140d48600c1032900032600201300f01e8062102800300d0250442c0e141143d00003410701c1540329000b03824105030380c00a00c602200341030300b04415154442241c1d8030a81441c10135071aa282e042c141c4045101c4d15080d07460a110b07034035012800d441c00d5401070908 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 241616762 1250 241615512 241615537
    0x30702030f0a030e0d0204390c0b07050c030705012f13030b0a0209130603030f091802130b0307020c0a05040e0703110303070506150103060905061011030f0f 69
    0xc0e500e4035003040d075140c40b801e400400068003003c0d030311242c0c14040030741007100c1d100500c0030624000212441100c0348910701d60355900780741d5810906944100a551400401d00c034900080074801c661924a400c103009428002000070010b50401201402d00599200340c0e07000d030090152381c03002030040f003580048400e11035501030789203800801f003035001040721040a0744505030500c0300e145444035140c5110084c103a00d40c0c1a020007070b00741580d0b95102e0290b0700c4604101d0005159040d0308004000300c04081c444002d00a008200340304842002c42c0b848100103008001503980c540a0a450214540a500c41c1a4500001c424000e0701600400c4400115206540654507950b4503420803064506180254410381c100300e03414030204416800c02c5c1d17282400034040b2031401c6955550381d894140d044a100d03004034188885e41c1e010350f80c5070040000814910005100a0070b150300010541804200e00c0e1060004080310070030320107000c0c41641c6400304040d12060b10b548030030361104200c1e03020301011080e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 241618012 1250 241616762 241616773
    0x602060105011d01080c220311040b0a150203090d140d031505010e0406080312090d0c031e020a05010f0209011b080304150b0402040303120b1203030703020f1b03070203 74
    0x20070b03500c640c0440782c1400c42d03010100e1110400c2001900d00314005454610401c00c200002a10100030540c80042e040ca05001c00796002d140d410418403950001d036076284164281701428216580320b010010607a02046100d18048400c0c8000307038034511804000540056401c480d41044c4101c1c440903205400140041e580c4021501404400304e41c10b80300c03461581c0b00c0546041c00603501c80d40c13051000c008090710003e54140c842030f54601e980c10a520512090701d0108c100420315074240010003460f01e050904a0051225a40181c10174032522261203900c5190b041c0c03005a103100304140800650404020040301c0c2c0c03c0e801c810060740c4926480d0b404034205038074801701400e90503480a41c554001c03e2041c03c684a96842581c084011441002d0250b00d6448418465807144024002180f20f51207158010b00c0562500701905d0110711240d20804152550b0441c6c05408000c40758400031034540103903100000c0c82005428050220560842130780a500e00c0000b4100100030304959000714100c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 241619262 1250 241618012 241618019
    0x402040507080412051305040f090201021203101814010303030b190807050603091005130209061909111e0403170a05090f0a0305010504030903020f0a120b1506070c06020601 76
    0x584181e003d80b8028001050302c43c1003540e0500c14005000d2281c5020840c0c034983d0740e038100180c01c4d00e02d000c500f10410780d55444a4021586c0400540b1604120842e83e40d0a40c585140e4020209070b4030300c2142d02d003032070300c901c0e03800740e2025035000507da00c00d0140403022950716410001c00909906144500610141c03846000e22002051000100d0b03d41c1710007810020300f40f40a114071a00b020b00740d00001c0c81146403c1240f6401c42c0a1207114402840c080d41d84003819004010039100064082c40c0914040400204280c40e1403e0300c80507105d000402007226142d02c2444a000d10403140030212400d2820404046200707418024001c682c015241e0b800e050440d00320550040c8202c1011801040341000180c149040c142d4081e4403241c0d00800703c140140c0c2c2ca484103402d4502c12181240001c210f14421300c02c6241406440c420880241d980d40402400c180b5051107254807448054211072300b400c0082c2044c500d903c400d8030300340d0001d800329480e040d0614080590b0304260142c403015009100010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 241620512 1250 241619262 241619267
    0x21c050412030b2b0f030807030b010f08040209040201110a06091709030d1b0b01122001020304030201080a0b03030f1305090408030c130509091005010801060e0414240402040507 78
    0x2054505402007202c102440d000c50101360800d81c00603001c410445881104012481200d122a0090302030303200e1140c2482d120b9002800c6400c0c0d28030450600202d0f911002140e54001c603800d274000da05840d60b044940300d600041ea004203030070b68659941d1040c50345030403c2203c9508100c6c80a807003580151300031009507000c065039000300c40502d03415504c10840301401a02c10761485000381d41200034500e0007200c907160091021000d0700401c1b0900320300380c514020040d10a07804001081400401c6008a4804000035101d110740c0c84064100300c840c00101d00c03847c000707500150850100804a95458003c01c2d4200c000e500041440c50303110000c0100002c0c203003003207510280319035840b0188916568804440c03040c142c00c4008000c0d0300948501e000700707140c1c907180d60751801045024000c040c1050740c01d42c004d06a034016004040700c0e034100b5a0820000c1554034203103030001d078809040000540b402001c0c0c1d20b0040442041d442c506e01c0490007280c13400d8400c080600560090b035082c0815a0303418000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 241621762 1250 241620512 241620521
    0xe06040302090f131209051002070303021b040204080105012d0503061b07140303011a0c0a030c1b03080306040e0c0108150a0509040501020c06090a110d020103021c05041203 76
    0x80c0d0071100030800103d5020b610350319954004110620349411442d07075141c2d0906002d5201403100030940700c010510140c9040124104042002d10040ae0410f06603a8001d4a0381c0300403d130304101c0c9c4800b285808555445070141ea0103400740760000c02007580d50302d04440070344403403695001003c684507540d840c2428003402100191040540201816190105401c1c04000c41415041ca0724405010344d000169484488a85138403244009680703d506100d141c42210f460703095091940c540c00c0051942030203002c0303443d40e01d0a4142c00c00304a03542007414204a04101c4592103d003211150f407010081100e10003366001c0c26003070b2420000501509811541c0e00a01c0c0c00050100304040000b4011881c2d15038040000c02010b0701d2050910b60f80c00102c1d1056600780c0d0200ca0f00d94003c83c0c0350784241130800649611200c1030000300540340194584004000c3c60b990114002c0040070800415039010350103c0d1500c040e00c0b0040f03c400c14003c4071442c0280707801d513402c0f40e4034241c2004000c9075500c030303005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 241623012 1250 241621762 241621769
    0x1e010f0504060c120c020d0c0e092103070504152606031b0310020708180a031505070e0a06020102090f091e0604090204091202070e0c040603020a020a050d0e010e0604 73
    0xb1010f01c0c02c070380c58494440c0c1a0010210500b044003520286005032500200f605510344203030700c451310050a1111420109500400e0300c803151340015032054607001609034881041c100f080115a883c0c0724168125a2031085070820000780c0365400784042c06c940d105000000614400300150381082400010418000382a25070a9240d806903610341052148840c01d00034a0800030102d03003204880c0c07480c40042e40c001040c16140000049075100010384604031817201d295084950003521b6040d55580e0f0302942030900840c48066480c00051000d038001c50402c40490801043c1c81c580559880c0d0080c080d5021000071806100100030040742400c0146005000b0070b200c51204d0710141d0f12912040360a407008046c2c80e4000d84403050741016880314800d036040301e405408014854014054080d28000071030b40041d0541115608001c00710007410b081c0d0701550740f58030b00940d40b03041540303003249807440d81c1c10050041e02918040d0405035801544021103140d0a8a03590b000d00081c00803c10a03008620 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 241624262 1250 241623012 241623017
    0x70f020d2f070602010c11070806071101020c01111902010c05090d030507020d060b090108030c06070f02010b030d020607090b0304080d09080403080d0209040b04050402030a020405060d021e010f050406 88
    0x8040d07020070201102240e0340484001c0d0140004480611503618000441e440803000d81d66814410980c1a8040886010b10395090010002240781c00013050b40c2c1c4000804001c00c101004280a46214003901101d400c445030000920402e6138070f900264044d408404d41011110382c480e07072024014018052082c20034201d032112400d140c0c01c00207000580c5083c10080b000c000c01007010030010f030343d07002004400900690307000895171006001d020313a5410607044241e1a90091168807142c0c58005203040d441041443c00020780424804260b01510348070304096418000c801419030f0103940091032a1040c541c035a507401384140d0329004d4501c030344000d89010740042010001d9000781c9515030090100c1c9031017110814682a503949880b40c440d04410032809109400240729080791270a0301415507504e108881c2003159051a50010f03655040c0007400a00442d1580f000400c0c640c0d40440c1241000d402500c0203a00c4c0c200401c3c0000c01200114402e40403032110145615450310403425182a0340b540d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 241625512 1250 241624262 241624277
    0x804090209181521100b0f032a130218240f0a021203070c0201090e060108060d060e0d080603120408060a0f0b0a0e07021e07062d08070f020d 62
    0x83c1888a02030011509032180c955a0402e030712400e070f0401410078625001480020400d0303902c0e04121071840b07215451403103903000340c6030110142d40039031070300c1c0c4024050388013281803982c01c002041c4e00010705000c40d030300b162001c60384d450503440c0c0701200314995100300c81d4035102e0620081e0802e002c8403820410162443c05110000d12854590024400240c588c0121241d015101d12420f5140e441101e04034001402d0800444c1196000302040b000360031070503080d10481c5025400240308120040070184a44060030500b010721403140d00c00c001100130f68003a2903102e100404043c000c80d0003600c00e07034068401e20500168020403d002e89058580d0720340540b09540b1500346090141c92840e07a52801240d880003002d1290303032682256001803d40460300c40310782c900f40750081c0c2400f030054915000406881c052000c882c00c041051010786046041c0503900389012a040c0c2d803402ca95500b206070360340d420208000590382005406104803800e41d41c084088080c074008985810f0000c0140f00411240c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 241626762 1250 241625512 241625551
    0x1014040c0f150e0d0b01060f2a080a090e070309050c030a02010c0807141903031b3005130209160905041e1a010306051507021507080409020918 63
    0x35842c40f0211040145044403c1019441c0c03840300503400c1c2d00090108400c1d625091986401c04e000c0b00c54446003003802890340e894130850414854011800800b0244c1c0081c40c960058011403d88014104c0b6000701d810915040c0030240090036003e2041d142441585e0f4501000c0c03400080c0c0d00007195040c0e4070f40e03105c030f6a50740e12400d59030841042210241e51401030103582d88401c1040c01d0380d403860b20014081d10041804c016040b111240000029060100b040d004110f410054042080030602c690004030f0721841e982c4201c01107a00e03900382c2d07680d00340070600040b0000751645506c8140211003003249030311010101490341c1c00c0601100089003940004202610381a4061014030002541964002c0d2900a117a030840390b075400304801100f550022210725582c507105100141c40255080400b4001250726040340d4020140020301c9468840b500c800b008040c5810b40d0325443c6e000c000c082c1c40e1a280d20884010350080c1407070318041d0007035500c503107110700316642464064608625510600743c1c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 241628012 1250 241626762 241626767
    0x1090b031303110f0a0302030a08070c020a0302130b04110702100c150c03060e090a03030510050603040813030c0b190903020f040906020f0c060423031b1014040c0f15 73
    0xd034000e030a0f029070700c400d080311307001448003880161180c0e014554507501c40502610b4000060036200c1001550312282d001a100c460642c401c0d01d8045841c0c41050500140680c050048880425049403d024003102c00400c250050100c1c0c610071a107407001100115411225800502e9000c1c08084004681c00d0480c1e82d80e610440c45503407207103000b160060711382c0e504a4008100f91950507240c1e0000b000c0005240c7d0620496070024200ca82d05041c1030b181c10001343c0d0600019201519504000030034074000100c000d074cd0b9009592000110b08600d07681c1111030002d410100145c80c92003015000c0403100752140d80c151064a500901c1e50300c0c061074400c2440300420b9010400c17204654208144907249007140301400c100c20200d0000c1580380740030303d0800c400d641c10441c0850780c040d0a50501e0202c10010042d00c5942404810000c0800d08003081d1078a07000200c840010064600080110000c1244241c50301c03c60069540d03a405960721010140d64494034403c000106030f002c031031900d8052 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 241629262 1250 241628012 241628027
    0xe0f150603070c26130f15030b0a0f0602030d051f09050a15080102070501061a030f09030f1b0c0a03120302131a09091303080103080304060e010609050601090b031303 73
    0x340075240104c401e440f61010120b00a4900c0802038a00e500861061071507032032086004040c0403e00d101054841c42c1015483c2c014182d02c5100c01410b407694400300742034450416400040c02f6400403e5251a695140070751a9031002c01c080807901e0801d00054843c100c140f40c1c0cbc01141c0c0200c2000c00d04a4541004500180000b400d280307039554031031143c4401c002d401143d107000b6203081c1c4001a9580f01c641341090031504aa480814111046001c000ca000d01820940c1d60040c0504c1075454242e5807054061b00390710419403c0001460045450800c9481602c0c04d40b517513905460441d0107018009081080a80661200070f0054248000300170740e2a1194001d0050781c40071685a084558840c3c2103844411650300402110340703000700d400442c6180600515400a8201800c100604059180209208414080a8109000000840c04000481d80200d11500411000300206602c844080024000983e0414006524450003040c8038854804a0f80503e4511300c4a4401036980d40c2c0a98000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 241630512 1250 241629262 241629287
    0xd080907091d100204080f121206061c060f060e1e031f0b09011a0307030b01110312160f050409110417010b19031a0405030904060e0f15060307 63
    0x110b01245000c040301204009034402040340c0303140943c4032424903036100d10300101320300d0441081c0d002c1142901e0780c40544046500e5074010030f24040782640d0b09804640e8030b00c00c0b5203641489246003002c020700040d4661040003911422010030600c107680313203000c84520060410586e403007e02c10140108007000000d8020b00d0300b00c0601541c80e904142d509200a1000b4425241142c5444500d40300840c07410312415409082000140d08030800c041c3d429260500004081c0024159035088000841e806910020b2800c841c4c0412656240440c05004c1410a404d441d58140903005402d4010207034026440341c40110000c1c0d60b000d007081c0c0b03000e01c1040900000c43c40d07e148042d0412010880450649800a04014600002ca80864030f417007402148011081c159961034284081400000d959004541114162085916050302c941c14050f065109083c1d0700c41d4810b01c3c1c01c0000800584288040d0b100d00c00c1070140b1407040c0e503480d030507010900ea0b004605911510810002d0521401020043e640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 241631762 1250 241630512 241630541
    0x30703050720160b0304031416020901090902040e012f040305150910090b0c1c021303113003071a010513090309050609041b0309050d08090709 63
    0xb4941c0d01ca041c0d0704010100742804000341c0282155000c024100120300004090010f40a891458903450007044d1024180307043d4940080000c00000c000c03401030410320202e80044c10300c049540d481000c180200b64510f4128015420700070480408e080c180b0540303148245154490412817101000080000703d03a00c41c2d10701200c0300703000c04008500c04100c0c0340c3c02c800f081c12014000d0b0520390001441c08540300ca40001c80c1d800c0060b80e2001900404045410441044405841d42200c0c0040100c0c881c1381c44800740341034070100d0710402017414a00740d40c0c05c990049400390b0300c401e441c20901c200910821140c070b0b0541e60b00c03181c1190901020152424085008096034180040c0e6503601c0303000e80485507041e0a411105006000c03a240503141103111001d200ea04115014107503401511100c00c6108261040e40c9c085803203000c54480741c010b011203407884a1580030540d40c0390750241c02000b09200a9405104156101d401103005400b202d0180c6034100003484500e142540c1030029055840385000c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 241633012 1250 241631762 241631777
    0x14040510110c0f221404050105071b02060403060507031e0c0318050a2301050a06060f0c050c040213090509060f0603071d0a02120708040b10060c0f060e070311030601120203030307030507 82
    0xd02d074003412070450241e031147c0c00104d514208260700070407103208032082c100c650946050f0107005a0f186c40840c0c003269800000030402d56aa0981a0018484241500980034101c0d040710b04000181d44081c01400e826182000800c102c00d4030852001504840100150f02110b5940b000c21044031074140c1e002c3d40c1e0710b07031050158551a440d0713017515000d5502c0b920407a00c4030010b000468105446441c04a01d501d014582c1054a80700c80d83e1b5003e00c0d4003910301441d4001080024080785540c031002a00440c0014413643c1040c0e010309648240842d4903100860510004c501d03185170209141040350002c000c24840c60040d445412840440940401039065007003002240712075840305e00500c110950f40780e10443d807815060200d003040c00200128807801d12150300340180f5801100c1c0b504199004140e50365507040b02e160200c01000041e190484610424074008200b025217605580300c00c006900380e0b152a680d468400d184007490140080d0701d81c00920020305814400d07800b4940c8498189010384 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 241634262 1250 241633012 241633031
    0x170702120d021209130b030c030d021006060302040f03290c180102010b0a03110a0807080610050303070f0807051203010b090102010e061614040510110c0f22 69
    0x40e1401081064511681c0140c1081451a901403081c0c0c001c02e40841000c83c50450140001444074848020f4280a16501c9042e048562020030090340304d100003404680c5200401d18000c0c0d582c0520a1650082c907050240110b8014401e0080c1d4003113800110078546a941960340303804011400524502c000b0208005204034009010342c400c3c061943e9010b030562303505040b000803001d089090144d90541e81010307140c3d40c49854041200341265000b40210680c04285c00000d00c03841c0c0b00d036001643c13070301c90048041424800401c5050143c02406c103440b00c0f040d6030300103050300d03406081006401201c4103134208021820510040a515105030162044800520b1110006400030b03045540400b002046c11401c95809104030f0505041c064010451450080d03001220340032801401e40402c01c15013505201a078140d8195006000000d02945c581616008002e010111980461943d8030404509220504000180c0d03401c480b4041d044540d411941071188040c1c400348180c0c141c02d43c0d82c1d02d560300d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 241635512 1250 241634262 241634269
    0x3050a051903020301082401060509133b0c092a0d0609020708070f02120d0c02041a03120a02031213060c0809030703180518040309060903050703170702 67
    0xc80e42001c090300c0040c1c481d414402c07024500003058504903058190120015a8002004101c0741100d44601d0f000e640c4415a0022580304000542e5000809003403003990b5000c90400b441c081c01144095912035680c42c4d1205288581c000341000d44002600002a8548203090a0f141c540d8440c0901a03c01754100b03c0914090302e01003d2146103c3c5c2c14400320b01842d0300d02c01d5009400080501c1482542003402c0d13a15441d0340b5218401d4002d1006408040001c21911800303000e0200b42c0d5950180e451002c910030380905601c0280c14102d100d140303050355029031031400201300010000058010104012403920ba050640d218900345021341c441480030003400690703845817a1203203101e0360070b0343c140c2d10540c81e041043c0c6507401200300c140301da10b8040217560100001a140c90070340502d40801001c0d0660840c0600880c143c00a5802411050060002c50300d485003141c0510311a6480081e140d654502c1101c812246010007010364100d0b490400105240302d998541d03648810341e04901d882c91a6000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 241636762 1250 241635512 241635547
    0x1803030405061605090109141801030506040201140403120e01050408010f0e013e16030201020306090f060a060507060204210c0f050d0b2707031b060c03050a05 70
    0x1110781d5480603040080b03a1900502180a44a5500b040c0c3e007881240400030f0300f010124080c4074004c0720300081d03028107a651034074041e1420361103000c0c0042c0f9584900b440740e155002250160701041c3d01c15100074070760200c40100d804484c2c0102e840c4a400362100300c12210718107581480b0f410807506001c003140c594420310882155621a030400034078040069180e84c01c2d1260800048000c1d002441146a101083c0034041421281850344c402c000300c022803501401d0107500d603c3c2c00c070320f002a0004c40070950154010341c022501100e0000d019620300c0a600c0040000b08c0700140c22510400c41003240c00e00a001030304c507081c410030300175003090b48030311540751048e101601c5401c01104440ea034030240034564440e08050038045004800603420306003c601d004600071002400c0d290076500190b01c10380585482c6113038942c1e0350801a081035035580391660b206140d010540e00314913174105500f0402e407100318480450303c80b40c40d08002c05d109a2429202070300719250300000e114082005100ea206030320741 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 241638012 1250 241636762 241636771
    0x3010e0705010e0d0804051014030106091712090d081b070609080f07210b0127021c09030c0803010603140604020702011e02070509011217130509180303 67
    0x240106440c007000103101d022083d400b18040c107482da20240104040c0002c90b000d4900559030030318034146400c002c849840c2c81c10400180d100000c00041015640102150115149054000e4901c03100042c0f141d200d45800c500e007580c07038100301300c05a0300e82004190510214083e010160900c07110800034454a41ea90301024280d402c044070500581d40c22107901005401c402e0005d2600c6035000c203285075100740c68064982031610714040c0604d00e020400d020703080943e22000c0c4001d0307941e59000b03900d01d05441c020360900300c1a0300c5643d50000b25262007601c8606040041c200c1084404040010082001580c2681002443e0180c1004100d01394000d40c024445594009540c1d9458542c8400400d0041d140512a80c0100b0901c030260307910901c60500107500e06008141850b6001d4268074241d0f20ba807100360001d5610000188441440c01c0502245000708411401d00000340380b6040d03c0e21440c0b416440300b5442c40804e01131410b0000c1840c1d44030201c002076008005104500505c0d40d00100c2c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 241639262 1250 241638012 241638041
    0xf060f0501113d0c030e070614090d02060c1209090a0c0c200301061211010504050d08090103021209010903140309070e091c110d081512010b0301 64
    0x2081005503809682c00c0072042000000d4200030102604140c0600c85603035003079030412002203265880303801c28007000e80450411a0100110020340d04060050a1090b140c0180d41c02400300c00282d4a02404196a04041c60b82c2d25600c0d00ca901030400c01041080c00d400da0704114241304e440c0e14010304020300f0520245100641e51650320010800c659120010100e921301401c00e10550b01554010500514440e170003901080516a0100080702c0c3e4864401c51680c190f081a00000303094070a446c8600805001303444d103c100109110066501b88141d1080179000f1401407508404a118480034140c1010140750152920716562408909001d050300ca52086940d1032070751808050b0404440c2d000e1145040100c0c1c21407401060454555030284210050038910000080b1001014014144002900482c00c113100000090042c1091846041501544500d211800301c040c080c070310881c81950b0504c90382c070f2102c0c1c413a424000d815030154510001c0e592656411840c5175030078042c0d10351003110803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 241640512 1250 241639262 241639289
    0x9090103081806071104020315041e1a01080414011104060e030c09040308071206050d050706110106180b01020a0f0b190e0d0c0804030b151002010b0a0e07030f06 71
    0x40c0b03070200340850140000e803046408000550014100c0c11503100d00c00e004070740040c2c0f66074841680b144000105950075901919190880c1400e0b40e62141501c1c003010030590800090410a0900c1150031032210000c0c01304044000050000d60741800c1003401d181450004135004180030321207440c6400c030b600041e0100782011000380e4542802c1201c0342d8901d000b11001320403030501d901d010380310040c040c000c40100419451107894902d05500400000d0030090200c14614456003031540c0c079018680a8003000648a40c0d1004a9107014000c910517150200080d583c03c0030001c249000900e1f07500c00c0d590640c01266505008100807403049070304103000b40c1140c0d078140340403e0303030a031814a80c41684860900d07040500c4e8891500143c004181c06550030554540481802c0ca620f03580140d910090021000e03c003004080c95520303100000050054641c0c1ca450408600143e080c0e42216880c1500145d410300304001e028031a600c11604400c990600107074105105004030103480303050f0040d404a0111 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 241641762 1250 241640512 241640527
    0x21801030b09190506030703020a0801050f0609010f0b130e07030608010c0906050d1a090a02040504200a030c051b0c091506030705091504080a03020601090c02030f0706020909010308 80
    0x60107200070185045990740c48528011242d5144401881c0380c031500d00d030783c400c00184c1984040009401442c0c0007446039499a40d0780301039502a1500319103010100404801180075400c0c107c0c0018180d40d156644d01d400e06003054070204c0c0305c0d0404008880c2d0844000c3d00002d80d100090304031030041c0c4490f070300071a8540c00c2000e59804d50b858411807400f04006100100030311903105050307850001100401040c0c1c40550601c80d1f401546642081c0c3d48201b2160502910b50095030003882158016101881240c01c0040448102e5148009500c8425020081c07a101d00f0320952001082d00c9080c1010781c14010001c1d48040c2001e0f243c1482d65007580f105200c4242c91a1803400345038800006580d649810081801080203800003030800e40070b0010200e00210207543c1d02c1c0d6131610720488506030b2602c5c1c0b9035407501980e44a2000100f0b0300507005802c00403c503c566402401000074035500150b01c0d2090440c9040c1065022840580c0e0b41507090000c2d1920344c0d211510103000f14090507601d6100c481 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 241643012 1250 241641762 241641767
    0x4061b0e0a0b130b0c010e011508060f04021809071e0e0a09020114071e0804090e0c0307050d020a0806070e0307060504060905101704051f06140607080d021801 70
    0x21507009000115018801d03d1000e004210052040c0c45800210f151140c90801c80d807400760400c0c9000350303095424000080155902001124100c1d03101c1c10403a095034683c00e40c01e2561040541c4c0194020422100b080d088890603040b40e9000002c0340b04807110075a81c4c203030001217034480d12103e60b0807103240b440400c00d04800c9007000703070030610001c401c00800009500203044805030001c03842800c030b40801d5810034800c10040c6040c000c330000c03852803100030161500380041d030f105000302d4124a20713000890680200001d0640301c1c00c140600286441401c00e02048201031030404100d901a141c680c010414060030320500e030203500707544c46040181303900f04101030804400c3d40004c02000000d00c002c210384c0707501810040840b031003030f960091b0f030f10120a81140c07541007810104044d81041002d1000308000000d8154139108803094a08400c0e10408500c1c06460040c810340d4080100341d13010318018078020300249401803191110300d2420380300042d180309036040203641c040c4000316006240441e58 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 241644262 1250 241643012 241643029
    0x7021903050c040c02010b0a0306051009020304030c021c0312050a060b0c15010e072307050a030207030201120614090702280209010605121618090504020f090402090f04061b0e 77
    0xb41380c00244156098000820780110700d601c00a8030454440f4080707100c500c1c0411000000d40440c02c1c041d50340c0e1a081c00d000c1c10300313403000f1000ca001d6012030300504800120880144103070b55066540c200110044202d100c040c140140070748102641d14500082c420362520002c00c00003001c24080c00c0720101e921141007100390140d00400741c000b8003d00300b102c402d92112107402c003100311407030991716841c00c0f1201c3c2d41c0a00030800010540d20420407071805040d00081c403c01100e01c00d80e584010340b401c080b202d10503181e180c03250341e007569912159407405e46010480c442d840f05651040740c0c20030540051821110500804451b01c6000303480b8100250b050410b90380c0c0c05000305092480c6007294000384584070344001013003440d645034180301030030100344210300042c01c10054009020200f911032010500809050b10102d00c106d9030400d036404641020207030700780b02d980c0050184210340ea0303a0b07078100d0040c40020300840703840d5542c0c01c0d00d9800da011080c4d20a40307050349a0b0746844887c2d1030024080200d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 241645512 1250 241644262 241644281
    0x50d140108070906051f030b061c050108010606021504020d1e03090506090901170718020406020705030109020d020907091a07020315040b061302040803030c0715110a0507021903050c04 81
    0x2182031070000d000030b40340d850890140c40a0441c403100b510661b03510403030080148030425648a40c2c0024a00310968040001080031410709400b000343ea40c1e82c1184d103089420b40c1c4641800358214012400c01040c203510310590243c0041c00441c2080305564402da6020424498468445400031201c1c2c141640b0414804c0600419600d80789082e0144e0b0028845840c1486034017018000410a0a170340781090000070020181e145001008812010a15010350000c0c02900014414284000750074034050040b0010140c02506885000700c4036024800800c10042041c2c00703004249100180c0d8040c3c8030100001170700111a0141c54030b20602c1018100801f000744690b0504982c002c0c00007050f654110540c00ca80202c3c1c0092a40d60324410200203030040741d0000c0001d003c00b10800c8502c203410001010103912610a0754018510150400e0469145041c282207080007441a100b440740208000c01c2e66a0001b0800741940440180000125038603800c219441e030496074100c1642e040602980892 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 241646762 1250 241645512 241645529
    0x307120207050a030212030d0e010501061d0607060b0607050708030a270e060d14060108071703030a021809040302071e050105030f060d12020a0c0b03090a0f03050d14010807 76
    0xd00d01070002d80c0f940e50500001c0d02c20405140b4000c4048402c00c00c0310030b07550840d00309000310311407141aa80200710034443d00707000c604284a921403a121b1000d10003850f41c0c0060942e41003205503241e22000300b0111404542290f810030a105c00315104200c0c0800400f1780c00025650760300c0c9048002c00c10402d0741d8004201807102c00418260a140d48500020384094080070a410b07950000092400f0161500c0500f061041001010002d240400c0304c5041c1c441010484030095921254454041c000f07030054011900184007042c40000302d500200084400c0241e00c3c0f24241540c0000f6020032000d4a007180940d205800c10080d6070851a0a2807104201102e0382403020301e400c0000c0c045100050148244600b12000520280da1740b40340c56901d2a003182006c80c018910903006940c1d04956001070b80c41501180c80000d51943c000110b030320601c44880500507440c0c1d142d480c02c014002c410412002d0040622108455001521504d21406024989003849514041d4503178145421038016a14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 241648012 1250 241646762 241646773
    0xf04080d140703140f13031403070201080f07020a060609020d0506030c030c0103020d0617030a031406100c0212010e07031133040f09050925050105210903071202 71
    0x41d014030303100c1911085501803d10041d01210400e1001c064032403112012201d001c0030446035a1076095501c0501900c2c0b0692000b02005100108181d4038003070213400a0008080b1b100040c0e4141081038065088421401103d10500345551080152402c0c0d4000e40142c5501080544403515035004072504081d060380030345084248034011989403284080792506150300004d0070020658960b10020080482216201084401e42c481d1500e03a40000849000682070001401c9601c90007041d01d406404000c290708960070b4500025074184c01910030a99100d502043c0d1160135910a028241c0034506603400b0b0400d43d421451f00f456801c021603800380c000e804031404904a10022101c00c3e081031102c41060a02c940751411605c29449540c0203406069840b000c00104401070742c100ae4098981c0c03409641440100c1103516040103041c00403552022000a4204082d5010b000104000c0b280401500301203108007000300507040c0117450440d9203900015840050000e40c4441500d483c100384003908 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 241649262 1250 241648012 241648037
    0x501051509011a0c070305060105010909060b2a0a050f15041101030b210106030c080606240409110a030e0d050306100c1e1506180507140f04080d 64
    0xc00504050040d5102940102c5000000300096015071390340032440c0d41166a41d03a16031401c1501d4250a00c240d40c0842d8480002044c1000030f8000d010a48005030140e50429a844c9446210b0070554040c280c405004003040c00c1641809101094040380240c0c0249018400d08000d50f14010456a42c940c03840300c40030a10001802c510068610240c0902e000300e501001c0f0307000281c070b60031401110000c0c140004d0182201040c1900103004032801045c91990881ea5403441a4030340e40c0440d561a400040d50704141e281400c80d00c01c0c1c10150742c4141c400c50515483d18442c9040710042c0c2034a1554080c003003007502d40181e00d8040c0c18401c2e01c80a019054000d245c44001c2c105004c040c1802d84540104281e03400790074810780301c40da101900600d020b4400143c6145030580e03040c1c104425284401ca00d0303031141c5850298041d1000300c0b100c0b2150000c0c18112400744100400c005041442004040c00c9a81d40d54007490005e00505144204a03a9a981c545401c240c60f10901d40d1840c000d00c0f403001e0064 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 241650512 1250 241649262 241649269
    0x1e082a0f030d0c180e0f07050702030d0c06111b1b0102151b03160f03050106022107050106080313050f0a0e15030708010b0a350c030d050705010515 65
    0x1a001240c036960081035800492000391034a2450039418044c116900d40006000c80380043c029008842945403400c0c1d540314800d013124584103840010307404d03912990804c80840e05c1000604400c5004850000b098955240c0840c01c9520051140c0b01c071405240091511010074820310580c405a070400303003245150100049e4480d00458003c046401140700003c02000d40d42c04841c94040391aa00b030f030340c1d070700c0c05048102c8901190f481d00b000240f10683c402c042e081c080d2003454165000e0342c004185040c81514024205441001d104c544c16000740052400101e00340a103501a2002c240a5038079001c03260000120075519904c5a80b0894903111124410b0b240c610700381060303510080c9102001d6403000c030403404090f0141e0030182c1604c034060000490041c19400701d031516104950000d0110f0b40c4482d54200010226007800b00c5030403070303112000402140c0c00c1e0740e8a204011350990307070b030b000004000a062007942c000f1240450ba001a240c010802c00780b0400d68800000240c0e01e0441c00d80c403010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 241651762 1250 241650512 241650517
    0x20306010b21040501020f040f060807090b04180e07080d12020304020a090506011815020d230c10060f170a03020c06090d08160b0f131e082a0f03 64
    0x203001003820b0101c045014004290119a00112180145952a0f944080c05030009d0501e00c60000040d00f41030128408a100d4200501158490441030341802d05000c2000f11070580011034890050743d03620300d14800001401060001c1052801801441d16103500c054803d020200d036a0000038070400c1040016a1401e14500c2941c2110500003030076541c00c00142c9201075500b400a0300e202c2510300008032620f00b010300441d2018941d0a940318900b5881c0c013642e624072a2030000552001c081204041c2881280c0a0440d0000c02011281140c1400078180212a1590800c82d10105588410700c6445070f06400c0c22201c084200003800114000d440c02911803c078000801d1050a001428805568030700001c003502c65004801c0e10343d1034120030722038420038a030f082080700c4c018a41c000190b488004252000d210f00006003e40c01000842d076203a007000d114121181280503184c41c01c880200e4400405000b0100c00013400041380d034140140c11102c800d6150b144841c03a80071a1012841c003002106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 241653012 1250 241651762 241651807
    0x130c1e050a1d034204080708190203070501060e0c120415020f03100503010603031205070210051512060106090506090a080303070203070c0e0c0a0e0301060b0a0903020306010b 77
    0x602c1207011452030341e001e050166004609515205400e0301421042d41c4401c0c0e80d02149000c01d90080543c489000500400d4030700f0207030300c010000b500000300403070390300802454540e01c104480d07880c2800a4a92004010704100030344016403002c01c6490422a00b40304103009030528501d040301a160112007032000d8421000c0300c800210b0900c01007002c01c000c4260403d4400c0c0e01480039504c0c6c01e08640c6428058004841240c49005443c8001986041c107106190a50b505640c40802d001c010600c038001411300603242c84e0452041c502c51040d102101e11609009001441103200ca180d600300030001d00504460746594150030403001004419004031444040b20419a50755455a929600042034002160310400083c08004100300b65a64040010503909100f40cac20344031107684802075524134103011a80c1080d082400c00c03c06542c207008008404d41100b0040c000303e9055124920603480750000715068001c0b450380c004c11700440c58240b00081c05131a5103c2c0150809480c9a01c401414480e080c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 241654262 1250 241653012 241653017
    0xd050d080f010e190903030b040f0c030609110301050907021513061401081e071509080609010606021209030f070b190e0d1113050f01050a0e040f1101020a02130c1e050a 74
    0x3d1701da03000c00d4043d401c040c00a540061080242c0b101107241f1501070210111000c00191902d9004621103030b851240c2c0c0c40f6504e405020a04507801c120910807112070181c0000c0652044401992201c540261111710844142e412114610301c0c918040c0140c0385002c00e0321030b210b14050300500035030400103100710000410002c0403420610500625051203055000400441500444040c030307150802c082034101e48250086490b1a6079154646d0f00722200c3d8000d18005802c00c0b080400c568200802400e5201c030014140c0e1030450042041c1850502941e000000040020590345103003803040d10401082c0303d031810641100d0303110100060003814401c0008061170744c40d074007400240d00c0b00d1665544094030700c01c0800c07941c10013614250060000740320355442420101c2c000324990001403045c602440d030004280491f90031698403200340805485d1968118070a0000d6140540d9924011550801c0801c41c00200c00340b21110052009002c00c1d0700604100100781c0001449078004c0c01c4a0600b461403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 241655512 1250 241654262 241654271
    0x41814040332030105120307150b040209060a0c031d1f0212030702070312050f07170d0906090b16050f1e0c0d180f12020d050d080f010e19 61
    0x40c542c5001c20111035101001d00801d803540c2400301d1000c80118140c0c0d504a41e940480701001c4600303a500d00c01c2000041c0108140d800411304400980c00c45080c00034000c20141c1052206000306903d07801c0071501400044607a1a484141904819000c40c4024948010140400c0350408200040726000d4980c17403c00040140802251003400117004804d981000a596410900381c029691811400b05540c404801880100c0c0305008000720f802ca407280480c01800e29481d511001d003c815180782c900300c041820450740518a0b401c1c0f00e0300103030301d100e01400aa031001a0810340d940baa4010101d004204442e10240c039810b40120035907580e466103906040c2c0d44e0a0034503e6844043c05000680c10b604000304002c15825000b0880c02c0842216569039407080440c00120b085144141c0300300954017525080900240004501500010380080d00400c0030b04201d0799101c0c6003c083e01c030a100040d0b18541070105000445a00d82c0c0105400035400e0f0300d50a0484034000b02111403841001155a034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 241656762 1250 241655512 241655537
    0x70c020603040812011502011113030210020a0213020c011107380103120e01030501050f010f02010603020d0507030210020109081b0f0a081b0304030503091c08040b0418140403 77
    0x283d0003181d800c076050240e296010f5940303e07200e18000768100c46610155080280701070100c103503c41a281006503225902d80658559002c0c0084244000c24480c1107004901c40c200150303c40d00c01760f25009081542c0180d942d1007100f019800c44c0d0140d4110303d00f065003000b4070804945102d100107451001103c03c0600b1451981c08000d6985c030801c094440d98007283c00004c18031036071840c0c0c41c40c5078406071500318001d40d501c0d00440813540240a5642c0c800c1e4690b00358425035105240030002d482490000103a00fa407690000b40444503140320440e4560311034a414411030510b406028811112800240040d144e00ea803885850b018408050092182e01519540d035580100044032400140c04240c0e100b0890500740a141c940c0a0410281c0c02c500510781ca0403001130000c02c9804480d00100610305154482c4200450000e450104254980740c00903400007061451008000a103021204203540340d01e801034680903007032030030103070307540c49141c12030440c40d40c2071700c01000b6802945841d00d003082c500b2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 241658012 1250 241656762 241656773
    0x50705190503092d06070201050601030b04092112092018040807030912060b03011b09030b06041b03020702040b04020c03031501110307050703020a090629120712050a05070c02060304 80
    0x4802e140c9502c4e601c52801803000d45501980942e00459080c1e0f404d120380881f8009000548a82c840001c107200c0071920481b5810a41d11460402d510041c54001e402c4014040e5132000d41c2d001c0841034a120440b0740010800800f40704004c500d041090310482c84100c0d20340d00307884061130001d00141c402d0724009000d404240c4203c1501000d0045042c90201039400c40c24410000d20b03203403192600940c60300b203c203001208811a040c4603040b40c2c0c1c1d5a0701d0b900703081d9660341003401b102034443e6401540360038411000462124040480c4c03400342c1d0380180c5801050040009441c1094000380c042da02c1089503008034600803003100d034031005801d1499041c550314801203c07803c1032401c2c200400d01020039600c1c02c0020100c0d0754800c581c000c495890780c89440c2c01d6904100c82d4580308035420084a41c0040c1c20003202d48074403020341c81d072812a039410711028041c81c0006640c00c44000c00001e82e11101003111001a01c1441e4002c030b00c4030301c1000140b500c5d5002074007004003040083d01c00d40c0c011002504108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 241659262 1250 241658012 241658083
    0x7030c020405010b07050f07080a1511220f12030c020d150603051005070f0f050f030a0b041a030d0c02040f061712070c050607060f05070519050309 65
    0x2503029008210540e0f650002c0410b50300549000c5846000d80c4910301300310000022941d00369400361f40580f010200b82c3e0369403040c0c803c42d07580c49861140c0314141d002100400380c003d050401d1510710132054440c0030b15040071142c5060b40000d101154841024004103032008a03a000a55050400f01c040301030500001c0d80000c4120310041180b1030303092000160040542049045038442c00881d0741481c102105c24080d20000c58010300041d03011484000700511590024120300024100107180c0303860603c00b9003640c1c1c01100e44900395501d0b12190b6185041c41e200d2507440c1c410100c0c009406520350f0002903116505030341e01a003004061740c4007005650b6254400c2038085a0300c0e40030000940c0c0d81800b401039003480340d80c1030304a00503141c3c24140c2207c908200c82c084ea40c040007010300103041004000712030300600c0e415504d09985005805c020b80140c8642c42c040c0020340c40b41d81d101c0e8154061050b8054110110300308004d030920501441803400030704203515034504c200d45182c4002d0100304e0620752 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 241660512 1250 241659262 241659287
    0x30429090102090a0906031e0206040e0f160206040b0705030711011d060c070816080f0d09050c0a06050d0c0c021804060b0f06090907091215060608010b03010306020703 74
    0x14011000340444200154000c0404400907100740340190750712a00c3c002120714034440580a034040c60265101c2ca490b8040101c80c15100810041c20300b902c038900594410011908009101143d00a000c1294803920f00c985c0600180c0c40180380c039103003d5551310f514282c081c0031078040c040080b011811250080c0c6102c0e6070400008020011381c3d01c0d40c24480d80c900344210415a160103190003251032515408119145140c00c225900c1c5071a054a110507003018243c0c1044d070345520184007210409603000002c0491040c2c80401203401002801c0150800303004d03410191140402c00d90800c8543d80180a560800107498000154000110002d0714480c2840000943c03243c01401900701c01d0454125803405240501d00030088400c20006015603200b1a00b005580400d0034402c0b804285040015194060b600d427401d500c441d41e030b49804410008071010f04460032450200135042120b4644075070401409285480c040a504d0144a4455480180000b40c1103640001c0c901c814180114100140d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 241661762 1250 241660512 241660583
    0xf0a06020c10030e0a0b040b090a03020a0f0201020a0c0306050a06090b0d06050c0702100809061e01090b0d02040c03020a121b050c25230f28060203070201080a0905030304 75
    0x320317041482d198040042c00c6400700c0b004404200890910400064030058440c1d041e00100105002c0d5114182444031201c0100d045102c0c1c9013345c0c0c00111125100801144a51400302d00c40c24031111440540f6101d0300490120b0745480360031101d5a0710441c02042450300b08200203030f140c40c1c0e030b2425442d901c151140a504120541e560001c00e80e0f004c2c00703113881100c100d000d840d003540341c5c2650404080c0640c07021884841d65200184691506540054009140244600580d120650210b02543c2d046100d81e00444d90210715a64401e40142000c0f05140103207100700800c041e00300d95621490855840302040107070215690b0b000c0d03d4100301c0204440d27100c018440e00c103404044007000440003400340e00160640d01000d03c841060242d1b101005c40e00082032100740c0391a03502030043d0840100f20008419a007030603062070780f2040021800182400b44d0181d50f40c0c40c3c5500000d03020320009040d040046150540315804544007205030391f0090b60020114030509103045690044559400c1c1e1030b2103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 241663012 1250 241661762 241661773
    0x1020d0e091b0f1306110312010b0c011e051b0c030d050c1605010c110115060e01120e0706030b03070b0301060e0109050907020d120b03100e190602090f0a06020c10030e 74
    0x300021513034403c046511959503c1c10140c00d03602011744034003c0070401d07202d08444a0052000320186000341210b03032008000001c1d140c04102d04042c1c0c2590800c2103056003039403101400749400c05201c41c481c075400e504506071b24100c2481c18031503903482102c1c0c220007116030301c401180f80c0b0702c80b02d02141c009102080560f12207150f00e0409a00a00140c041600402c2690710440c0e0f1042041c09646084440c0205a0281c4c514262007035401c000da0441031810890003c034200310f10700c0640301c0c615406006000402005062403000340403102c07072107000791280e8031255041050400e000c041704d06503030740351070112404d40c0840f0068072020082d03008950301002447c208104107500091910100d05661b6510582004501c0054111041d0211440d01a003010f0380413404011306411966800399940c0c03c44813860241142c40360980103108007141c29580000e03e00c1c445150072000e05100e07040c1192042202441c00d00d000e540d070111080341ca8000c0000200780c03031195002e5480a040380b000041600c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 241664262 1250 241663012 241663027
    0x5060307030612050f1014150303040b120603060c090d080d02040e070e1302040f062105011e0b03010b03130f050d02010923120f0d06060c0201020d0e091b0f 69
    0xba2501900c0080f11510701c0346e100018501810350141140c7e482001406203020348460f024a03180750540000d003038061104200c00251015402e009041007909500580340a080c02402c0500b0f00c0310107461805000c1c4103000351055940c0d614982c020035540905c003590740d212800d880340c010f400386601c60301000e54200b00b0400715075000014903060041c111600c00d0a10107090200701240a01e00400c410b000542c00244090f80c00380d42c01c81451402c11003034560b0301000b1107050f42624400d8000310b8030784086d1004102030484000d00040503044291009007150306042c0c0c10321607400000c061b40054040308500205004079880000c10154218064178207140100401034082d11645004403202c0c00c0d5020140300326000307003852100032200403018064402e0030480c030760b815030852080303050356900c10405c5a04600081c0f00e680c000b0404d036103401c00c00450600019080c503072092500307000c0c0719074200d41d400e16580c1d0040c19030340506008003802403040211004505030044582a03055070390001541c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 241665512 1250 241664262 241664273
    0xb0705063c160828110d0903020601080f0d031109031236010507050709060807030201030c0201020c0624040f060e101d150916021207020a05060307030612 68
    0x110300c607074140c00d035000d4007101004007200d500d50b0440c3c080d6000640864a4020700340d20244583c602c000500d000f0a000d10b85ca0091081940403400715401c082e501c400c03942c05c150301072101a00401800014000c0280009112900c50744d070f6000b04410540d07038501c4404451540e00565103406400f904490280c0781500714202d01340e129810110150101e00c055130b40d914202c200c0c1581c01c0d540c0e0f8551114912209006407a190400c4d00c007140e9902460344081280b00f25481083c00811904005081061450001600b103544900d001400c59004001c182611400000c229401000741c2e42d01d40d205000ea00451341d145d02c00300c40201d41c002e00f091122407881c03445401003c00d0300e10302c0c0e0740d031080c03525441c58042c0c00520501ca11744c3e0840760780c0c0400403c4503918400300d510080d00e1000488841c3d0680001e004aa0300315810480c80e035440070340d541000e504206410420720f1341c1c2440d80c5000c103613400295a410003840342d14480c00300000000e1095201e9080303003000346440826205030b1000c61806 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 241666762 1250 241665512 241665631
    0x108100305030310050f030c2206080312010302010e060307080721110c010e06040b13051005090a03020705220509011107080406032301150201060312180b070506 71
    0x2010701c2003460086d4134071b4614010502207400030008081a60b8111485420782040c503a0070340110381d5603940d0740c0c001a004401d100800c600c403070b050b41140da03c1d81944009400310000c0a55940500c00a20030400c140e40c1050b241030b007181c0b0724100407112500490324001c41144031794080080d542843c500c0c0c1d0080c400800500707141e40c0001c009102d1032411180342c80e900c0c50f080310080d012001d620007103015084025025150140580140e13000c0d1035400140005484043c0c2e100c20b4030341e01801c0300105055040c0404000307060215030f2035600e010062250100510800601580c00f0340c0c41c80418040142584804101c9140790050764070382c80c031801c1c600c003181c12034404d01011a0408041d43ca000c01c0109820041c410650758412199080502c00d581d003208503081d01c402e66507a0f10307002c408180110340c412038201d52507851908080c032140304440d0701c0c1a2540204540c2c0c4007840039800051020034102c0c1d01506000124202d184d60000000300c0320000020244400c0e007154403c0d907550b904248 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 241668012 1250 241666762 241666769
    0x20405040f080c0a110d080901050d06230f0d0302030301090c031401060215010e06030604060903030e0a0b06030706111b03070f0909061406030a02090c04051305070201060501050304110108100305030310 89
    0x1001d4500c2814030a2146c02400d846c0c0081030a0300420904129600480241c42d0b101180da0380050b041ea20f907569400784ac20302c8444501e80d161210401c6200e0310f070400d0250740403103054560b460013032040e581c00781d517a00060151802558075400d0394003103248030b039100406480800a0751140340d40d503080b01035118101c10900c4201c845400d400030079080313031182c501802100041c00500480c1c0d92900c0d10b41c010074103000d04404164a41a0102407280108030002c21382e401200410064100242014a0049550300000900070800481c41c80340001040d100301041908446440c0c10351800300007800d00341d258000840040c1e01c0d010119090740c03640d012007800c038131400003000283c40682c0b500200001c102e0380b15506501181001e1700608040042c180c20202c802d001e02d00b031a48410008820f00440c1c880e8801041c0c1c0d520401c0034036a424000c240040400b030800c0e03869814030b41c2340c001c45294170001180c113010f8100042403407803031442c440c50001e58020041d00d40f64203040282070480c907161311 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 241669262 1250 241668012 241668023
    0x40506010f090e07050c0105150f030c061b070b0409090b06090f06010309030e030109030509090f0c07080309030d0e0a02041b050d240617150d020405040f080c0a 71
    0x1522540681c080d10181d1000e602c440450619110500c00d0141005202004000f001e00c14103105540c2400383c40c0c007410403180811680b1881005124800a06801c641d11944c044c05007951107031903a108413401c528000030300490300344242046510706a8994800c4a03103400015001484000551201005901c5120075500b507448210030045010020382d400c10300725a5060100b146907000b680013489091290500c140e148100c04000703800c591040c10290b006c1840015555100d00e03242d05030541c03106d1380d08005401d40c101551822110700441000800d00c840000120304c6005082040d42c400d81107850041c440700d00151590740e100c0810440880c0603500380318070b8607401400a0701e11070b04001c0580e6070b00e044c0080d0340024805084217121644010210103c0b6100c00610317191480003400031503d83d2000035110380c41d11108400018145002c004c20103685c0d031025514541c0303004020b0b8040304d001c2060303202c84c14201c2d101041e0160007000071000042c1005086c03c0821154503590046 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 241670512 1250 241669262 241669271
    0xb1e070b0703110906160609050d1206080f06130c03020303130302040c0206010b03060f0f10080f10030503090409290a14040507030204051b0406170c09010c20060301030b0604 77
    0xf12030b003a2050081180c2c1c181d2142c01442041042600780072a24aa41d005440124080585444030743c2400030581c540d0780055400400e4001000844c002c2c20000e0407040c0040010301a40030010391035000151011b152080060a508107000450100c3c070061078008059958403c110400040403213120700c002c03030081d800d00401e61002c1d8004550541214503203200c1e249540d0f82d01c1c04100c01401c00d030f10046c1e031001c105000c800c00360301c8031242c10741c01852a032581c0c0a0360510700d000c05405100140740d4410460342c0e02d000d0001420100590305540301c01c1d0340205001c011031800100e041203145054000011500514100303040c1043ca40d1300481008a04020050300c074034840201a004440140180c0e0104008000500703066201c9680102840e082e070030764440120403611158416400100000d89980742032421402034096560400910520382c0c3c5807615070070007e490780850403800341c0000c4a500d0243c100c49404120110076050085c4004c0c0e80b507840e4031b409120001c0c10b9a00314002c07440d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 241671762 1250 241670512 241670531
    0xa030b0c040617070e01210221090706050901180b130510180b03060409411c030204090c0302041805090a0f020d0c09091115040b1e070b0703 62
    0x840740d06501520741583d0381e5002c080c510740150b801f0141000706a95820b800703900c4821007500b9101903c00c0064844130250072904c59044130903281c5000d8141d0310309400400c0100100ca402030102c1b880d1240030b0801c6008940c3c0805500c56040a13548103d066500010305101400f05820b03a1400741e0708108d40124a100003100d0842e181a0094240707040411410070a00106a9600240d0742c4900c004002051041c85581c4404901410900300b0300c481200480703034401a155100c4084c007001c030345c000d00c06480301c00042280d82e840c1d158500c000e082002e081d0a00000d8840d8040750050f110036a02405460550b4400400950003841160207040340c0085619400c00c2c5402500e0080c3c00f00070041905c000e40e9161002c154011030b038203d038424600c1c4d00990000d245015400d0040a01010004843d00c80c0d0405545c2e60701c4002000c0d200e00c8140650102c44182d500035202540d20071180302d515040070409640454200c1a1135852000010070b1844c2004a101c410074403441c002d50302440020704 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 241673012 1250 241671762 241671797
    0x30d03231513021c02091c24180204050a0603050610030c090504020114030c120f040210020d02071203020c031510090c050901052506230103050a08090a030b0c0406 72
    0x4c04510045003034801c3e50705555444070350060181906d005007d41c01180900841036118182c01d2012110714000041460345010400180e400d02c010410003070040f040703d0010741040d140c14000080c4655540c0c4003054800c140380d40518040c41d80002122440c2c20301d80701003c0244002d1001326141da95800c8007003069640c070300400380031f2641038460030420006503a41c40120b400007418030891050278030180107500d0071400340034041e008403040c0d01403500381030060140c12008000b82c4825075002ea031410068a90009031001191200c0d4052400c81040d0300d412400d025403070b44001d5040c400c0c1d051900e01d480c0803152080c05040e6140c5d41340c030003d5480030b02005807030b4030620100102e10b05001c40141940104001e0103100d0302203400e000300001e125803181c100c60009034195007040d90780402e0121110304000a10308541c103419030413503c0d0324680d541c07603660b14190802001400040b46550407034481d07c2c1c5075000b03582c2c4440380c04c00c01e10b0640d200342c103160070501c500400640401030301d414020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 241674262 1250 241673012 241673017
    0x3031505030c0f0d150c0f030b0303130b0307030902041118010c0305180402160b01050109120b0a0911030f150c07120c0c0b16060f0b030d0323151302 66
    0x582c0074111011030a414810495500403145060310b00b40029049521007a807148203d01c0030312003940f9800a41901100014115210404814040d602c20400004501c00c2852034204403150162500c0d40ca030340d41c0c8401c9001d0a881140250041d0034099241c00044044c0060460596101075020814414400440740820070703e6000e00802c00400000c18041c07600d10070103a108101034005890691200d52030881c401854800303952400f501c100500182d030f440420340c03000b01340c8c0410282021019032a074900074140904126400c907030311842d00c404c2100180c0d145060190003400d0f1901031861408180d00c440003c50345846c0600080d0003e83c1d406a058244c8407010303000107480442c00c1030301105446040c2d0801041d112055000e400082c40d104900c010300d542402040c5004000805180100c26505c40c11304461003e8105890441c198800007030400ba548040d24020810b021440350701c03820340e12f1f4402c0058003012a101044150b00c140d94a064802d82c080d11080000c14034030800b00203d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 241675512 1250 241674262 241674283
    0x40e030a0503040318170d0f0e03030d0e0a0b1810181b0f140108061002030f0a0c1203020c0c0409031e05120907051905100804110d0303150503 63
    0x3070400e0020a0109215800038034a048a40d10f1000e80c007a120201190003592160300c440440c0c0c001408406000e0344114144082000c504100413521040d20000b0f8482c09000b41880c201c030b07a69510070609010801070003503c6a00540c0449650030002016405081c4040800c0c0301480b03400c81c440004120ba1081c2c82c3c6200a400c55600201c90f6a95001d41c1e004101d074514041e90a039000202c1d901c1280c8104200420741c002c045503201c141c083c005016075038011704903481032003940348021041e60044111007100001080380346e503034042c0400c180c41146c030f4010060311407200c0440441a045d01039004114a1843d01c04946062021008000a81d0001c5400400040520440d00c50b0810641250340340401d86003032060a01a141c0000100120111450001e03907010841c05c000034208107621201e1424030182c406131690408001c1940f4080541c2c903107040001090000d0f00380300003040030180910000304103045062241c18000d0203009011404904210303000d8001409180004018910 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 241676762 1250 241675512 241675517
    0xb070c0b0a0522050a060206060a031403070f060603031b020a170109020d1a01060504031205030c160b0f010f0305060f1f0f30060b040f02070b0402040e030a 69
    0x495080003000c10480c0c201c06800014008244a11140070304800c210800700b04400d10600c40b1145440100134422846510020954010703505104940d101d0200b00c0c015a5005a141320140ae52512a50314510940b840a809107058803a4101040b00b00d4020900300e034003903a901c0005c410300c03110702d5414104102c030081d888408610104440310340540c02c0782d040b240d28030000907040d461f03401088000c0310914046800781c24008003400c81c0d04100c090076000d0500c61406e182440c0c2559100e90641c000a80c80e04203200303000c40000c3c113081005044403411805a104071040031070602e0034000e004400e55615140c5c00d078000000c200c1840c540c0c1050112508140102170648a0041d030840681000c3c101080307804403410004020450b42c2400f40041929407c544126850070016100520010070007c3c0f040f410440c800340111010001c9024007900302200040f001c507284002401031403808400c55a060010440a0034001010584c3d407103140259800d102e402d01c09596240c8a01c11846200003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 241678012 1250 241676762 241676783
    0xc02120a020c0111210c0601300206130b09040f0e0c0d0609120f0f080103030c0b071205010f030303060b09010203221a030a0b03010605030c040c050f030c040f0b07 72
    0x1070b98402c02404d103810b0030f03140a941031240e40350241003040180b1441403079150b60000c0c004210f000c00b003281a00412028a0813141d208801c24660b1120300030710081d9001c02e1100c66800199070700c1c80e00700d494200e400c80701c082d441507803441240fa0603000f003040715106519100d0498030640f0240210000f1190100292410703038900010082681540310040d0350043c0d8910011000603405070b4800300c601515201c0d01081c03004600c0c000c182c14202c81d100c204008c0940010000203070010301403010f940c0c0c000c3c0b601c1043d0342c0c1d21a00725201c0250000e141650b904101c00000e02d20415003448050b81d0203550180001030b01c401c0d00c1003035480303070044a900691040220000c0d0b0a0310001c3c404c010001d80c182d03814010707030742c030184000401c00034201c019001000092011904082c0714891001005900a01045140400080c1c544024582d100d009035100e00c90b20100b81c3c816411101001c46841c801e80c2c0b03d06201c555041160445e001d005640d504102021440d01141000c0c0da10056200e00c40c0d14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 241679262 1250 241678012 241678033
    0x1c0e01240603020a0306050301020f2d0f0a020a060c09050f03010e0d0809030f03040506010e090c010e040c05041205060105030f06090c0105070c0e360307060c0e12010c02120a02 78
    0x40007513201603103403002c00d0764440300800d0719170f0280001c1042c0c0182c9084141c9803650000d28090800c0b2400e4881a60a615050850b0518540e803e0300c00c41158490280d0705c941d24840240d080401b1351000400052400030070300002c5801c000c244080e20426210702040344006070a2600700c440d040600101e6600c048000b254651080400c00d174000802002e40b420b142c49041d8085c0b15400030358040300c054122030014411801c1295a50350700121903002011017038120700c00a0004444840d20500594603040d41c0c024403800f0310200d81c010f120040c1007482c3c003a800e0030502d0b240d4900f0b0042a12034001c40c00d00040d0b030389002804078041e000c1031019000c0c1002c1c0d41d2c019180ca501c5808115000350628400144540a80700d1052003048075580243d030203031010368194030f0705503119110305600c810040070f520450030000c251091658000d1001604c4419a00180c408403904c030581c6610041c1390943c40281801901310001004c41038003207881821104c80c0007551402601e03040801680311800d9503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 241680512 1250 241679262 241679267
    0xe030316020a02090c040501030c05120a09020a1701021b070614070302011401060206160f0c03031802060a0c05070e061c03181e0e0f010b0f1c0e012406 67
    0x80312140c0050048841140c03060380030610424044a001c403807150080340400c49943c1500030351501c540a844c01a191160912100d10b80300d4010f4401524159030720b40b400215280e8ae904400982040f0484600d0440003024250203580000c0c601a299040d03420181d01c860400204001543e101da143c920045034403440801c0c43e03401c00c1c04103804540d2110103601d2414084460640a04102c3c1c0c090f103c03600d030a03a0f84400ea079030344c2003501d010400c1d08182521540c3d84075103407010055040c1b80101c1c42c001d00d00380c0003031881084c41e4060b44c410400542150400e400c0f06c0e18819562240060350780c3c46955201c00000d0307070400c490460300300c44204641100c00c03103047d074607407299440303810100744800c0000c0106011000340c1c0c02284558072002c005810400301940808001c0050250a5059250451601000d64030611684840311804100c1420702c42c52030003501c140ca120040f140d820b10810030748400c06400d0131082e2603142e520b04191240040d40404009100c0c1e60030400f174400503803511004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 241681762 1250 241680512 241680541
    0x312080408070b071713050303370b0a0e0103020102100b0123090a09051b07150507091a0c0a020f01030e060c0409110c0705010c110603180106090e0303 67
    0x1c07100708004010319400290b0101c1c80354000e5407180d0790080910b0044211000f1844040c00c081c00122007801241c000400000460f50f01001300e0808049040d1114240354003000304940104800301c45401c0d020890095034032411a04500300d580046c860b6490403400d1880500380006170058100045400d81400a504a8230400c00185803801910300c0340900040d40c802c0719601d0108030080012034510a1400241c0350024044a100c03c20840c2002c000809160086e40484080c080020a28606100c1c0e40c13000c081503103200050a0107146402a4010700c40c08040c0103044248203104a50128000c00c001600d10182e01c81c4000c14194109800300071140d112003503000d04250302c0766070529012000703020382070088031145085502d075401e10360f0a000b92a2070545100c3c501409122152803940002480070850b5002c1c20040300c0c541c413901b0030b484c51401185610b50084000828481200c0d040c00f100c00d000381e40d90740204241c41d00c545408090319100c40740b020103540305001141e00c02c410801e0303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 241683012 1250 241681762 241681771
    0x60c050d0804030c060c020606090a06270e030f04080106060c030203121005030d0201050a0e060402030601090e01060906080a1101020c0d02061309090b18120f0c120f0c011401031208 80
    0x2011408100c0303079505c1c203007514801016140140c00940c02c0c0561410050075071504400000b03014032410381845288040031003e404000c4240304004070804040d52690320403c056031802040e20794600c51790a00b001c81c1c0c0c1c0944035410b0707250310701040002d5040c0b0954401c22601da00d81d014501e800491840130402900103020000c03100d0814100180a640810410810410076000400d1929013450034100321804001e050340e071900700b401000010b940204916041d01e14143c0c0004103c03609020103401007259804c41d041042c07402e5070200700c04a000800f005150710039400035011290290049803106001c0d5031168014100080490061070254081c141009059081000321603441c0b248006842960b4401d59607440302c0014800e600e100d07400c543e148255086c005204d004002c2c13840ea102407141c90b520601031003001c610955501070a000201c1c5011070305500617120490704003440300b04d074050000315040d5807811102c00c569860f00c80d402070481c1d81140381e4500710a411841a41c01150050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 241684262 1250 241683012 241683017
    0x31606030b040b030727050c07030f020a17090915030709020c011806090b09060f190e0708010c1706031504030215010f150e0307090b01090e150307060c050d080403 72
    0x200f000c030a9032001c10810300103051083d440c201254101c018030940b500b840040b03130303121400c1008100c07880c03c0c001c1c120f52007940d00d032802e4000911003040883c10300403082002005d80c0244110b10181c00c0e01500500b8047c1ea00720b400c62a60345400c80110180d4490456490b01604040010820007038030307074041c0c5454440340001140b5007003c0301215080c2c0309030040840d02d41e036a8000c0c0c48148540d408405074041e51034002410981442802101c40c0380009100a100c420702001000b1001c4040e0004500070141c441110308094840c074490307000c0c080034403500c000a5081d098410000002800300c0f40140c0001d0003070305000c050b00c8444c030341c01c0900034425010b600c00c070000d082e070308491503159500034098443c158040301d0420b4088900368009071840030807c0a010b146414554000ca01c0e0411243d195000003042d110590040c0e600d018280d000100b0364549400304601e0348413039440c082c0089000c40c243c40c1b1042e00d50a007503a03454210400588650b2014500c5202140201c2141c1c0d0071602a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 241685512 1250 241684262 241684271
    0x10060e0d0302150c0c03040e1005120604060f090f0308071d010516111309020102100207083403021606020d0503070f03060902070f051501050f010302091305040b15031606030b04 78
    0x1e0740c5d1403565002c3d900011650225004002003c4600800305000e810102c440080419500c0e044903903480c2c003d80b0180405940c1c1100d00c85644e007503400411100e41c44286001c9215060402400e200811991800402d02c00887e18481000404405010301416101c00c1e09146120b00c002140000d035000440380e00264056104040d40c910420400000076450082060034040c4002070078902d4013041e07046c20a0041c090440060828015a52460342c0750814403648000386e01c400840b80b1a03050300850300c000d00e2014500380355000c030700b85854000480004031482e40d5040d00f04d948204020704040060b900f407003c80d45080c0b080c000245504040d03c3c02080080d01d030905041281c0c80280f040b544612a007a269080000030301c0310071400e41181c55911015890040400d1040e01c100040c41d04040c5e00107600b0b90300f90341c1e0b40807104044071414400c1103985072620345000020400c3e50404100c0e0134201e20607210346800a4856002081403607d003220300c0c500502079026081304600d2560050700c0d0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 241686762 1250 241685512 241685527
    0x601140f0a0c02030f12071b05010905060a0216060c0204050f040201080609042a03031107181113030b04031202090a090b130504050607090611070312050408010510060e0d0302150c 79
    0x8000305d03030b0304051b5907800c0ca6484840d031130701081e8a144869091150300440d00200400da07003115085045550507140b05646100e0000304a0812545420020010006100100b01b040d4088980041c0340d1003600d0802c0607886400701c1141d41c1e4001c44d00240000d44400c000b500303e041c032700d50154001e4414500c1a1030320007007680c485503448441030a03020b14521b591003081810ba22003844030740303080c00d0800b0305840740c18155007014a00340c00c00d0b42c1161540300c0207c20f481c0141c4c00101c8007c01e881c2c1100100d10385e202d1401c4604100305980940029500b1440b140340184c5510854001d124001c00014001d85083c0150b000703000d0b415006c82e40200880802e80d54a00c10380116807246100f10007800440c60aa2006810105290000c801708007410185590861000440c00252500818154034070b040f1103004848521039500301d407803107500700801d0180c01c40c8541280e0041e51210f403900e50b00d0280e45e80c20b104229164602c0035006030700200002d070280e03400c0e010309504124034890052a1140b0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 241688012 1250 241686762 241686793
    0x207140102030c0306011d090403050c07080304150201060503071409060103090218070906180b0f040503120403020405010b0903100c110f07080d170f0a0603020411030601140f0a0c0203 81
    0x441d00740502c00c10002c1002810343e80400c600900c04149218080c0056001000c9207000230018030040a01c00000f6510802810802000c0c00500304003048035a181d44440707401c20614440c108140143d801d0a601042500c0c001c5140710a482c0c20403003030b003d00b00010040094000000d49540c0c14950740e9001c5402603214602c040108204010300480c1501780000001c007409160b6000f60100140c1c00000305403094813a240000310340840baa40c9481d2000c0381690051407045501c100d9240c401c01c0611291610544090401c803130080310100001c0c0e82c1d0791624a4580704100c41c4540c0340e04824060100122180e00034402c1d80320514101d660b040c454407003640380c0003480c401d1040c207902540f0104080101000243d040121034a01005440c61443c000c070b1040348c001d000c5014801c0d402c000240070301801d03400309000711b40041081c40f0114140720090f401e0360040d6943e40c00100d9000c00b80d42e190f24040304846403509a040054a401142d09040360a86017030398040f41e1501618800f10060f04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 241689262 1250 241688012 241688017
    0xe06070b07030b210312060a120302070f0902070f1b0506040906230303090d0f02040207060506010201150509010909020409060f0b0111071401050c010906061503060506090f040207140102 82
    0x8160b40c8000039418010400c000009510808210386100b008102c50004030000c81519440581c04c0080b40c800c1e294000081c606110039008580100c03401c0300c001c0c043c50b500040c04411141e480e82103e0041c4d0700c440d140780c140e10511102600070144500d040d4002144c03080320124034004400c003000c2c61922403000811030751240d8003050300d4603112182882405428640c0f0700190000003040003000b42c056010039140d0080c140c00034404c0241c400d4400500c11034a05418456600030700440d560072051030401c0042c4820f42e00325006610301104078140c11541c01004007940e6006000d035020760719052081001c0c2141d610203d0700980c480081c24000f0760140603000403400414000f09294000100040070103846201d07000d1305a0184904000007010640d48188003034007803800d00d99800c00c000e242030240c814400000c0103280340c500000741c90084e00c58280c6850006075030500c50542c0c0d810400c1400c0c0514169664041d00c0003018000130302d040d500810403184144811a0011460301c0a182242c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 241690512 1250 241689262 241689271
    0xd0e010603060b0f010e0a050927030a080112050a0b070e0a0b03041a100b0a210902100c1104020703090f0f030b0a050108060a0b1311040906081c0e06070b 68
    0x60b403a030400d90000d2400e900360844c011003c0c81c00d00c442c0d0a0400000740140c110b403003614040e0030440041080090301c1018002c41008a11354941d1298104d40c00550f60b0f80507031118000a0320340e800100303103c2c0708441000c41254001c0002c00c03c4908a0702c961001d01c1d0040d2100042c00b03040c0359082141d4440440010040c14900f00064403441c0a023401313000203080c08115210050300f1801c000200124640400654441c5000640c17505840c90081c2c49000038051401e0900c41d249a82d091540001d4010009840c070135104400701e4495041c0c20b4500e070014003001089145503106664260800c1d85c046c0403413601a1511030055030381c076182d0602c424000d0b000142c40c040004410700602c251170341001c6d0450b844290030000d83d89000d0045803980300203806d80f0881d60b00c8075440005076607079000031ba00c21020000c0400500c1860302500c1d2050f48140300782a5840d00300b000c005840780000c110104c0c40c0006090032005542444022903802c0360011020794031000c10312110300072070032044103030b84034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 241691762 1250 241690512 241690523
    0xc030a05101a031009020d0803090105041103061005011112030f07020106063b030d020307060e07152304090903021020160b0a05040b0112170d0e010603 67
    0x85110040c41d2005950903840840403030740039082e000e400d0f518002003050407000c42040000f101100c610010f2810b101d00c01020740309074004011700c003110006602880c001da206d500500400c00e003c07005d254a0b20005c440c401c2854051400801c00740d40140301c1141c0325284a001e031b0380c400e45004441c0c03000390415121f02c11011014070400c10f10540901c10400500a242020b0b4250040100d034982a001c513109686001e11580000948003002c00c10840b426010040640384681c0341c01c43c000303542c0e8012403000d8030380c0e81c01e001c00000c2100010500d030058800346d60411405184091054075000202e00b0f89045028451400280c001042c00c00750014240000380490381c0300c003504000b46030180b80f40c0704210203440d006840c3c074511000403000d02000703020b24205403200c507480440f88902c4240440580200c0001040040000980d884a0312680c411022280b46076284c486020002d080a07100400c40100d02d407240019280305006008450802c0201103154100d41c040c250075190300d40d204542 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 241693012 1250 241691762 241691773
    0x1e15050d050d1d0d06020922151a0d05071701030506010302091f09050c070206070602040905010f0609050105090a05040905060406060b090609370305070506041805090c030a05 77
    0x40156000b201c51031941540640d032043c555805000840304038080ca402444240d0015000e180d51329660400d046426416481c402c19043d00324441000c0d188a0160400505c8200c5010403540c1d00304c28000200e50700c42c1032050400400e85c03d28001003034050400b80501603401004075190844c0e20805010750311920103484607501d1071061281800b0040c11245101c0401000d682c03030b0a10603c5442e080b10031000c1d02281d0703525601c1c035000b040c1c4030350007019400ca0310015022043c031000e60010421201981c80400550380d944a038204a240c80e0b008003000a041c0f00340412207984503101801d001c280050400c192580d032040081c00311909983d08803500d802840810050014a120b114006c04104411525000c040c1c400a0240d1145c241081d11941e488000380300c80d0104424003401c0b10040d805180c43e41146590304049000652004540510903400c0214440c01c1a40c02c0c2d90460f00c2030311b50001c0c912460300020003d0400204813410038400c4c03408000709940d08102040119015602808 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 241694262 1250 241693012 241693033
    0x14030703080c0106031106090f0405070509030d0509031e03040b031009020c0c030c0a150507060f020406021b040218120c060a0509030f060f010324060315050a1e15050d05 75
    0x504004424200390f2081f80e0601200e400c0340c0310341d00c110380c1000307040303a001801d640c03090000c2c0d500d4001c20845540612440340d00e500c000b80c01c04000c09088804401700c1e289081410203005c20003c0308400006281c20600041042a00007006940c11048002c0500d8002e82c40b09a00d400b2a0005042c440030340d0b0104100c1a42070906101001030303607106440b10b03c01d25090000d511120b1a2040100c400c10030f000a2020074422603902c030605503c5d0803201550344031b94582000f950307040d5001c0080b4030044c14044840081c5424070844a80500005108444143c50010070242c9007190780111018020f03501020160b41d1207400070040147c4684a007a22154003509042c82d207038060a101d07036903a01407001e10103214140c00700c03581141da01000c00002c4014424600d200d1040b0204034811060820b03201104100c08001c105135000d14080040000d0b075206000041a240c0c0c031810850701045c4c420003030f2583c44668000b49a500c24044130b800032655500c0210b039100111007810b481a8004040340c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 241695512 1250 241694262 241694273
    0x919090c0c05030405061830071401030b0607060608070609050a030f12050d06241e0e01171f050108090c01050307032a0f1814030703080c010603 64
    0x20a12a00c051070011180d0381681d4429035a44114040c05100c2c20010a9010241c03071080680c0301c0144000d00000d8140301881c8458414020600210720200e00300c0441131420140010300301c00b152103d40c244040c00c0c0080e80150300030081ca94460b600002c00b04800d0001c10864043c031401020094018001c1c14a419802042481e85400c0184501c10148080001ca9081c041128402d5000103158a081ca8090800e030b880b8854040b0000c03105042410024182503100100404150000c0d19101004801003048803030074901c10030044001703414111007105c01e100d0744000c41044c0b03060604000032800c080c5400c50801084035400d049428152507510b41d0500560200d0042c1000e080440c5242420341d0900c0c0c48a6020201a04014000c07000441c100d129401c6511400ba418603508500700300071419814444101d0b41000214020a610307d0303c0500c244c40740380f844000881e00c40282420214801c028101545105500d485800004008141c000c001005216000b000014000c1d1951519 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 241696762 1250 241695512 241695521
    0x10080105070e0108060f06280807030605090411040e030f03040c06030e030406050d150b0c0c0a0b0406030e070510091e3605090312011517070302091909 67
    0x640811860300741e182e50030398001e0007082d0000e10480342c00403130407400750100f40c4c43d024948411240c1059110303c2e0642c3c1485084c101030b5034500ba510000959074400041d000d9805520819400c2040c41c0300080c0858001a004600ca50700100046100013004140c0b500e5500450020814001c0000500c400c01003800e581c00024401428280050002c03520015224080ea1150394240000041c0c9150f600700d4a60004a4221054032464805600c922802c0810b4014000541d21032080c503a00b5503042c030700800c81a003203501c02e048003843d03d41044000c60117001800c00212691041d01c10100d156622a1070401c4100351607550041100e02c0c00e00b2a402c0c00c248800c00642070302d00d8407000d00000300c00e101e0444510250403142039038042d0320600c0300042d00700d003140c242e03000d0315200a224903e0400b000401c1080405070307901c910799880304903030701070b481024881c403000c01c1000d4101c01d419038480080310360080603030030300506003200bc5011840e14400f0044d40c107001c07000754000703100301c0390036208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 241698012 1250 241696762 241696771
    0x1f17100f0e09060708070e0618041404050309040c050c0a12120e0717030d060603060807060516030c050a080a09091107120810050a0e04030905031501091e0510080105 73
    0x710305041c10200c02c51621410003600410402c0003480c0040e00650161483c0c01c072080000d4111a40c81c800e41d100034000700031b121502840355081c03000f440c0100106221071401541c22034065442c047c82141080000c203807400480051240510242c50020010300c082000389010b01c49040d809a50500c0060802000186c0100c80714502030507403552032000100035090342d84040040c05400e801481092130360280c00c102d021600c0c01c000d0081440d6074150803032402c40c1ca20100725000151070710401d03034060181d203a4540e0034200d1050300f000402c1c031411180852b00d02442c20787e5042c0781140c441e0080355010030b0200000c04d821000800805016108801303c40328020510f40c05c0201301e40d00c0c165000c00c9904204100401400411008010421400300500006000c0b21a09685038090507a000c030848065001c9001c159000526040224031186450b500412000e0960b080465140c000e0900c0c81130900305d1168131850242c0340f54103100301c40c0034284010240b0a0140740c21075243c00d40d10000d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 241699262 1250 241698012 241698029
    0x2120c131809020325140409150c020c0f0114390d030e03030432010b100507080714101d0c010203271c0f03021203061f17100f 56
    0x1880d107517404003800850243c0c1c003200468601c9400040014001e040030b6500904540360008100601d044264880000030800d5000c1d40c8081d0010b80410803495026600d45000c9100c00c88a0240104d0000c0100543c5844055450b14200ca1141403074000100b000d51040e2070b0544000080e200d07004210040900c00d1034903040c0f2100c00041c1015480b4000a080180741340007030648810303c0e64a01d050b40803241480ae450305580c401014416020302402c50005026058400c0c0892a49100d1030860700015045000e061804100759a04081a83c8449030042580184181440c110340f0a01a0281c2c100c1e51a0b40740d079a11200c0ca410a0809018400c03190555004000c034002c1070340010f04003c0ca400302d8545155105c44e04402141c0b05d2842103c1c1c60341a0301d003a00b080c000300300001010001c2c241c0290b080b100c4620340d27101b480000c5d100c2900d441d9440302c0038211480d01030444018030700601c08145041000f2020381004448480001e490110500c14480d20900800700f00b6071040d0002d04580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 241700512 1250 241699262 241699303
    0x804060f060303090501050c101a040f1103010b0d060302092e0509070e030a0f03051315090302060906070b0c0c010b06030408040302010e1c060b0901060302120c1318090203 76
    0x55801031304001c82c07442500d05201002c0b030b04241d504003d019001d0362024411040c00a4000314000e50b26140c0d20640d03051045280608100083c0c20521840c4149050381185a14690800440861070303000b105401842c2034407034002100503141c40c24603e00682c8041d8440102058080c0d1482000f1420440c808406041c1c202c10459582c803814501e4028516042590100d46000d01281c1061a100c074094602d4191901030010150722500905103407000b4001c4865241c0c44803c500503902c60b4581103000240800c0c1c050000d80f5203403000704a6071000808152501c2019a03541c2526441110712080b10240810f01c586021030a000c0c3c2c1c0039200c400c541061861810307076110b48a6000318040641040701d9405c101d5030a0301c94460b24800314000b060400404e0310f2034a0b00078080d0401c00c15081c051000340000240041c007074000e40383c154054003003055030b941d600d000c4154103401100c02040194044c40000486082120410511090020011036095014018140703880002c00410744000c001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 241701762 1250 241700512 241700519
    0x20a0c021305060f210106080d090f060206010306050c16050f0606040b0901180207020d0c0f050a061e0509180105041a0306040807020402090915030c1e06030c0d0c0804060f06 77
    0xf24400143e82110841d00810045100e1410584041180d80c201c8651742c0383c000086623842d0300044e59070120300c05130703140341d203075520382021801492540c0b01c1c040c05684880014800228150400d9900c07409024655040c000c41800e25441c1c103064440a4449030001d08203089481d1007846140d41c810405c4d1030601044080c400410184541482981070180070b414041701070f0401c64040b1403451742c000f040b110344c00e0528201046000030a00c40d545103060302180003c6d590801d41c0000044a005454080d62245070908104024074a06031240811800b0040517216a40b120100418520700d01c0d07891303400c0d41c1001c06000c2120600e602c00c200e401b40e80d020f108281d5500081141d409540100296200c0070039102140190051001d010b5001030700004200f09010300c074041c2c0400480850444007419494800e01401281c07000a000f003940d50028400c145041c404020b5410501a00780320b07143c566681c0d44901101d04911600700040d10003c1880244070150240301d1039000210f8007040401d15 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 241703012 1250 241701762 241701769
    0x27090601051c0f06141f03080906030a060e180c0604080d0f0e060403111f1e0e0301090b160e0105031b0706050106051908100e1801020a0c02130506 65
    0x18016103080844071002c0c080e040203410a01c02c0c0d80340d50b00800c18001c0e42c81e02c0b02c0082418100b111031111119009100c0304003a141d4003105c0c0c04072500003070168a05544101070003180e604c02856a11179a407101c90004042d00380070302441c4a211300941c0d52079440b00141c0620700340304c24803206e948120024081482403105c0070441540c0c0706914240001e41ca040341c04255007039195541040d501c010007007000010f0140c0060005d800d074100702c8980300c400d085409414920300300e46d880040011141100c0c00406880d114109002d5103c0741400c00c061500303100000d09495580a046030075a45800500290f030501c1d0b905140c2c028101e0610011005610b00020502e000040c10b1070f998140c215148000241c1c2482107894540e003204045c0003030360712114081d1107a0303c03a294180038036402101003d5007030f110f0051035000304071409581421a280c000c022000d2180a00304000b0424a6401419140804d2006000c0b649541c5c0340c41c9040358283c0100170f000f484803030444507810f003850b04003c075954 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 241704262 1250 241703012 241703029
    0x909140109150909030e01110d090b1309110705061b0307081302040207030f14040e041203020f0301030606030b010e010303020606010804060b0d110f1f110c2709060105 74
    0x244041c2002903040340b0140d18031404001e6a0051040134a0240c01505055010103c2c681c01407003a00c41241c0c4d000f2a05010307640e0140c03000f440c000201c40b98002d101c418443d10060141784540c4013421203550b01d8420141c21900c0400709000003a5000802c3e00400c54280101a441940742c2035582c0001c06c181d0109032540b20060901003089004000207076081030200d03a00403a103070041c4c02103441d1175851501405598080740c404000c01e40804031400e001c5410720445065404100801046803110f50300d0002c40031049500d1030505409000d4a00e840d034220380a14029409414081499469400d10b4001010182c203c0e040b0045030200600110360001002a0070940a18000700705980358200350000342140004c40790b005003460700d44014800d03030044040401400300c440443c0c904600003003040d5140721050840070320703641c508600103241c015031045802c40703c5181a0b40d02c6080000010302d4604812105c0e9400740b01b0650748009031501c920403143c1c8080040300410f45941813100091055 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 241705512 1250 241704262 241704269
    0x101d01050907380a0302030a0f0506030a020d0f08070c06120b0d0f050f030d0c0e030c01020705061b060a05010314010506011407021503010f051005130501081e0c090109091401 77
    0x81e1404443c040e060fa495402d00c155240d14485142d1240c9042c40020040d500960310b0789143d905111491020017440c0c401c03180525001002001100116801e211242403400380c16500354420301d44810204188070000d0101910850010182e40d00740400600842030401d440030b01c3d64a0304840c40f002e0f848010149040c26080036001251b90f07606d02e000b07803400141540081304d600002c21214001ca50682001c1170760001c9440f00d20050303102205040e03036001002e4040340141d01161040001381008030041c210021000f8010f4070708241c108640c0d1500034150b03555000180c0d070b80300401c1404821514140300200c0140288403030700f400c0e40000d0803001e540081c03200c00345000034510215542c02da003071511072464201c40354496940706c2e1180c921040603c5000e00481490754413003c4580310700c0444808446909441520f5801c03c001121000c80c001c11303100380707400c0018130100c036002441321a034031034940c1c501455507404049000500007485603100200e07280c2407000c1000e407040e101c0d8226048d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 241706762 1250 241705512 241705559
    0xb0307030e1501030c05090612011e0e0f0703083a18020a0b0a20010905070e010303050d0c090b03040b041704050303070803151903170408031803101d01050907 70
    0x380d02c2c0c4000080d4000c44000402c2c03070940c0313042c1407420002801c480164000740000b07010414240d11008075130f21118207401307620582d004014144001070b42240540b41046051c200888510740542c000e041c2604a40039049480d0f00c06601520b200040c0e01440c1420282c40404051071500d43d808103140310a42c0c0165959500b001c600c0c80501481614202c244510b0b040084440310301885130240241044602038ad90303402001c1010551814800c2c1441c1241c0d4960707202c1e850184035107526030003400c920387d80700201319022600060200450000d14002c60084034410b034a401c1a180011140d000c1c1c10840058140a010400079540c02100356460f0a13084031078160740c2e0743c900074504c0601038009489684940c6092489141004c1b0003528002d49100d03441e04542c808003401942d0340340c087c910800d81c16034010172000e5210a000d400660b000c0310003134111042c0400240d044001e560304108205040c3c1c060001980c03040809014450300154000d01410500b400c140da40100e11703881020103a0b1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 241708012 1250 241706762 241706779
    0xc1b020906040b130b090603030703080a050c16050309090603011109041107060501030f03080a02130b071a0a09031b0506070810080d080601020c01020706051b01060b0307030e1501030c05 82
    0x2a59200c0750894000500000c0074541480d81901303040e0014171a00300000e0140b0354004c0020064100001215078264268407141d1240e6107000c12440905801412426122802c0c001c160701c000500340b15400d0705110384003454a441e00381043c0059024001d146c07504c6a8101018510600c10740e000b01d8013044400e90380400e02c001c4a001d542e20300d12135444002c04062918000005202514407042007a600c641d0b1901d4283e00c4400340307842680950201180c4221010600b0482c484503180101040351180020200302070460300c02c13210446c0122642e04003d5114ac15030350400d580b00f0403a00c00c1c030304003030340610601e000d54a50a80d43d040090400041c04441408580c00000c0310010703000500200b41164a0304108060080138001d0550b0b040c3d01500c1500c2c0c500c18150300104648055900075541d250034520300d22035044140300d07540c4050000707551320320012402e4404040154070036261524049000307036502000500d030071a0415909201114a4014030004044602d44070444004481810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 241709262 1250 241708012 241708021
    0x60108220203070f030b0f0105060301060807020a0b090c2103191206030f020405090607081b13080c0a0806070206190e01050406091e02031002070302070e07120c1b0209 74
    0x10000c4000400c041e61511072044001480950301d0484026684194500d5450b40c4503204a05003006013801520f50051051005101a92155400540c4200789204407070b04a240d41e1103e08440d0b606480e601441d03089074054010501700f01004008080c1004c18460011003405c2d4141d0f2203000d004144020b001030034191000c03140c0b04598140c44400054801c2101a5481c900b08841140101007240180d0408002901824004c41c03068411030300c944543c0129541d0803480704821a44501e140700409003440704540c2e2031134030006540a0038048004098015075242041003140761507015005c4c50b0b0040c41000700040d40495595000146804030010998011014001410340300e00514025031810040100b0f1040c1900914010303400780c40f4004c3e240c2c200a00300350f100a8130315006509640421369290306da2455500a0030918003900c142c1e01d00d00c3e11890f04003801c010a039240c40004580158880c1440024840d0150b82051410300840d00c00205400413014601e80d10301a101d01117a50008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 241710512 1250 241709262 241709311
    0x1707050a15170709150201050a0c050a08060f2202030a1503020102070b0703090b030c0711040c14090a0509090a1a06090a0519110a0e040203011409040c0306020d06090b09060108 78
    0x100c024041705c90081c0700140343c0c03403c001c0c002c000868010f02d905003401d51070481c00d030060040f0b50240c4403035551129255200018000300020b1121060b4200c0d0602c0b87c1126002c00a1501811003641e0f500c0241e80c3e8280b17801400152081451114002c0260350700800050b83c0010b003c408981c4103050072500d8941d64101074072a606a6400b10b51865000410070618280a2005000040c0708010b0f1044050f5201d043c042195040d000502c040785461805030a40059000948086400100380111554403540418409141030300d04000317540c01078040c58104280401e410b03400c0c04040f00100324600c0c04074005180c481c400340440b031401d50b44102040e20000884201d9800100240f82032040d81850200383d07003079034812558400000c50622182c1481c0c6001d0081728101d84100c5052485001c1d8901080001200039000310b48000c81c4940010015200740050910800a400b000803014609088007003924916262644110f85c89001c0003202c2e80c020341c0c4150030415268000d5160801e01014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 241711762 1250 241710512 241710527
    0x1080c0c07030c05030d02280206130801050103170a0c020607030203090a0b04052404060e0102031c050612060906040b0a0b09090a110102070303271707050a151707 72
    0x3500038000d140c004801c1c4003002416004896042d800c07540c80480c0020300304d0f01c0c4c208288101c180c3c03c880d151482c00000c400325103605440e0000781141d140140d0301e1051580c0e034005a01404259444100400503ca406075124418240040e0318070f03e0000c0c960002002c0d50b1004800a102e0200450b2040c00e1510810503034851201c00360000e0320142c1c85084280e20750b045071143c40d00c02c03101108403c810700c85001401e0700c07034030300c903a41c00e8101400d002003503450681c00d40e06a03045200074003c003d0050105007034400d460741c58140008290401030144903103c03080b5503454402c0d6011001340121f40500040841c0e009800414a001503100c580040700548401071050b40d000700c00d4030038002031900c00b10b503041e1480c1c0300b07010611803240240d00580c0c55001c00c0c400580400c2d003103800e88100f80e041d000d1800300102005482c5010580b01c1c2c01e4075200f8030011400c83c1d0350780c0c48100b0521160034400c09100240081d4540f12640c5441028003c20002c20f00100e802c2401c0c6501c0401c900a019010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 241713012 1250 241711762 241711777
    0x30f0f160f060b040e16120501020c06070f020c0411070308060a12032c03030a03050c09060c0313060923061902060a05010b190f020f010f020403030e041a01080c 71
    0x180a02900380c0c2c1c01e0040c06071990030f0240b40314524003112400300907000503201030500c090284078849549444c08902403a10402c87c182c5455400b081590070a55003030110074412201c5864003450700c00140402490720707501d00308981c01146005407000c07040001da800da52010b54503140981e8603030b4803680810130070007841d444850012080b14107031301059003118007098208010b02e0418100d4041c660f40051402c013298005030590010059208040d12940000750720000440c21989080407660100340030b503120034242e00c280c2d0030200b05034001041c50785280f1700400641c40c1045101d414280c01d00060180102d00d141041300c007070072002c10307525110180e4030394400080c2c18480310741c150380c4080d48406080714400c100030b190800105106c48100d050341e0484030b44014844009140f220203036140880c03000c000042d4881e00b40e50100c0040240115842002c250402507103a500d03524018001c41084611548540c0c2405142030b56104005050b0030030007424a05281141c468102d5800c1520803001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 241714262 1250 241713012 241713023
    0x504051003060c030212131208090a17040305011505010f0e0102010905100209180f2212020f010e010204050303120601050d060e060a0e1009051005040203040c1502030f0f16 76
    0xf500c581854259000d0444000c1c0101068819550064070030700c4135140c6100281009078103048a00010b2040f040c581d4031031504412110303200801d440f0042c80318100f41201c1020007000406100b00710080c09107510540f10780d5040070620b0b0507c000078040400603480d00082102c000400c9125038401d4101220340340c0c01c0f40c1521080c00b40b42042c0e0010b035010403902c5000341907800341014106041d0b14514414864042a291503031180650202805801d17203c60500326042d095010202d0300d641c1002c61303289002d80080c0042104d07803e109003034402c85103400c60310ba48140010411610013100700e903a02c00b102d440800e5070b40c0e50a4010384550050300c060082c0c40e464210080340d00500403075424081c0d1000c4a400d80c6240d42e82d00f80d2001040f08031078698400002020805c4800082d400c2a5045004564100c400b5900d03800414103c0c0c03c00c541c15109522a0002040141c143d0280c800c0c8410861003d1490840d07400541009440b5150201030120400900b656003141da055403c21400c2c1d000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 241715512 1250 241714262 241714271
    0xe060706020f090114041206051527091b0918030f0d15030206070b06150d0501030215070302030712020705040606020105040516050307030201031a0d030206070e1801050405100306 79
    0x3040448880e0f04005081c074080b4401c84500c84c000010441613400303c030000c440150403240340f40e44280c007070100980035080142c1c8040d503080381580c81490110140408110504201140c040d0f201c540748000750002049030002100600030008807204901c8907981900c0b400c110341c4a0491612a8010250300c00505000c08940200c038841800024064607500100a1040e045101c02c000c0409081c0d00c4021b5110404012220000da0070a200c00c1e4000c4004020891603508010019900d034003d20980842c0c640c0ca40060046142000704550b40e450483c001c2170500c107107030798040c1d1349202c0c511001c0d190704540820082101d2080001030060034001d04144441c60b0788513800390182c40d043d1000ca4950285115001403d07058000e4002103a07002402014624034540054004101e920100c00c0d1448804c40d0301c160325145d81c01d22901075481395000780b2080c0340ca0480182041e40001c0710510a405005407250365a0841c1d602a06541381220002000c1d29540d80210001e9041c0d4070050055050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 241716762 1250 241715512 241715527
    0x1b0a0c060207060302090108150103090501021804060b0921070b0d09200a120503071406040c12200d3009050604060e0a03140d030b0603070c030e06070602 68
    0x520050200e410a400311042941c6824090742a1700035082c0181c005092900010313409081e182e03580f412041e043c1000250342034603403600c2c1d099901a4030803013030702440d030f00d40341190341003500c6070030010181e03400402e060110ac200019112034200e00a0480d80300d0f4000c19240c011001c0c0f1030000142488680340307a44440656214010f4031112030256880740783c100c1070060a002d505c0c0b44c1e1002c0e410080c040809103041403014403091020b107200381c0740c1d0b12003407005000081a0840c6000c0342c0c00080c0082c1480d103020300d4811755014440d081b5090102034403d03000c0002c0e41c418a101c049104940c00d9503030050034030012405104100c4405080030703014001c003a60741420b41c0b448141e41c540c04c104410600010070b82c183e03031403001c3c4e2003800d8102008210800203e0300c1003600d0801c2100c01800c19900750350301e80741c0079107000000814038001c1e085481184105901445100010501503600509503d841a0080e0807000c034500b016090042c20442c072111a40c50b40202c5e0348080d0701c43e03400c541301e008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 241718012 1250 241716762 241716773
    0x6040b101203030c030605030f0d0f17040f110d0b0604020d020f180306060a05060409020c010e0a030e010318110f13140414060124050f030708060117070906051b0a 72
    0x101d007400b1302083c13030208081030b0b40c100410030424498070000280100204004212000103082c402c030004c01c000d00605400d60182569450f001d00d00845400d00c0d0480c280c200b4240010b8540c2502741b040c1c02ca09021800600904070061b804502241e00507192880740c0307001c001a03c101c020803942c070300000425400d024a001c040900b840c00541c21225940d99400070300624526601425500010a0008004000064000b407900d0f9051400220707240d00e001c414186020301c0000c040700400d5190b0000c14055030b051040101e40390010074a9801c1d2207042d00c400b00740e100d54680b00c60290030005e00220040d164402ca0490043c40b904040000700c80886501c14031500c20744045a0580c03500400c1214620300280d1a8161107120001640340c1540c1c1210601d514200d91125003031100603c140714031032007810040d40c46858240c031000f40c42c0c074116000610045030700070400c5205203d4070500c504281c0c0000d200302541d1030760400d560b8a412940c460600140d0305007003111180b140c04407070000c200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 241719262 1250 241718012 241718021
    0x1a0c07060315181a06090d02090411060a1d0301090206090402030a1518061508070c11040f240312050f0903031602090702010501060804080a050c060a0e190506040b10120303 76
    0x30340400c0c101d091450138604001d21442607186003a4041d10905800015103080c04a454125209901000d9400a800c02080303094201414400c081030a144c2c03003c620101c20802e040c04480210001c0000410769400201c03180949840540119404000135262510135403081411405090100c0c195642d902c1c02c1001d49181460050549805c00100007002c06003145d040195443e0303901c408003a6910f20340c1c101d480210095090361510308070744480f101620385105a618041d003008022800d110468501c60041c18690b103d078440c0c500b007a0080002c01c440c0d010210041e5110302e0102d658095504c210801e41c091404955410700002555454185206100c440528400d88060f0340e25600c03804103a08032a424400d2030040740c00800002d00145001d402054103240310300740503080030048018a464403104452512a01c1c3d980c0103030245822080006812202440301c0c18401240a075550395100c044c0504020710380380000022807100c01d0300c200daa1001d0001004004000703821814018044c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 241720512 1250 241719262 241719281
    0xb1305071205011518180908071e0b010605120a020a05070614060907050403120c030c05030d141008070e0405010e06090a03081b090120070b041a0c0706031518 70
    0x3400c017150105d000c1c9101200701d811a100500140e03c422801d001c0714014042559080b80c41100410a44000610303207803003440110090751104003002601e20700410340034170603000541448414040489195881c40760b5a40c81410f030000541c850404800580d401d001e82c0074020641801c000c0d003030408008520f00a07103c0e00b41200c41403542d480304a03060b2041d20880c00044c00c40c0c02c4080d0955403003400703214115406031003442d00c5a5811050348449056403c805a8a8111a200d801c00b111141041103229080b402c006010001c4c140760006407607907130306144604041e40c00700d44009014804294000e106541d611410348002e07141c00000152a000141c204401240300d040110341002c0500944411541c0e111100d00d1500b0b08050055441040e80004201d56244000110100d150309100c010001c00c2009489a241e606050041e00542d0340c95001003500b813000d0050700504030f8001000f6080740c103181400682812210040c401b50303540c5030001a4082851200102d0751030b850f50124011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 241721762 1250 241720512 241720517
    0x181a1003020d0b060306011202130308120402030601060e01090302040e030408070803040e0a09020a05010c0606050303130305060c0c19032d120504080a050c1e1509010b13050712050115 81
    0x1c19403c00304120f42c501065802d50300180640c0c00c3c5800c240c0c519401081001400e0040440c003a03a2a980c001c0303558000003c40100c7d081d198244011414108a40d6014001074100341d210382542000003000010f8611000c0d00c100d894402e400c4200d202030007108d02900c4010f0540b90103030303118050240da960180c85080001c90302940061180d1b4114402c2c2c400880c0d00910002c444e5290034011141c82e5000c0c901035900e10b0340d9050004290741c0400081801c081c0390261030401c05e245003006401c040300105403400b41d07401000784920344000440c00207115829000c07150440141c901381104d60f1001030700c6940203d215514070071051a04040710007003403101d40e507655181703806000a03d410f450041d18010308001e020b12156846500480c050880d08c01c40904441d006ca0720440060b043c25152182400303180c02c10b6022401c103000c0c460502e40e1103000b120090110166a1002c51900310031588084242036450002c21b004078400d0245404a581c403080500c02540c454089511403894004200702 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 241723012 1250 241721762 241721771
    0x91201150f080a1103010209130c0e0603040c0b03091006030b1005030d120b01020f150402040e030408060103110d1202060106031512021908030a0c0507050901181a1003020d 76
    0x8101600c06101d00030354000e58041c01054159940343e00c519544600826450354003403110107460f49498400d04185001604007041e00380d1130303020150604040c0c0303d806008441c100f04110200312101c6010b0200c0303007101b09071a0381741c1da40c03203409082010304040d2207491824110700100340091002010f00036849010680703540c0360b940c010950750b8100080fa09e00490200380c0100d1301201c1c03a510924209106005030358214139840400c609000300031201c0d0710f10361220307403d00c03040d070a1601c1001c01c84044c0b10021883c050400c0581a5548014403004101048032410040c040d2520015070000543c058025040903506c03090103526004240200c100003031a005180c0341000021201c24211040d000d148a00c403002030f000d101c04066a014903a400e60141c00e0300140701d03c02000105629245039660000f203400705d207040c41c20a5030a0740300c68425110700380140007010100c640c2030b040c01a070031340009400c44034062003101192142c0623298822011606901c0c0b95405070020a4500c185900411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 241724262 1250 241723012 241723019
    0xc01050f061008151906051818010e1012110907030b1c081b101b0e040e12030a0212090613020d0c050d03030204060f17130809120115 59
    0x89403000c002c82000000350010003141892821800380780310b112010f404080f2a690485404000640320f40c400c0780002e10000f0030451064280a10f0b681072501101e201c10001a00d640b040e05209040c000c05034401b4405000c1502100280e11a034000c00307952080c1c4142c042c142c09c107540058450012240590480800900d4840c4030748104106040000c1003690a036024650100d6401d070080d0045031030780000c2050313000400811580e0406828490014442416245201000e6420241b16561261000704000c20503a03040349181c8a81001520000f480c10701c05030065282004000d440003002d003002040c030070700400d142c005210042c65114802c0c0d40780c48541d80140c0d18030341103aa401c550300d0110301072030041c0f13003010241180c54040c072403c43c032283d240c400007220201c0ba400d084011070380c005010030100380c214601290600f860f0408844511603070088000701a001442d03040c0c200d00c0c090031070b810000c00c2c1c2c06441310142d0141000da20003c20204c002c0c024800b14540d44480c245002000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 241725512 1250 241724262 241724269
    0x1404050c09010f12050a06060e090f0d0914040902042f0715020903030d060806040c15080117070914100e0c070602030411100207060305070201061406030a060302060c01050f06 77
    0x40c120351080080f4245980340604800411140750005c44040c040c401002c170105000340207041c0a4a03085d0960b5096090184095180044450520f01e02e6002005088045504200d070302044400e00304050218064000c00070700200b0440c01e0082d41b051a00d9140b0202500300c03446c030040403610302c07600c480c08511034101d04041c4c0a413901c002c05140350620030300c0c1100110f0f0080c01100e4009030031a810303c00211140c030251641a049581d55500400c100010302455a60f2000200b0b090400721000032400704000703202c54414000c0c150003e00300c629480841c14100a85001003200c0744e41002500c83d003500714021418261444120070040c03d5011413602c24001400d03024100304105503107080642d589010107900001c0090b2030015150b00d82e1f619a498404100780c101d08a980940308050504101504541000c5e100c8001c40e807604c18103205a009200311420a94130440f4910b0b1250307503040d180b4010300784980009410200100761611452415044036001d00e40d844020310241e9180011b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 241726618 1106 241725512 241725529
    0x604030e03010c0504120b071e0e040c030507050406031a040f0e0d141204050c0a12030915140703020f16050411030c0415050c011404050c 61
    0x361506103020700c1030b4a6200700a0901d03e00305070514040300384a011085e00208100c1e000c502080d003483c040ca9040c1049260070040301501d103a640402441c011039446024000c5081010250005020380140b51060110780d691504051415030101c2c0504480c4c0c03074140c0c40b9600d03180f014070592285d00641c00384500304c01000c599907100b103070242d140c91a070006200800403015440e40304104100e040358642035a0041200c0b158441341031040c10702002c010026484688036400181d108200e03034000329664000c0d110030b03c04130b46d904607000040d40182090300c0004e0340300702c0d0036007203152410182414600a1048804200c00340c1c081c82d240c03144078032000300601c0d45601c0400c014070741790144846440c480e4540c42d0660a0074415265140202d000307910703180304100c3e56101c03154803880a075910792940030000c1c488508050713960030b501c960603903040c1c03154050902c9424040c03d00c0c113032 = true := by decide +kernel

theorem cover : BRFrame.Cov 241546762 241726618 := by
  have h0 := BRFrame.cov_init 241546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 241546762 ≤ n) (h2 : n < 241726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
