-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3749
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:54.564433+00:00
-- url     : https://prove2.me/submissions/cf24fff0-c808-433b-9518-6a876fb2679d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 674100719 ≤ n < 674280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 674101969 1250 674100719 674100727
    0x70c320a06020616020a0c0806180c03101e0f0605130221060604030b0c0a03050114011e120504050a170a1d120609060603010f1e0504060608070b0307080f090c090c 72
    0x25410007036860103015888024072040c9051400000c917030030000c0ad520f2850780a030144550554001481444011082c0d8000c5aa1000100300401c98040c005035040307424240452581039900a500401c200c88084461460308480d034500d52080340f06085149034954801010408042400c40b5419048240600903e2a20745d50740c440c140d854a059030a803090500002e01d80c41482e505000d45405084865072208405058000281007840c00200c8000907107600f80d000300f01540241880400000d19801c1400700c0d10309403a0058030381c2c8403000129034034003000c055170b6005100c20007604e55007001c3d0340b02d40c004d2082402884042c1055140b103e503104102c400c01c06503d070003d0001c0d50080d0303404170040000d800c0402c101030035540c0083c0080c0ca5585403084619068181c02e6040a007401d6051000032551501d040c984058410b84d005043c1da80320711040003034060f2540008500c500042d81c0c4490b8151980c0040d60764204050b1b81910043c2c1c0102c0c0202003e141c142116a002b000d075460281c58 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 674103219 1250 674101969 674101973
    0x60114060316090315060905060901060f11011e151202100e030c040207050d0809010c1403040204020d0207050706030e0a0f060e162c07020304030305070c320a06020616020a 76
    0x4d4030520202c5c00c0703494031580c0130001c1004501613241c108004440c2e40b1803a40c1801c80c0280312540e140c82400c204051508e03000fa80d00000c0d80b0039040b00c440310100510950000e000300002e820304800c054031070700c050304000914804084a0f049019401080c41d980900e0b4160200da20341b081c03040259040c0a8054918403e030394501c001c0c5580703441880032300000102c40d00c002e4070748540204502001c0c0d04205d45521195031002100b42c20708582e9000035100d89550010070300a0240b440202c0c1054400241c0000780b120018102e030855511742d80c00e0104104000c002c50300c17020310b540000c00030150b400c1301c80005591600090100001e910803075540f501c00c0c1415020014160307222007038140c1c0108080707070854804d115100315480942c04d20760a505100000a649100e02d2001408000c400714400c0100056107a03510000e00e1800300700402a22600d100c0b81d00b411062284e041000b070803c407682207504001a11400302c0d5000e030041c05860b80c80001030000811078082420443c0903003503900d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 674104469 1250 674103219 674103233
    0xa0b040612030e090403200a020405010e0f071701090906150b19180e09120c0714030a020901050105030a14041103060603150a0207230a050601140603160903 69
    0x4021404600c0c40440c41d5007030150a1040146000740540c00c988100008690081951418801140d03940704000c004081e50a003004074602000f9840381c20f1900015040318248500f40c019108003096040540b204070f025200461001052110035488000402c0304141a40c0410fa00c1400b6100c00306c0c0e1010402070301590360f4140d0300319411a401c041030b00880340b125400b6035049101c85050910010010311012613040000d4410510340859032800a0800d1a05100c1c1141c61a10b00140c541c0346d2404105858848843d400b03444410300121184c0d0303186140020760755080c03940241102c0c900ba402c0500440c0d86a000400700241c8540341c0c8400070455615020300349c41903010f003800d5900c4181c0328080506203a00940854841e501801da0b041250404041168000e1514000140c6c0d031015413a05000e102200c0910907a21354030b48002d0210508041541010a0b01c00c0094400b640e0700e80040d0390026600401a54005000f0310008404100d41400c1c00c403e50005d044c45006d8a607640d903041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 674105719 1250 674104469 674104481
    0x604061e1e050f12010e03040306060305100c0807080408040b07030207050a0b030103030f110712080307031d0309010c060f02070318060903030e040506012a051903050906030a0b04 79
    0x2803108510000d040021115450000c0c118203210501d80815920389000511600380e03010450303100b1a48010811407004096200c40c1890800380182d83e101c3d596420943e000380b140344025581405007d202d8082c3c080d45100c1c9030220801600c074200e036501d60010441344002d00800403143c000f000c02000c02c61038202c10250112900c6507000b012114140000e2050201c4a81d00410400700140010b00010360040c9011032605410311300112031015001c8550701c1e00101c0c1d03200c0e041e1541d40c110140113214220b0300440c81006e480e00c0c140494588902c18494041c1114003005241d0018040f0b14101d6200b84440c540c024000c0c44082020111101c110040b43d00c601411030104400102d401003101c1400901e130014002d034140001c0ca01d01e55140640700c0d100ca501000d2140d603450000401c1c50b0b02840d4505414090100403910301024190404202d4130549401e591a1203054102c59806400c120a10041075055071a5403c00c084013060001d550405410000138907100e001c4d8110944542c4918 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 674106969 1250 674105719 674105759
    0x8040f050f010b041b02030703120b060a0e120f0c010509040f0204080105010f1d010311030f010e0c0a0e060d12090b0a050403030f0c0f1202210c010b0111060f060406 73
    0x580c0c3d4220301c003084100c800350007240141a04801e90950865000b005440f1080d4240c201004020000500d0034000c04004142c150b1007000031400d01d4a03a68010322444001e1410381e02c0da0b4400b030392103500c50382e14050b110003101117034440c80310010154031034809400000c0d4007400204031081080040000d82e0131a4104203c40d070764400040100d0b220401091005045040010306509480348225400840501020344a041100c0f403409254074100218480514840000c024039610010301c1a1200d8104811038031544c912030011840c0c51440341c001d0b00a0380001d042c50605e40e0340da6600d400310a03807101d010062100500001070f2030340d02c10b40100401d410559540d640c5038150b18000e002241c003401368000300140c124204000030075800803010800e4001039180d940c10318074601249411850a480d0345440002e0800da14258401c00181110b03130100390092007580500f400465501c01c1c914081001036101c080440c0310091214902600028043d1022407100e40360745200e5440e9040e1890 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 674108219 1250 674106969 674106971
    0x606180612041b0b040b0f071e0303060503010204080a12020c2205070f201618060501020c03031603030912020604060e070503030a1d1c0c2408040f050f01 68
    0x100401c0140f00c1855440c8021004400c00045080021810702c5000e14040c50074110700000d400300d0803007031103401d0310390b49a40440f50044002031501d03600545902240c00f140403d003451000705803440c040c02910207841400e001480703280d106840f441c140c1456141c0c840d055010b2402c0041503070310703041d10001000c5c01d01009117100c4001129484104c40c07009059000f044550300085900b154000c0780c1c140a88036680c000505145513031801400c0c40c00310035001c286200c00710400280d018200e040d1040120043c00c0420407207079103800598607000d860120340d80c15001000940e203403c0540c64010305440c02841c0000310501d0035a910b040c01000305411170051b0340140304004c2001024042e101000c1400c2d8040d200003481c00000c20765034050242e8603000d03c440c60f00c119540c2d0b0036801c91550f00e000010f0001c50603c15101030040c0c960107070141901c03036140454020a200000e81080460600600c080c8040011141012a101d460203401221070920030408180864401c0000d90301445c10200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 674109469 1250 674108219 674108221
    0xd11090112110306011203050c07180f1109010203091306080607081801090b060d030509100908120708040e0a1e0b010f110312180d02031804140606180612 68
    0x906000011020320300503c43d0f0310190040c44804032550070080190780c0341c01e056481301880a00d4506201242e00007105070071400404407184a81500801d1480d00c03507640400041d20249441c098600c0780850442c0940e2080003080503500703082e442ca0f11480014200082e103d078942040a05020042c4c0c2c58100059030310044c0660307402600700c0240b002c1001c1000304141c4810703940c1e040700e6003c0100b100e072085010744602c07014540500111078404034024200c440e81c6410303203800b51200f480b03405810154411004101e02d0f45001004840c1d12640002c05182050701d0503113003400c0a00000d1003000e0403511901c44149082010721450184801444041841c40301007000604032460150b082040003400a07907080201d00100442c0d601c6074059071420b00380d942d580703650400e22108180003041da00c1485240b1841540c084080c19582c0d09460f802548000103500b0030090f01c401180c00d190408050b0082035651411038010001c2c140c4d40048d406880c04410b0010b0310a42146410310078442d1044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 674110719 1250 674109469 674109473
    0x30a030207290a18090e01060501030f02130608150a030f05060f0702030403080708090405040c090f02252303030a060e06030c0405040224040302040b030a08031b07060c1205070207060c020d11090112 87
    0xc09181c51303003110f10741c0450500491a0410003b2481c610880040c03000c00008102c804a40c4400b8006a180140003003810650303c0c60310382000080814161018090707a404a8040701fa0094580c0c01419503074011810541035858603c183d40c4a0235044807251400c110300485602d4500800b0f01c20f034060503070015a06e10340b854580c142c80b0b001c030310034800710b1040103011654000101030030315038119541c03641c03440e5107030349409041020000d813500071411061100500d0080004011403184152120500196075219010700c800350042d44c0b00340d1300d0707040450754811904195025503400350000700003140400300c8941c0040c1d14420000c50940040d0300190a00641c1018080c40f0140d90054004101404043d142e10102e4040500504148058415070701e0140301c030401500c500b00c0d0010f40400902c0900760000d0302c13440007082c0044405013808002a080c60020078814104c640d180c803103818060150307081210300110303604102c4100305140f448d541261580038510b03000c5d000814403402403400c54 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 674111969 1250 674110719 674110721
    0x12060f091d010507210f05250905060f1e0a02030d05060a050d12020106031b030201080601210e030d0f060e22020d11030a030207290a18090e0106050103 67
    0x6000c1800710303810b0009100c1c955920298086420081c2c10f01044028112030490307002c2c1107039460310109a41804240201400220254100c00c202042603000407140b10805464680b02d070310613240e200205220316038904000780002d0010401c441c4000c00c5c41d04038218100c00c0c0c1d4002d00442c0b801070744080b07006003850000d44602a04444212990401036240c076001810054032844001d04100145448092a80c000d403c10405540d21680c0820b955615038044000340025210590000d061040894030301c0d4010500b02c0507141c041e02c4007581d480e842115460107490034928480b07252004118140344004180f04a04002544100c0402e6903403800c5810004103601900382c6400000381c400c0003282c14055980c0200403035040d0b550400e51a5030f800c02040780d040c0713440201e4050085848142c10140e011030071105485580701d132188040e4841440781c103901c0b902070f0701121512003000900da099020b00c0c550100c0090001203038880716202d000c440c003a941d2508004981d40e4440030184019030705 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 674113219 1250 674111969 674112011
    0x60c0a2f060709081908210f060f060307022505190801060602070b09010e0a1805010302011d090109150f06080a0b01030b0d060b060c07030302030408060f130312060f09 74
    0x200000d041c2c41129000148030880b4105c0d000313294180003c0c0c1001540e88440d10b01240c2541c1d000e2100c41440c1014040c412000102d810034400c0024540c00c04180c40c10b101602d014042a41c01400c20050901c003488180f03c46011105954202410000d1341c3e0742d400415032801c1e0140003d40120b10310b0001c0507400d480c040e80280081d5080707900d09010150180702621076a0009203400e881c074110200c0402c2d6503a0190b040b03802901d03001c0210741d501c0c1240e9000507040b40d01c00e82e100700c0701703050b03500400599180b282d00d1958000441001001306075020340004c04510f0059140d8030445175030704e82a070781e90250b6900c9400814400c0702082400009803186022000003070a0034020102c4440004000c416440001050542e444030044580d446210544100903000c000305d40c1d0154480c20003039076a82051180c0c061501c5800000b805850001a031701c0e009a0a2401c0d50261901c242e809407801440f0760b509080d40c9590fa180081c01800c103000312802480c3d851000038806060b80c0e4500c91001d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 674114469 1250 674113219 674113229
    0xa06140105180703020a051e190905011709010b030a0b01030501051513021b0706050d05061203120901020f0d0b01080601111207060906090c0611060c0a2f060709 71
    0x245103400c030b914089244940542c0602a0310b001070b9103113103950041d05c80e406440c2240b000b030702a442c111020f504040000b0014811406a1030344000361075001121420030710701800c0d0024803044000100400302090860700020000d0010403c2040c0c3e1011902d0004c520005450560600c030042080c0720082c42070b0703a008103441c0142982c0c8012240892041510b003400d2900301a800100408240e255203100006a1185025242043e0780c907076004055070000f0520702581d521348004a1002d00d4050b84030039400c50b41d60042c0d4200040040f42c00c940030001003140566540801030030031030f03035031b040d0040018080304000007070b0a494040c001400b07810001d000505104440d605c10310365200c00034009910010103c0c0b8140e40c0d001130700d00306010304500130000301000d041403000820841209483e0040d100e00d544ca079400190607001e096510801034030002410f0404012031034036144100c51903129030507540d0407900b40f54022002c03c9202c40708a26030882c0b6030020414002c0096010344081c000700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 674115719 1250 674114469 674114479
    0xd05040b0f010e06030a0b0a1b0503070908030705070306020901090e1f14030606090702030d11041e060e01050703140c100506030c0a1809081204050d090e040308090f0a06140105 78
    0x80313480c0b804a03607104000c070700140c11400781d140001c0c640040d94010204040180045104907003000c40701038007980099800502192680b40d0100c0c54205c00016561160b4000c8002c01c4081d1070b5031101c000961107452650b0400000d91400300700754054000c000d000d008021080f230031841c40d0500460b040403140d0080425981c01c076010a0541d0f5001a8841e0031003801c0f9540c1c8010703120508241e141d84600301703c900f04d0505082101b052549604003504c1240c1d080351696241020029406001582e00e0003a10081500c007010075056501c60806003080c0d601c6401c0051410440c019607410607003080081960550150042030400345c10360149a4002101ba0020190051144001443e00341c850107015801039074000350001d440300c540c00450310715030884d09080da0349854030761f090180d400c1290141d40a120301c8403c80d11440c0300301c0c0c5170011a130f001803007034184d44c82d160340c100c410203c060802c0c80c01d0b1040c1c0e80c100407204014440501004d2061000040d0301c00c10001c072441000c0142e009a20807 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 674116969 1250 674115719 674115721
    0x1415040501050d0b16030209030a0302010902180405030403060e1603060209100e0f0d02040f0c200a0b0f2802091c020a1a070b010f051801060509150d05040b0f010e 72
    0x7540580c10940141100a00c9181c080500d0f10486c0240100d040ca1035042c8114021501415010f620050655000b076030340c1c0b841e1601c04001c00c529401e00f59401411517101300000c00c0480c4482d8400b21181090006a84520819940c2d583c10315100b504252840b6900003a030965624080d14032040a0f425804d00d0450701e60b079800080d03000700320f448a460151a044410204640d41c940c810314003d0315030601000b5651004000912106412509030b4000220020018248000042c1c040200b03900c24040c02d11540c6a0002028030040608204000301001c07105c02180000c00e00e548140165209006032540360328810000344c0c0000d80c50f003800108110700541c002d602c80c4140c5005680140b0004406801018003a21140c4100000a00442c20640000c03806103100f413281030866004031400c500308030502c00c21144d8440e00b8410f2401042d010000700705c15061140075a40c8a0f9071181696040050240e50101901c0c01101c044070b110411030204404042210700306030141189200013001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 674118219 1250 674116969 674116973
    0xe010e092109010c0f0602030903040e0705090303030103030f052b11120f0c0f0c0114090613140f0709060303091e06050304080d0e0609071403100f1415040501050d 72
    0x420710484001e43d0400100c010400c1c28000400c04100c003e6501c07050440d920b18021200503260b0300140034841a9440c0d03000400c03942441032082e22400000100910b107035910b542e0302580c480301e021041c40309101e810b1200c08000c401000c00701d070f50108005200c0c120000c14204100c212001c1c0f0250039040241400700b1807600360920483c65200a0140c0d0307040c1c9546424003a01c1080c00342081010070340c01d000920107601401034003c4249000e1a051000300c0d84c8a040e14a912998210741c000c1502040034464008903800e00254649620200251a140305900100c14101022600604000c0d03490b04005c00405500442220041980c5000400111251075049112429a21a000030401d0220104090080c01d90450b8100301c1e03c04c108020000d8040a4252118012200001c880c0a0401c000801c600048001c0c1c24040d4010003030580c075210514048010a580080d0315800c0e0350310746039500d01c018265403c80c01000088588480c4002080030801030380c8050300160b0249000d2000000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 674119469 1250 674118219 674118283
    0xb01050c10050a0b03031b010c0c08090f010e060d05060f0a0821161b0b0c030d1a0a06080a0c030b060a0e011101061806050306040b0c070303060e010e09 67
    0x907541408120104858a403580e0a0000e814810801607040c040000c06041c2618500c161141801d07080002740a00c080c4601c2c160b440d445480d6024000101c00c110718030780c0c1d142887d0803080d4850305060509198041c803010540c80e0b040054005100c0365920180502403924640311030003d00304071401c41c3c5c49810b10320041e0b1515002e1150183c081010108514541c00c244252203020380c000500400c002103d0600e916018404c1c900c0f03d40340d155210002c1407188010341200c0381c64503101c00540c030b01084409050010001c0d83c01d1030900c14609075180c440e41e50340406000040c0140e03038a60080b410050101c40c12210100f015005151604910100c2500c8460581d040100d00d410842642c2c0040310060340d00c104480d80240780e41d4030f8103402060450102e034200480f412144d104210135926002810750740c10081d20040d10300010b00c400920110202002030806612902e00481c680d940c0342e04a010307015081e00000360700001c0108010b01d1400400c4035444002c404d0050895101e20003c241b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 674120719 1250 674119469 674119483
    0x909110405012021070506040b060906100503011406040302040608010c141e030601020f300913020309030412030c02040509190b07030e03030c220f0e0a0e0609100b01050c 75
    0x3d2228800504c4600c00030341c095610894101c001e4881500c0c040c90021003000040b902c1a102c0d07884c0030080b401c40e00b8848025802d208460b115146980d0812044801c04401907680d2a032200c400c201c00f00c0140c03203038001e40008144240001c1590b08070240058414001d202c1c0f80388103c2c030240200c3e074684505440a410550b01e400c0301d00d5498684900407424002d240304010854494411002d040601c4650390b0710301c96070490303925480300c1c2c0e05681c01c108910526880304c4d882795101410040441d901d80c000d5811801c1082180e2078141e941410030300034141a8000c2d408103102c21610000d5080c1802000c1c0d020f00340e9809070421420f052000042c400088501801e20204030700003030702031800b96103c2c0c181001038008407a00e9251075101c2e105542d2021414083e03045041c0307840020501029418025202e41e880301c5800541000060003e0300c1d0010070910703c083d10381280340f42c40b0400b44450350098840b140540000941241340070140d40f824100300f41004402c20203001c501001240710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 674121969 1250 674120719 674120743
    0x1409090309040b0105070501051e0903070c0e0a20043f0510060311100813060903020c1c050c09090a0f020a0e100608060108070e06030709091104050120 67
    0x5494401c2400417581409090402843d41d8605420b10002d01605a00420703079100010041400c0c3e52070a12158490240b401e000300411070300f440900102c46405021540a00080400202c4400c48441c000c109084450020508800043c09200d50b01d9103170180500301c00d44208201c03c002c00c0f05042c01034204003031740c42d010002c54100000c040217810b211004441861410070320059440b401c0101e0042c840d008481d10503181c208401e2005800380305194422201d5610140c254000c9864400282141100880450103250031700201030749c418644064500740781d4400038102d000c038a40b00e440d040e0307100d688a210300d88000c100940c40310002412600594007080441d085a039501c0454480c400c1908907054848a8404022104041c08a124104d40103990381100a88800d00103507070b0344d5410303102c410000d140f00c40750054a0408100540d0030408034076200e80944d94031000d500442d405004c03803940d07000c00010200621b60313000b000f019407030202c0c2d03c502c454280b403c01d110380e580d00c5440c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 674123219 1250 674121969 674121971
    0x20607020c0607080d110a03020d0b04090c030201080a230603210405130b0402071a1503030405040921180803030c04090c0908030f04090e0c0d0b09010f02070507140909030904 77
    0x482a141c0705e0903049415101c841558040d111003942201030041c1d006586609419882c3c00b00d05e050350720302805072121b540d03040340d40c3c070740741d603040d90011245940000d01c0c0903092a05c0e190010b82c020015a4642c20342c03418a0740d14205400d080d020035040c03c0d980045103115000c09004004103030406012982240c000321154503a80c6c0720000d410015046c18070b072496101c2c0c030100b0300303409100306038a403401d162100c105589110382d0743c0e203001c01c0c0e010050106a13803d070b03100380700902c0301c2d043c581c0c007418499000d0540d90003842c07220100010361020f400740080025800780e081c01b06070307240c4030413000180042802a5003540741600d800c8145009500c60f0a64198407102c49010880c010302c984400380000a080d2507940394080e0240c0c0c030700e030b0244c80380c05180c2d86070034100d03a0015008207a411000780c0081000c1d100f402c058071401c030107030000b0b070075880705540c1e4240300003000c4042d00c0180090b030b00c00c501508826180c00c0380029100c142c175079881d00070700784c1008001e000c41c008011900c80d0b007400c0310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 674124469 1250 674123219 674123227
    0xc06020f1e1e10180c030f020609030f1509011a040f02071b03020a0f080307121124060a03030c060e0a08040815060102031602011103070b1006020607020c060708 71
    0xc03075103000150625041a00e003140c0d14424070b9600402c04031000140c6a80900940780c3c4003401c44600d101860004e4800083d041091000030038203140a515240014101070030078030180002030800303034441c45883c620b038014440203c500700019826a1300c80c800c14000c02c0313012a00d070000e00c900c402c02040184215070f030703441d110f08244907035054035106500049289a514607014901c50b13164071a001c141e114010a4100003100d50b280c100e50000d540000c009503080000c80c0e40c2d480d600300d41c901d4025080c0403103c070711601500c40402250304e042207800f4800f80541402400e240c2e501c180a000301c0d006940c0ea400600101303401c141c1403004a0b6111500050300700d8000c0e070030380c00e001508100412440000900166010f000240c00c00b4080242d00c10040e6600d0f1400107980d20300c03510b04000302a1a41d40d5201000d9030060013000040954003003038910700007040d40d134490079480803588036403c24030b00401404843d50410aa9901031620700040000701443e00001d0410f0080d444005c00c1940700103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 674125719 1250 674124469 674124523
    0x1c0206070602041512060311060c07181a090103120f0212130302010e09010f051e0607050109210207210c080c10030506130e0a1506030c06020f 63
    0x90212006660410303411900d640d01d440380c081c0380d14008a6400d0010f640d040400b100d054052103134408495000c445140d4240e0a002480983d0f000291001003038060140d0001e01840b003030f032160305452035000c4000391030b01c0502680e160b900c2c061855035000e816968014000100005545643c07051181030070352072448d01d150200d15011607100f04902103003000c51819070400c454a21039054a100b600e410200c04056014001641024494407e441c150300c0402c00c002c0c10a031111100064a030001014040c480c0b1000c07800e15400200e0848090391b49048050500c4403e0020000110050000940194801c00000e641d07a656001301c42d100aa0300c240036141640202c00402a1640320b0036040d042940d6000554613043e503a014a4001e4400b0080381030240e1103445820321494000b0094500d03062105580b600601a40503020784a00c103226601000c03540c00c08a0080c0c840f1401404103042e4203504d081d10040d0115030148042d90300c81d08201c80e1425011410b428010a002c1140124894007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 674126969 1250 674125719 674125729
    0x2007030b0606032d01032a0303030c0311070b0402030111040b09041503020310142a03090a150507030c110604061a060d020c190201051c0908040b030906151c02 70
    0x8010820004c082110b980c0c828600c0102e801d41264040c0d604060015812401d401c5000020520700140541000003840040d0081e440100316640a00d4001140d6200301d141c290241d200c4a070031340d02c1000d6002007204618090085644c0214030500e581d00303140c6006540b4001e402000101c03407043d503c0f8042c05e0001d0345002d0160000f507030010100c980440c0034209520003842500715410421905000003a9186640310014010b0065580001164030001c2c1811a40380c001528054440c001c2100d02800b041084003072110171854118000360b2820005005001c58144030543c005020f85510b82000031a00401c035240d11903048440891018114118180c07030007007031700e0070356841b200c00700300030580201e941d000d00740c02e2110200300c5205440b10031404803100c04440000f40010700401104031002d00d02e80c020540f40152240214154245544c0c04500c0d0700603810250f042000401000048101000411340100d5840c0755030451044d0407000c214114015010443c40f8641d140c1c8020031034640c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 674128219 1250 674126969 674127001
    0x8040b0619060309050c01140703030e1507053105090a0b121b09010308040b0f090310020306010f1806050a020c03150103020310140a0b0f0d032007030b060603 70
    0x120000078814151140c102400510801a040d6220300c1000641c20711940201c40d000c44503a00b03280300320708110389607800320043c080907011905c2c28014030f080303202002d4445001d14015100303500c800d07031100007011031466200f141503078040103029400301681d51410401015415280241c0d030f8a1741c155500141103018140402d0805e400c900074008004629002080c500c0300342e0710722900144400813403810804210300a00011380850f00400c41041070101c0c884c020501e9042d56802c150925400d2300010b0f080c695516081c865031a000003c06c201582d20148940c2030405609182409602c2101c041007801c2c02070080d07005000c4006150304156000700900e480c1440300030102c501d1880c0d4038480c00e46281c1c0a1004a01070310030780034141c01c2c01c105070080040b0120000c610003003075a035000130700f03028241d181c400b05d8000e031811a84d03225075250b5400307000406010340c843c1030405000d03558440300a121000000310b0f80d04150b409100080c1e000a26a8005a003240c070281c89445040700610407140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 674129469 1250 674128219 674128249
    0x1302040f0b220308041d0405061519030c0311030604030e041e021c0605010203190806010903060f050106080c09030c04021308031303120519080c0c19120c020108040b06 74
    0xd400000f042102040040091341c1c545503103007840700001c5804034081803003510000c01542060000030901c0d0300c1c86110721a80c0c1d00080601444d00349420f23645004c4a60764005865403007130032105100340860b098403503003004820340041400b40b070140c80c000c2c40302101010b218841e0741c40d0035030950344040e80b00005100c080742c2c0c0070856480ca80204d003030059001e00c81003205c4c81410080c0c001941e43c00403054804c2c01d20141544689e4109585040b900a08010031413410b1203540080400442c1051041501d400b20455000800c2d5040a102400f040c200070f22201d803140f1704001c40410f0b07031808698001c4034a03050350301680362902090405404a85504181b880d0300c40410110452a9103852000480740203d1000c00d0911035038200b15440c1c440c0d0721f075142d2050035410100c01d00e0741c89070724101e600c58602078401d41480e48010125080060785500328510301403d241c00ca00740a05035810009141e61814802c81d20320140d030019082c01c50040015105942c0b400019241d62035559106915031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 674130719 1250 674129469 674129527
    0x702040e0705060a1d04090b04080d091406070e10050403080315030a0305220f060e010c0b090f06010e04051e1207080a110a0302071202040e0d020303061302040f0b 72
    0x2000b070110017002c4003a0300c00a29424540d071141e00355141003522031007508070780081412070341d583c1d151221484c030380c000d0061240d1a65104003080100300b0114141c004942c03081c01030705290401410040180110958162160307030303200c0100c1162604241220b040b20390041ca0342e034981e03407441801d24452010b0405242c240c02804424801c1644c003400420005007941c07800f0b022582e084d0303460000c01e003540c014040d48081d5000c05014890281d00000056001494140701c04082a40c07160032a1b50203444191080d0301c100c003a01e01c040c2043c820349015005440c000c20700c2d4541174944079503c207400d0001011120040401084501e0305001809010030724140d800d0f0b03560b0355031414443c99400401039400203001c080e210f000ea10300c04158800b280d0741590082160305e00b000742d0f0301581c140402e8100d0744166580a102d5a461050100464188054001e0360300d0b4540f02c024062030302a8140329a003800e01c10001032002d06120300010341a5003052031030645030788050f501c510f0b01000b00f4000341410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 674131969 1250 674130719 674130727
    0x15032904060308030a0c09061d0111010902151b06090703020d030908070602070501081e0610030920090907060c03080a0f24060507030203031b070b090102030610080402060702040e070506 82
    0x40c0702034101b54003440300c55480c20181d5541e4030040316000040742c50b11080ca0003502001c0c0c2c0d03541c0302c1c40d440180310401c0e000024210096500080c9961050440514224008150160b0401318554400100381d48080500f07040c3c60126001c41c0c4581203030100034880c90104048900785445100c0e14406840c0003021141c01c81d84a040c0650348075651701c50a0f00188aa00010301e4400d440c4500b94990103600c02c1001c0b0036100c000822800c088400e1000080654401800c00482c40712a06401402d000d0200c4400b040c11030020700c10f90401c02000e41250303500600080014685c080c0c1d20700c55694140c50141032a4807041c018801414442a540050a080c20109401703d4444031003445411895070101d481d00340c0c1c501c07007521701d40203095010b00543c10603c00664007040348444400c0c3c858150308040e103070000c00d584082c1451001d84021010707a5010081140f6400d1525a00c0c8002e81b182c204001c85161582c0041c03400d2083c2d503002406941c40d00000e41c040c1f00100034003800703000d00805281d12 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 674133219 1250 674131969 674131981
    0x11042912040611090603071d0415030507050405060916030b0a03050c0a08060c1b0a050f0d1b1e0212060c0703020709020306060403020616080703091503290406030803 73
    0x9064001d4400b695034502d8402c03a03120038003540d002c454540c84050481811580c03030813010f9a20024846c01c000031445900361400e059580d910407205c034030b4554400c00e040c007411420400e280c840d85400c440d01451400090021660360490303400c1e8040103040c5c0b08004511044800c60252240c611016000001080d020041020124828680c82001e5132035400050f030b909901550345106447d8014102401c02c00508603138502e0740c020f4100800c050854149840c00e03924a8030708113085503034090300e0b000280c145620036844803a00d02c000208440360424030b05181c481404441c2c1040d00125401c4d0080c803488115240c003014000f151480d481503507410300e007502829039540d100100843c0180921600419060820f100703481c081d501c09000f00d0b04150071a402d03c0403c1d800310010818080c420107401002459060040a40d00e1081c0d80307000529143c00c0401d0000c1222080401c145410121168036100b00010402442c06103400100418031400000c10b00401803030700081c0800700d000081101d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 674134469 1250 674133219 674133247
    0x41412031c020301142b0f0c08030a09090608060604020a0314070201020c1006080705010c031e0e0a0524030c04180c0219030e010f121e0b0301110429 66
    0x104172205c100648000d0005002042060b0701c4062481c059442c10b54501090201e0860700907407413521801d45d40c2409102c2d42c41d0303c0384000d00c541c020040c5074000584c2c3d00c0c01903403201c188001400000d905104c554100780025032181d030010008c078082c40d40412021525482900180000311002c641c0c1c02d240d06200c0e0009001c3d5110741f901051074403864101c1c1f1204002e5120b004211840c110180c82401d09000044540007107120056080203034044842000400312030341c00318003950395103031651600310180620a84007802d41c8141e2050f8580301c503e1040d8000b480c60035070040c1510003a549d80359a80b40c3c440038140115003001d4040c0125a9104c00d017041c440d80151172203400c503021103410406100c0214191303003a5400080010b80b075038800c174219501441c0b1450310b403c0c8504004d0050306501c20080d0440c0d0345404d20141c0c22200445001c0d44000d40c0c0b0900864000c254000d20443c500310000903510710451260011224040403d602d41d5140865040d80c5510140c188558610300c01d13030014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 674135719 1250 674134469 674134471
    0x1050d180201082206050a0b0909010509100e0c04050702031c020304152007020621040c060807021e010e150a060b070f0201030b0a0305030a09030b0606041412031c0203 74
    0x280440c80c440d020032856085076403009184135619111200074007217640c451014180160842605540300c2d002c840e0280d6500f41042e105500c0300700002224501115018585079808171143c6041c0e140c101c2038940050007203a0408400c0d0180c82c086540e4440b0b0104924601c5042410606455091001c0311458941e400541c0254010101040d10004040e02141102c010b0151200c00031110228007082030040b10141020500041140d4144501107080302c0440c4500c09a1107505041c1408010411804a0006024210314640310030285000c1c00c02039070702e50010004802000b501c00d11030319200303403d400c41c10301d007407581095480e14441d182410034000d9094544203011410f000780807071551045402d89106a400404400c0040c8864006400403e091107107290444003920000c008140204020034a040c09955580c80640c03860400c00107211300941554481e1004200420001c2000c0902c0d040c61300c81103450140e2280154081803843c4100210710380d2943c20098503c60000546e4065 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 674136969 1250 674135719 674135723
    0x190e12010c12060b130510030b040609020d0f15120c030816210827070803180a030b01060311130902070b0603060402180a0212040510060b03010308041401050d18 71
    0xf8800c0035141d5404030741c1030103001d0040701030070b60202e0200701074035016030725548030b0045080000b003142124010400380c90960704500446900004c010040808610402030312584000c1c04000091602640491058072482811401c100080510040c00403062802c0000d507030042c038040e641c005910715511715520529041d54640049224080c05c045841c192810b8008903a60307020340c1da581c00c11000d82c00445c0e0814090760500128409201440030800e100c081c121480045465619031920f034901c80100305845401507104600400005154001d128151001c03400d010400010949135960300c2c0c010a528000300c1c0e044c500c4000740711201ca50050402c90301035a6803071101d540d108241586c0b05010746000703400180c0d000c480045000d2103215141c00c0070800d40050700d8041c2e418991000d03202e09541c156110382100d001d803030b940e903800d01c600c1008112a41d0414199031664840050074061031060343c03410400501c08041581c41a01107c21400710844100030110071501c4000900c4102e01003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 674138219 1250 674136969 674136971
    0x6070b1602030307020601050d03110d020604061a06030c07050a0b0c0316091202040e07080d051c05012303070e0a050f0106030e070b07110402040803030a050c190e12010c12 76
    0x140c06000d4400710031a0f208141304d40081c20564a80400e0042e2481d0003002a410000701100250001d1702c2400343c030200b44450780c0100310b1170030141442012580140846844522070b07080002322a110041500c0e401180014125240c0202d410118240102e6800c0201340088000821030308240f0000a14005d10440b1000c19039040c80400689031007a8600034005078240c0404a14014640341d00130586440001d401d40d4421071351a0486440c12100d0013080010401c0440c0102c00c0209690712165080c408640c1170009514064400d040d81c2100d41101a040a481007851610348040002400814214a0315801850903c80640091109480303100b0252210000010900d11074012040d00c072041c040941005841d10300940780b1980914000ca9015100e2125001265111300c09400284039101c05540d60f80b418414100c11074074001d16050b2010001e1000500240406002801c0c42516042100012464070005510003107180780403500345d8284115045600d42c03050034441645003640b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 674139469 1250 674138219 674138251
    0x1d0f03030711030405150c2a040b030c010507150b1809060a200a11030f0702031204122d050c12071508270d26150f06070b 54
    0x20b809a1a4401da1169a500081c100d00503208511148000d014101060040744c0420b15040c14440d840803505e10b015042420242c100c44040c2028050f0400072078045010344608400500080c043e406072030002390500120240700001401691b101102c8803000038001da000c1010404104c0c4d0f03000c4101c9400c0c180b0b015810105044030303030740d0051000a00301e0b280c0ca45292001e00c4c01d03421064010407110020001585440811040c051004149206992200a03070300d01c0c0e00d00515242c50041201c464841c60104410001d58000704121150590f01103001c040c03104441e1107143c0c12400c4000d4079905107414000440c20403e0002b88100c00700d0342074400001c44030402c802c06032212010310600250340488103078284001d204580c11948100d00312030b14040c541244905008280061034400004c0c1c0c440040000c103142c2103a0b0880d468200318400c8080741041c40315400418201a00c040560080d40c400c08040744d640071030714501e00c4005420942c4070401404c0c4000910000d480e002c2168a0840b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 674140719 1250 674139469 674139497
    0x9100e1305150a061d01030b2d07020f0d120c0c0b13141f0e010e0601080a0c1202031005150411070c0b27010e040c0512011401121d0f030307 62
    0x7681c00707601d05032001178403081a0300e9a128601003030b01c000c001007400019503000b01c5002c140c2d041c00c00181844005078006a181064010740351840c86d800140041d0300401c96001d402e907010780490700c0c40c02d04c6180481c45018000064401290481e801041c21681c41c0400202c50000c055015500c1c1c00341d0307110740e840241a400c241d19080760a102007842c070b1816100419100b0160025141c289141000003040b1010b1120340d420f10400ba0080c00f03080d00607a10304c10074007440e0301d00710003e0710351711340030350030707005043d40001d03583d8410020341c0d000f035501c0e200007440207000000c0000b100710010300305114a4401ea40f0740c0081e030340104000c030740f03040c1200004606000200c06841c0c2811340d07100c50703a00340e26455611003a07000c081c410f01c2c0d040100d0801101110f495500070718803080120740ba1a615081c1010300f82800c600141c104c0500e0511500c024807107070b80e100c00741015400795001c0010749603400345004025141c0320b4011061a1045079104400070a001000b10310942c002e54950100504034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 674141969 1250 674140719 674140739
    0x20705120901091412010204150906020d05030609041511090909160509041104090309090b0118060513091815090b04020f181f0509100e1305150a06 65
    0x1015485000501028044c8929203025510a141c00801012450081c01900099082e644240c05c01011048460b0440c083c0c5c64119203403034007411103030028250000100310010110f00005203803e11030100e0401240a012143d11000440318a0580c10301400300e00c006c50818039404924030380d00034007140000801c0d8580101f05c081c0c10100119000f0b0310b02d0314080c2002480c0381c002d0400d40340300302c000e0b9880380c4a542c0d510550180754425101e501c001450301c1c0084080703c000c940300a05000e90108801000c2c206140c8480030740b0000c4c00c0c40d40c0c9a60300400450340f0300c903050f04050040c40c500043d00c84100004495035100da480342c2031681080900240c824240d59880e50010722a1a078000410014a08403080c030458580160504444034600c0a4003849104c064403010301030040450f590b60340030103021202c40584820b40e81c1c85a0f03424054042280e10f4001c2c49980358160141c070105102041c040128103aaa40000032915500001e80404a002d40144e610300321080c42e106000850b41a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 674143219 1250 674141969 674141977
    0x30301060210062402070b0a0e1008090c01111905031206010216031203020f1803010b01050702031902010c02030604030801090c1419140403050f0f0f0d26090102070512 74
    0xb0801130744080c0d40d0342180e2169000220b8040c42c0540c001e0300e06c0411240341c0f04001e80b504040a540d80c60704000207009028001c41102001000c000c1030308100601d4000004064144030000c2c0307012503106008200050030300079804501c80212608105031003d01c01c00001504040c0603221810f505d07600c8490040e0f0303661204034030705401080110f800b0800f04031005000040707490350342009458429940000c01d0958490068201d01d1445100d00346454102486105c180301d20038240f40c0c0c40e1490070380001e41d1f650001d42c1943d610900c1084e0032021644140300249095038064129003a40c1043d1a020300030034030902a00340742520f042c0d82400f120384680e481a900768031001d401c2d031501039a8044d9100c00c504040e1039a00b40481140c0b01c06c0c410300140001e00007140910094110b40c0d492840e104e05142c95140415104e9101d44c903c000301c944045181d0500311504d0412048007450342d18801003180303602065111140c4032604000c0c04c044103400824095200d401a551080b074020785164243c0070b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 674144469 1250 674143219 674143229
    0x1b061e01060c030509040906020c06010905100308070c03050d1e08072703021201090302010f050c0406080702010b030105011203080a0e03030a110c1207020931080c010e03030106021006 81
    0x50840010462240501c440d03244841c040d292003490818000b01103803d40d0901c180440b81240e00281c50038544800b48081800344c02d032610144481e0030564140307500b102003800080c1c804040080c1c5c800c10880c900c00c0d050003c50f0302000390f61151240150141c1154058224440040c400d5004c141c17090b8030401c8024814903075511407103548402c540d00f080074604200008580d203140f00070080056550030b0601c49041c42c806001144440c554900282900c115030184511a82040b041c007800c42145030540303082d00c40c24900001c142e176070070300e04a0240039a400e034680c0551805001141c61001c0c0d800380342c0c0b114003a4544181e00d80f509207000c030459949444501c001d800a0000c03c0c0012481d800c00f0034142c028100da141001344104c007507414000300840407038004d400000c01e83d0031414880b4220790b0203405c2c240c008698990140d4441400344000b80c810100c01c0c0f808080f1420130010800366913946a01000803c800c0e000030040d1a40c0303900c00e01035a000b52040200a114100c44c074016582910 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 674145719 1250 674144469 674144521
    0x7060c080901110f0105011a13030b0702070b0d150e071d0d0c08030a020c12120d02040909060f18021e18070c030906031802010e12031b06 61
    0x4246440d000340903000051054108010800621440781c0304010490700000341d20b000143e15403504404d40c0d90b0901110580c00c1e480003d202c00041c640c040f40170601165000245c03181c00750b5404100300d0801145401110501801255800d1040b111348d02c4030014101c4610510030b55500c591003101030460403541e4000290810404601d10305182880a0321034a0242510503602e0302ca07600c10481405503040f1000d264004901484001d50411101541c0401070300d06400301c50312201c3d15600c7d800c4500c7c2d03480c020140000c0040c1c04041a07812a001000048000c100f08134a40c51f0500103846044507089115060440701d000104441c10803154090340100300d20300c07503c00d0044607802c074601b81903c168002c07244a1180c2c14101d40302c42c9207101340b40c03d54440005c902c41d0f1074094082038158128008151400b592281c07010442c00e24240303180e409007019a010401a800a283c0b110b00f450766040f2800701140d187d90141059000d0403104031104140d078116914000c8031000040e0000162141ea = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 674146969 1250 674145719 674145737
    0x14010804240e0f01021914180609040f050703050a1b030504060209040507020f0708151906180b0411090a03020d111e090a050903041406040806180f0706 67
    0x2404011880064040303610a0200d00c420542c000e6600b4400310900076216071350000303281ea405180010216100d440c41d418400300b600b45142c07940302c0d607010b28010016005d0b541c00000e90306988141c15038800d00350040c0184080000c61068070301809050301d0400c007080c2001c010641304441405009100344000d00607440e41c09400c1c44c100d025110140007610216400c01419030103881d507014061007040d65030000c00a480802e82441e103012103541c00203030240c0080790000c00d0b641025640713135002441078040c040c040398000d001400074805079000c004016a00d8400441001240e0051440f80e14102c07010031800d68180c01002c0c076841244242548081c241e981440180b80c8016411400780c02140c2401c41d0108030000300700300303011103055424281c6096015042d075150812400d0b0f13000141604c24403081c2014500103a5034044d41c083c0d0090800460301ca10b643d5120300040d90003c0400600711001401c0110910100d000c0b003030005051406402040c034101c4000141c0130044524030303981c965030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 674148219 1250 674146969 674147003
    0xf0703080906070305041205031905090f040908160302010e0706030204050d0222020d05040204051f0b030a020c16060318050c0613081c030b04090201020303040b100e1014010804 78
    0x1140d0010724100c084c4074062101060401f80e01545502c058800d9000315600c69a213221881c0402d64070b01e0200c10002e082000000a0311107407400340350000e0541d00440c241480340b0306681c1601440b5030b480c0c0c44054404a1b0824558150000352a0804031800d41e1546c6481d560128144d00c260b024050308a13181018500043c20801600711010001e40740c40342c11000004099803d903032010319010f01560f180d5043c0000d502d003a100d50ba4201007038541d1648010501600c1809101003803007661029480440000c40304015a01142c500c0e5581b501900e07030880c08407246403a1844980a848002454800640150500f030104922010b400c0401800c500c00710304200881e550003420072107450f2449400020782110104078000941c01c50348804000b16840380f400408032418542d1b8988070b14280003106000d43d80110440e6042600702000c505203548080c04014804219480410000303240ca007000030809801c001e11050b01c1640304800200724030030004441c01001075902801e5a4402c40e04629 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 674149469 1250 674148219 674148229
    0x102031e03100b040b0304050d09080d08190f3c0b15040e0403140a0903020103090f3509010f0c330f0e1216230f07030809 54
    0x80d201a145000082481d1a1083c400031a0029409035003582c00c08010300042200501c0b809402081c5894100141450300c4489a42c0351801203840081c0301140000c6543c0c295100009203c01d520a8000d20000070160750003001441210f600004840e8804203680c01c4007050959403521140051000000c0100c0440707800082c0a418842980400300e003000c0000503c2c2c00c0050002444000e03008009440c0c0380c2805440c643c2096046454a0700400841604641000f000c02c2070701d03020301e40080c84090707615040007515480a0302030146080307403110550010000c851110080300d40d42d10320030b42000004c0410031078080e8030f0a050114880d1220181c2c818491222501c51501540849407968040c0303001d41b0503d0789000b0103103402400d5807080105000203000310421b41080003810031602080d07c0c081c60b111942c014803807004500018600848110481007511683d0b0080c4034050750a1000d03200301410024000d440010b401a0328000350800000701d28401141c1e00855018540040309082003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 674150719 1250 674149469 674149471
    0xc09031510230f03010b010909021303051009140a02010903020d03021c0509010e0a0e0619240f080621070e1006030b1017060f131a0102031e03 63
    0x20302004030101d800107030340d5080303000d080d601c0c00700c001800070848075207040c440d140518201c2d06002e40c0c100821443c060340e0000000045078125400107864141ea441d001b0955601070b40040c00034450411540c42c00c121603400303421024802c0c00c00e82444104100e8503503c60714409806800300e0800c490400160030b20100c201401407080c03040e04e00e43c24005640000c490b42c035210000c00683c2c080307042002d65801c2155a403400c0d5046540c00f407014039110116410000052155004140c20ba84101c2910203002c4040301810902c0d40d940701011480c1c45503401d9502545000c0d00003141048094011800f80c15164002c5602604a6119082410a8540d03006900c06134405503c00c8000000740c05516100307450040e2003458102c9070181c50044c0007426118440c0b21144242240024030011940000c100302880155100c94610382c0c3d07441000420780f1641c1843c240d001180c0040c06d60500e82158007403102d80c500e5244120035032114000481c0e480c080d06105d031a1001210301404e41c2540700b903001d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 674151969 1250 674150719 674150731
    0x301090513050f010e070801060308190c0203030d020d060e070e1207171c0504080a0f0c0e1e01060207080a0f0f020d0506221101110705060c03120c090315 68
    0x80d04054481c1da0360349240038851000003405955480305140342501c144108070081a2850081c0171a40c2162240c03801c078440d0840d03c80c01d1b5801e040e8080211406001031040180d002010341c1d44601280c2c801401a61041e4412000c061030140e01084903101840c0460141100d03540c4c0c00e01150803503092104041804c00e00b00001d01c5000c10010384505c006e540c88100201d40c1001e460f1505404032026038500c01d010821042c014240302c1401071010005880d8a502e80102014910f11440d00700320986024581200d8200c11080b001c11080130001c2462006100303504104411980e40c80d907040780c0711541801560705c584c0111035030002050084001303806007400360140312140101503000808041040070201c5081d0403660400ca20071010050440345008074000d10f50107007d4664414020700404521941800651000c6250711038040202002030071014010390b81e00c6009000c2140c1d03c0c1c01c108100c08981c888640001d6008103c9404d9542e025400b8004084401000000c90205000107102c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 674153219 1250 674151969 674151991
    0xa08010801050108030708190c0506010f2103140d0e010f0e0c031c050714030a0c0b15061207020c030106231e060306030a061b0e011803081602060f031f0b03010905 72
    0x8580042b030710500035503000306440107403040700614094104445891500c0c0072041809100343e0000072036000181d17503c0d034282c003902c2d96030313a48080c541110017414408409005586460400c10140d1001c2e8492099100d55508841c00111281c0c10190b4504428180070540202c42c0203e2990038052405445494442e03850b100d201162035505a1454200310509000141820104802d01c8102c2c149960045c5400c1101415915098040780d4036125210b1000c20700d0a00400003080301c0d2090000c03e813031800c018020300000e655503030714011502c2030101c2c01d414011200415030051400da0350000c40740703020440710302c0402d0801082004e660002050241c05005010850002948030320415020700a59110192509141d010003445d90f00321120345418800c1070480d07a0003140a040d4050110390b84004c444d030f03450210340079a940a21850800a411110101d0116400380e12031010314420000241c0d2010041c0e41400c0d4001100214070400404c4d24040005001d90341054009651104000f01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 674154469 1250 674153219 674153237
    0x150301020304030e22140103060b0a0303050315040b0d150c09080a02040c0324080709050609060d05010e16090c02032517040311040e0c0112150b0a0801080105010803070819 76
    0x5c02107050303600f010304081d503040d21200140304000395440380308040300341520381843d5541159006002444003400c1000c80107407400701002940d0b01c0741c1102c06504070242ca5003a120440e45041c500f0360081c5152000410704001d10040d00070700c179013101002c40c0c0005008145403d50b0707400740300051841504100401d507e402c9a114545034a5810b201c0500d800140c044006240900c1142041c0e21034101580316401e06081c881c43c2c1e071b50b00c080315401030801c039151130791201e00f80780082c018400c10450006500600244113540c1520711f444808490303140d602440440c0312100c0c200c0c1c4a20890b40e840300d0a41c44c0703444070701da4ac4d0b040d18056001a481000c000703401540d40744c0000555045a031040701d8110307000960303c0403800c144c0181c3d01034507403d800074200f0540d03100020f4000103208010314290b6039100102e01e1201c600104802c010801d0505059854220309001440480300f401101059800c00000044268000040f41c1d40d154209030881c0c20040443d28054150303001608030810828042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 674155719 1250 674154469 674154529
    0x6010c29070207030c06140f2101140a080604020604060c0305090415180902132a0302030105010207060203120f091c0e0312070f02220203090105150301020304030e 72
    0xc050602403055a00140900c524500d05800102c0176500890104440b5880400b000b40d205425940401d1242c01d40680320f011200c04000c90440d01840ca183c070b002d68000004031103c9080c0c04040e04001514841c581a031943d110560720b01040c0c13002500903c0030002000481e200d41c9000c400c0510a241c02d9140020010000d81643c94080c0da0560301c07824580b007000031940a24600c40e10342c1e0f58136400d101e00035003500010b0300325070171945038180c00b6140c0c03d4844140c982d10030151584446115414610140c2c140e00a0082d00240034030790140c41a40713070225500c0e0000003601c0240790702000388a00760b44c8002040c1084503000e80f0407800341c0b1845032905030381144164240451041e9a440700c1d82100c81c01c040502d041d403400911304200c207040006402040448244014680d0183d0f03003000c0014841c0710352011041c035065560b240d90b2003c41400301300304c0306400042c043c10803485400000c50040c0d017014203e10003030300d0003800b048000313000c40740071300b040e5008494002807221036101c915240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 674156969 1250 674155719 674155793
    0x304090207022e081503060703020d0b031002070507080303090309360702120a0221070c0311030606090606090f0f1021020a0507030c021c05030a0807020606010c 71
    0x2440c3c0740301e000001440e00c101e6014a00a40c002140b070501400c07514013602280c0c43e0980a0600310070181c00040c0c050b44a40c654100264440000d001c03200f202e000700402c40029000003c04403410300402d040012a901d000082e03902036159000075610300040f10080010001d5200c0395103520001d0070070b62910301c6158111001c41e00300040c90a00103860400d13002410052414116004914140405d514141d400a200d144403490030f8025001302446881c00000c1d4003074500020400c8604600c08420009800c0001c884104141c0c111015034982904002c03c82404071601900300380c0038441108540f070000f5800b0f680078409004041940031000c0402c0411400200d44c00c08202090800d500c1c1002e0070928400a0614950071400c0103000710b0003c0003840340203809000c0255a98060055548441c18510090417004001400c8445440c0a030380341d400650400000c81d4803040003428260000c60390510805d016034540900c4041956011491001c0481050b00e80000e45e06030070703200500d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 674158219 1250 674156969 674157019
    0xa0e01090207020d1713170706030e0106080303091b040204050105070204150b032412120a0e0604171005270a12030516020a0b01060f11060109021b01020c030409020702 74
    0x151082150703588030250a00407003000961147e5880c120415080c11600703800f00300390301510725a190101e280f180e4045407a0161105ea00100c007540000014440404c1c00021700680441c005410f002806212108210490086e8880e45021a100300b000c0c40061500d68401c0343c800003012204407681d034a5022041c00b9130812150b02c4180c02010004d01c096241c841c0c00b480d24204212601e0900b040b400046a0702c0e440c1410303602c0b2103040b012400700c19003802030f111103008035006014180c4869484e07021603600c0000c140c00030054000d80070300c403810340000d020f00f82c8150018400341000245c190590b8842c030880c0d02e04000d80707000741c428040004819444003480e0000340d42c1c0c045580c0c00d0036200300c3c081440600c6840150b41c0000c0254000550005c03180f41103500600b403002007825981d205031108100c40d601d805803401030100104280025a000d0070018038500030500e03c5850248080c0e08178407464401520f568000e1200300840c0d8065001041180d10252605011b000824210410804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 674159469 1250 674158219 674158253
    0x2190303020c1b0d02010804050a15020409051524070b0406060312110a03141908090c0a081203181b011421250201050a06050a0e01090207020d 63
    0xa00001c001011a0007000b50b00000f44410300d52883c001080b000103940c1809000c0000e06100d817000004040c0310040c0114014a904104900d000f0700c035802e0b0200085d8000d01514031034615250202d02144c90954007240f1000018250701541d625006003002102a4005510001e020801c008400a401c1d42d10840c011031103030f44040740b010306510700480040c81e02c55a08040101003454008841d0300007890744d07111601410200b50404a10f61805c2d518803551a4241c40248094002040c0c03681c03003403075280b2520006094440710b407102c10400c20824000e01c60711681d688507071030500d01280500000c541240c40d85240f8940040740b00442c9040070350b02c10100d81360203001c40e03040186507040f05010421001d20a403040c40c10031000780d240b81c0d1500c1c0150a00c6209003902c005818111461019002d5030f00c0804041040c040203200203022303210841e1122000703401d1110000f82402d05c1406181503a004000400f03040e030802082200a412001d0140c1c0e12048485625020500c4d41205101c00c00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 674160719 1250 674159469 674159471
    0x109030c060c02120403110f0d1208061012020310081906060501030b060a0e030c0303031305070503060435130303111606030c02100e030a080f01150f02190303 70
    0x304960a000088680c0030a150056400250340c103600b40e02004103c0d4140c0358070402c1c00700a00000c0001c6000c0b06603004003181c20191541e042c0c418001808256540c09003565a10f103095611001480b01c207400440024005c988954091300710b040d03041e006154000305018920301520b41e00c3c4815468021102c414070398a050540140090164074002c3d80040c11081c24107000c414440710101e00540f00703443e00b80082244080130094195070034050b0060280c40241160386a0070034076403003d030614401c60704a404e480391000001d40340c2404102984596000b9500c01900d1014100505941405103100d044030001000c208038013081e13440250a1524038190704840107400d41c54060b092400401c0500d12a5100b0701702e00c07400c41c510310803200c1075968500c0c0c08145a6049001680342100c3c1182c0894414240b004c1c0400c00c1c40c0c00806000241c440f90754107641c94031079aa0801c414403007030050001079480e035140d20343c0c0d040c060688e0a01c442040d204540c19112624142c5080000d1218124002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 674161969 1250 674160719 674160737
    0x160930020d03080f010f0302180a1416170402031518030a0e01030c0c11010e04020d0501151b0b0412050f0a080411060901210e1b01030c03050408030a150503010903 72
    0x9003100300b01303817401350042d0300258a40d2400c2da000030382e070f0725100900c3d40d407171811540000307800441640101e01c445103420501440360821154042013421100040070005501c0c2036a90010420108503034016500030700503003041124103644142442d00104070b46034007129080d030890b44000c01c10003810035000c0c0d981d9080c06c8141110004041d01c0009501b50200080802c0c150041506443c0402c0c030900e007401c241082c241140302080c00303800b958081c0c0740b0711442d140001036426043c00c05514112038982d2480c12140720b0110010325104510800340c00712082c0d100040005200d20f00d4101080c1c42400c100b820413841000c4c00c1460b0f07009004040028100f80103000400600050030805040100c410a0034882440d000901c182114a03070341c1c075011000b80480060381d0321507010740c03210b070742d6032040c0d60511110043c000d82d1811440e01480c0000d10b00b07000c44200900c01c2c410b840c0116070203098245107840360b000b10350203080c400240c007210f2504150000380c81c3c1d40134410b040ca82482a100c403180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 674163219 1250 674161969 674161981
    0xf1c0501050a0617072a14251a0d090302010e0609030406020309010810080321090a0206032e0807030c0b04060f140c15160930020d0308 60
    0x8500b41961144090107090000c914000104506240e44103181d803400381007120400c048002005056070301641030107080ca1040061151070103c90224540803011a0718200129034008100d058000c040454080400000d02005140f10b40b18810b4040d1039094904002d038150310841203a106980c1100907039512020340c520f1040602c0001c1e400341d0450081c42c00c6c40c0c03030b001c8065141e204100d9140e0400c00340100145417401d4a00c94207000e014407030100da4a403200001e005800480781c42c001103e400d020f500285104000240c042110707a030140590b421500c1d805010341411a2130140c81e0941000b00303040301809038501c042c400c01007403410b00502890340b42d414000441000354018039a6558100310038043c4941291040c5c15540462600391300310b11085003504581c1c001c061100c0f40501900004903030b5001e8500641e4050710b50f007615400024014141620031002a104040c1980c0180c2e164078a14190801d40302056048013449080018407940021a02500b9900031804503544009100c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 674164469 1250 674163219 674163229
    0x302040f0b041d0607030c0c0f14160b0d0b010e090406060501171e060a03080324010e01020a0b090c0301060909030806030a0b040818100c020f04020708030105060f1c050105 76
    0x100000c001c0240032803ca9092899684841e801400343c000d05485202c1e0310031041c031a51500e2840d42d00301c40348204400b100d10b0203020300b940f0f07040344090503c075015140c95104141020601194030141ca96480c00d1804034442009c2d08403407050b181444544800500d41d074075045061351003240314190003e58a8200700c0050030700d03d910215a422146640e040060b581c00303900150700ea100c51020b0350403090761080c002543c112615003000701a03441c08400e000b0f10380c6400100007044407130711350400c841d0709501c401121901d460a0042d40140d014840c400c0c042248034400c0d5811040d04005c0c0c420080a641c0442c1c02c2d6915548003254a6a80e10100c0c1d051550008117150130078005c80c09022030241c1e64403004000840500040d0207903100064128900e00c0541c0852940c4030050445070b140c81c1e0b65840a0400700709940203a00807120310307034400c255103800d200b194020359002040c141140d00b03100501c001500550310140c0014010420b51400348000500a0480c07500444041840c0d13061500303002d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 674165719 1250 674164469 674164481
    0x306120c05190b09130b13050702120325030605030d23030403090e191409010e030c030d09152a050307080a0b0f12010f14060f15040302040f0b04 64
    0x18100c10a007034010300800b00b2640407110b152008551540d04401c405c0e00b1000104a00c05603240e02c200c010120460902040d08001c2c810001a02a2550b6110b03500003000244002c45074500343c810301c6e081544040380c0c240300170500c540051400140c00b40e16078002c40c2c50401c0b1211084041041c04101c81a24001550302081540e10220050308500709560045c00000250141040040108000544002500001400340c4003048010302641c1000112034503504000d580400140d400d20020b4040440d000007254400c8a850004504c0c141d00d480c1841c0080a09100469096003181d8644181d122a409606020712080000b84a50740f41810541c160f80b100b424080300f4002d060007003141d019007005001c2e5200d40c0c0d07008040703482002c1c00f0018aa0000408009070f00c44c80050070028804015070140e00743c05200c48040000003513810000100d90021660554892403018403506241056000c4000c05071001e40c201e0700b059240d40c00281669005101648425503070a501445454a40121 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 674166969 1250 674165719 674165749
    0xa090509101a0a120207060522110105092d030d020d02060402010e0f040c031506020f060105040c050d0c030218010e130509070e0903040801150f0905070306120c05 72
    0x402096140c030312074540d05900312800010000c0c0100f6242d0015004440000c3d500343d91080031580c4811a00d002d400406054400d00c00d126100c0032011074480c40c0003501a00079402400203604140900c0c011101544544540d44e0060031140c3c030180c4204018082c2e1070801442c10380c20030414a00e8090519203410a4001821540041c00c001803054000c02c035141c1241d02032030088074070081000071684c142410030146800501d46203140802e250b041e4010303605200840340d0240303002d54482c1c003207a448050680980040e00028010002803a1503403000d2a002e9030f03030511906005129041f03a085880940c0100086500043d01c1c000c443c405641d025408002420b001c2c00d2410340d00b02040e801000803c1c02841540c0d12800300d412b04108118940081a100551506074600094665181d4209216042c03141d0308200312000701c2525240f48105540542071b00e40c002914003a08100900b002629500a05507240300200d440c41001d0f0303612684a004080110040340b5140c140710391414840d840c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 674168219 1250 674166969 674166991
    0x15150e09010f12020d050d20160e180d0e0117010b070f050f0d170129070c150c0507080c060405040207110a17010b010e100819020a090509 61
    0x18003402010300350010984003002c5580c81e0003201840862080c17007225130040c000c2d12170f400610002561054000b0760001b0000d80c0070407880c40504115903a24030800b0f04e01070744c4003108001d11401601e07803503076507100340c030145000203d603240c0405d9800c02d2481c41031f8000083c7c030700d088900320307507003103141c5081e0100210404d820070342c50640c00210038081c0390001030544c03d0118604044c003008210b03098580404806540f290915800c014103c101c1012440c0b41c1201c80400000b8940009080020400f44070b04120090640d00141c0c201c00798002c8004544e0701000442c082540e14414010080c1030b0901d40310101c00d520503041052901c12a0782c0800d415921500740a40c503511100c040e541111401d83d00542c480909140a00e18846010011908008921400202c850a104000003268075650081040305000401152405d002518240c0c100d484800001034613440b82c2c10340e03944101c000c1c0780800a41c1881e6a86000c2e680003500110010795000c1c0184203601d004446542c0001c5040a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 674169469 1250 674168219 674168221
    0x608011e030b010506030a0603080f040515030702060c1c020a030207060b0d110d0804090213051327030c050a141203190c2a120302181315150e09 64
    0x1852001c0b2a10500620340603e0021010880c0d4584a1304004040c55000424580364401e54100c0c0748183c110f0301c15030348074640241c1c40ba880c0c0140041142d02841e010760107820103980b0044490ba040d801403014480d44011041002d84501861005e040c2d0000290740269031615203041c043c040d90400340300c0340e02c00c1c01110064000901809200251184180c516240460050415820030b00503031340283c52040c00042c2201c44404000803110030b8880494ad03507920b41c030034001c28800715800500c0140004540c91404140910503110740300065103c0d15044142420030b9442c1420202c100c4000c03201e485240d031030142d42c1d510a02c031110100b00d82c141024150f00d0708035049644ce000401e8404d904503594543e000b0294460700310484038290300c58135100b20340b0304600c00800121143d0782c02c0c0e5034601016943b0039004d20900880b10086080203010b40703142c1480d800c101030b8056075076110000c96607450713060921108054000d40103003181150070b00c01511401c000b5100c10040c007d0503115080040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 674170719 1250 674169469 674169473
    0x6051e030a0308060324010303021606050a030911060d1401080321090c0d050304091b0e120118050304090b120d080910021209070503010606050403021e04060608011e03 74
    0x603010700d080e6010710340348a41c0d49402c40400c2c1007111285050880900b04c050b0300060413100d2480034122803096080f50b4003054801c05083d80c800302c0340150360005404000c00420f03076100ea0000c6000e02d01581c01c21000086000c001091603100034043c140c8591900d2124801c0e0500c01000740c010240c40000e18507280d41e2603411045855507050480720244940b001c9450340c0d200300440c1020000103007144003410204d04050759260014420008003e00700b100c07403c0c032940100340c05402c1000c0c40d164441300c2005030040140d1340c3c81990450555660310100e07211210456001803204600600c0a56585d070309001c0c011702950f0951410074000c0780d0322012a00c3c120030018401304800014904800342c1e071907800b10a8240045024100c6000c0d0011980400f030303204a80b680360081904400300e0b44440d03039490030325080ea2042d1140c203003c070b0824442000503044c42d062107500c201140f44030b072907140313407041c001411280103401601c00a2900742c014001801050241642c049051843c401014515 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 674171969 1250 674170719 674170723
    0x14131b05030c0103020c010e010203011d09010605090f04060e030f130f0b030c0a020c060304060606030b220216200307170303060f010c060c030507090605070809010c0203160906051e03 81
    0x14800e80f41015400140e2480000c400c5d0f00080d61802c048009568950f034070001004446800c10b200805000300c0b20105484540c140320f054100c2e07501900d60f91103607454a44205150800030415214140c869540000c203840c180001d0402c5070700d6201c204d0315402c80c1c4d1a0007441d04440c5e0881d20590145071004e210001c1d2810580b40d0103d481c17850a9600c100a510813401c0c4081c00420642002010044c03008000d41904034074113a2761107580422810040d40104043d441c1100c441030107014459000500403000380d00108540041a400848402c4040e6a11060300c0b00440380030340a00d04405050841d407509000450003400329000100c8042c000240883d16481301420061080e9062156030455901031035180c011590000410400141d9400000e00509000c80d4a400080c00000c8003141d0280071f4402d965825402040807802d0410a800548410004081c1660706201e02c030031034000c60014424400203000320003c081030641c507003424003281815400400c0d404035480003804820b5140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 674173219 1250 674171969 674171983
    0x50d06031b0f0812160c12021c0b0402060a021e0601080d050f0f1c05040f02030708030a02030910050906071419120f0e0d0b0402150301050907110114131b0503 70
    0x40c0e80d813040c0d684c005441c1d0301601503514a4004150751544480050004010106201210300039119a5502204074440311149550540005c110311242004038015080420142400700764900442d24103852070080102002460b05c001200d6074040c0380140081708081c02030342c0c50002d15003043e0341021030072054072480c3d00503980500d40403640450843c030140c845500e48280028400020082030500d0308000e01d100a450005034042d10400c080060111000000c45011081c1e503400356043c1181d41d000c001880030741c1e2410100b0050244400318642e920000101031051040d45820307038880b040340044d424181081119054511401003100106000007070455402e00149805140b8035010307001a00d210041e8022160002204c0488404200382d220070580070350f00841d0452000d0009403150011880309004032a0028502408180710300c0c040c0e2a80c480d8401c4c03400004c103190202c1500d41002e02802ca55101c07040140e00036142c10300c81420088049083d25880303200102d410207000c2075035454 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 674174469 1250 674173219 674173243
    0x1020d080903040f0315050c13090b030a0204020c0d030e1f052502012f0403031b0f0b060909010606051c09080a030605090c07050616050d06031b0f08 66
    0x304000005801003400d10894001e032500382c0b181d04050b912410596801000108401e1117140b130000802c1d6031500c2101a1461181c08902d03074500b29041034510300180a148a82c03503018401c02000c2001a910390002d0050003160a0092a5032480a5001015038102c20141c00340c5401010f520911454103003c00e035410b082c2c0c03690214030b6490380c0e88242011020040001c5040c039180080341c8069606410900490044003500c00c1d00400c6a004812084030750b11a1f482030749000c00080000a00031010340d81c24140c00751440c03081d4945522410455182d020080301c0d0b052403072041040502d0800300c1290401d010301d0003002a1401c000b00a400c40c0316000744000b0b1180390601e08245111103410080200340d01070140c4d07403207902e4800d000c0d0103410203008591042c828440010413800000043d660303180d400070000c00c10780d00c5003240f092549900c1211070042000070010204400258054000110311604050a46101c2c1c2c00130803030074000b1034120302207505c0142c200b0403201e0301c002080003e040b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 674175719 1250 674174469 674174477
    0x7020303091c020d1212050903160305120a05010306050f0405060402040e030409020f18030f0607080601030615120f060623070c06090f0e040302030714100f0e0c010e01020d 76
    0x5800c0010b0020655901c0400030350203942c10840404004100102e00d9100481c0d484402402c0c209a00e5001070311022502061158814028440c05a008518844019000c0d0515504d4041a03401001c0a503a040b6981142980c0302c000400070090070340b20303607540960815040b000c0c905007940d903107444490160000e4890b585485186800747d4080c01110000e0420340c81c115540e800b400c0c4032045a41011440c8203400b050750190320583d08002c07941030040e4540c800640300d18ec0e60303084299408074018241c5810141e5400000ca00e94901d9a00040e500d15280ca800c491b04180c10107a00c25038011201c0415202e080c00400c02c191600301c001d2454010318032807020103480821509541502a01c8005002149103020009a040c3c02004041c140e40b10b03074500c0c00c5c0140d00d5090443d94080c0c03da40090040e80100901d60105a01c5150b000c40b0040d45002e480c00c3e00d000142c0501542d001200008466a803040c100e00c1284c0300300700a001804007800c103402800c642e140040c1d142c201001621040c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 674176969 1250 674175719 674175739
    0x20711151305041e0c03020f0c1b0306090304030b10051e0a0f0b0703120212041214040b0a080603100e2b080408030a020706110903250b070503090901060e10050702030309 75
    0x1845c000c0d0140e03465a422012907544627038055000540d210300a248000c003c04017000d501c640303824082070251003600b21000540c6010324680d60b0213940e0000510849080007000c9000c20145c0c0e88030004503515403040301c01c00c6018055000c2210302407455101c01d49030308505008011109004040e81c8019402d030502100889032900040d0191051140c0004545040402c0004000c00c6400a01c45054a55949000202070340102c410610035030080d002502d07010b0201c0814184103e541075400320025003135401030b071403600084c420344000342d2030320440d5042400d14018000c200326412820346101c50009000d030607116805040110068005421800c0000c00684079a80c0764040300e18a99200d0741c00c0003802c1e500d01e0030382d20035081142070911a006032030055602070300d4001c1221101509090036000d5624110031110258010442150180800d003c4110141d6980048a0080c4a43c0d20b642503090f0242c020000c06003603039036150b82031000502141025032000000d48105100c1a6820700e51 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 674178219 1250 674176969 674176991
    0x90606100302090d0b0f011805061806010e03010e0d030c09290c120d050a05101502010f1d010b01050403121d100c050d030c020a06020711151305041e 66
    0xb06040c004c4014180c050710105005039095401000c03412617601134110509240b10035a000107035107095a040ea40308111800864510501c0801d003500800c050500310103101c080c0d408207003940d5584048503059000010520880c5d038041c01040e031061141c2c54402d40c81e50400c01d51545050f43d907c120300380a09018401c0e140b03401d48100b210444180141142e0900141c181811055842034180d414100c5c1894041078801c00310340180d501584074128050f581d9824062682c1080303c8038006d5008640d20342d0328428814100e07200d90083c0d0341a500c100180000d442c1c01c01800d4403681440309041250170402080440e07190002c0580c03c0019181105407862516000341400781035481c5140c3c48040054100c0402d50030104176040b692160064a1204150070000d40840307240083e840d0158000c1166400003e078154018144240300d91800240101d2081c041003440f807128101c0340081d04002803071034806148610f002d0080c202260280312520203250141181680d00600195880e192250500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 674179469 1250 674178219 674178229
    0x16140306160507050f060103031808060414030918060a0614190203070b010923360d091a0f0f0d0608060a0902040e0f03071211030a030c020609060610030209 69
    0x4250001304540002074500d20141c0c4454082c4000c0b004948010a02941912440300d00011142c0c1000513000550f40c41d1900207101c01c4190300050035000410500019603240e500c07201d108119104e00106514000d006c0c403007140136541126040c452039030000c0100c489201c0c103d81411190340c0c003030000321441d05001c1e40746000d9500000d14040c100c2001150551140d40a004000c11031200000c0071b11404138031404400084e00c00b000e0002d254015140419860100744502e1510540c8509514803001c540d04c3c2003070320006458002961600040050903285440e040c125540d040985140c240503829a85541c80381c1b003e58100c40d07001050b4000d41c1030043d84404000c0c0308100549146103000800c8400411031010101d1085d4584104075455440008260480e5030030306000314905080e070780302d01040e40c111040d2023003080f003182c4c103050307408000344081c0c5552030407503c020031460700c20310300a42031190040000d00503500800c00c1100c5e550341e134585201300c020541401a500c1ca01213010031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 674180719 1250 674179469 674179477
    0x50906040f022e350105040c05040909050105070807020d1d010201021b100c09030b010e040804150206061f080403050c0c03071409070206100905060409020d0302161403061605 77
    0x50300528129964442500481202d02c9201100e03022295080d018180d40000318500c03034010302013183c80d40140114102640301c1612600c4600708a821f0964504400003924417480007221103945500038800d426400c50040b40d00a1464005402c0b90300d0b00e100010141601e100181080c06090040c00c84240d001794100c0340010f100d14256501c1d001808015560f460441000700c0005280c040c100070701ca07204114400030b4075486401c0403440d92034041518100c1e00d0240083d208080100030003d003411000d48030200c54207040c0c000e407050345001410803110a1118403001070241c4401240c2c220160300c003200903403003641030400f551211810140c40b841d00e2240b07040c4e01e4041c442c108000c1458024641000d044584c2201c7d10035035035075001d00480c0c440000351002d078528120000c081c0040d0b00240c10032680194003806c006070f16032160300020800010307514183c01681000400c1118140301c40740400203001c00f013200018070729075400826a642da005081c50701d15400400709940d5107104208032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 674181969 1250 674180719 674180779
    0xc060c0702041404260a170627100b030c090d030e12060907060504050901061d0402070303090203060a060501050a051608040e0a06051c02060c0c04050a020706050906040f02 76
    0x200b5004d03c0c1c1445e0503040011030342419501407640b0584280560b14031402c0358003400f4142d4481c1c020780c0321000d00d030403420700181040764001c1c10391003950200000c0300d40003079642c60151001e020a00303095102c00507810389038103c41c08a040400820a265403e40200d500d04102521540d4060807281402c945441403d01920f5204d5a00382101d5550100000e1a40c003800e040b0381a40c058507641c250540d071904ca1842241d4108400e0001088810300811800f10340c4450710741035036a401540030004d000c07070344a810304801096965441d40213604042003510341c4802c2c11030040090b54109400600103028104501007000746c0065841c6c240d1091020081400d5031049100e600c80e03171610034640c080b0300c0c11100317a5a1180343c90b80c0002c09103400c15030541c3c0c50074021003c4800e5800c47e000c1c0f00481d030043e025001e1521505000850780d84461099912030000711074010703100c00b511301d022000d403003018010700a940d12230014480400c02c030041c02d01c00f00c3d504071a070403000060040c0000415101c1114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 674183219 1250 674181969 674182001
    0x5030406030f0f06082119050d0e0a201305090c09070f05040302062101090e010b040501030206190903060e1c1b141207060e0c01050c060c070204 64
    0x5040790990050300003400d489a0a100c2d0184003640c00d01100c00f988282c28980d03005d45080d0204024595190a002c0c078a031800078500070752180010920420741c4440400618002003004074041c407441078103a410124400b03006501041d0300d6085036000c48001d4040317000c3c810b545100003540c03011021107111010210900c050b14103019840c0c3ca610070b510069004000440c00030f0b00c0d4600c10040c0840440300f03501c44608150554081c491241c01880c0200d10040c00d0400708624240415911802441031040225207080381840305400d4600394005180900e0500b40140b00613503d15080ea000000036060740c446907039400300100c0c1c3c55510303648003601691034141d00042c044400704030355616100104d1100d1401c89072210480d03c042c0300551316920140348d901c03039000140000c0c010036100d0510008030340f90108002d8140605a0081c00100e4000740d50f20300c030600b80001401101100070b000d0030401d081a080c00c0e8130340e480d180c00a003607200c1f00c200000c02500f10b669076840008600821a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 674184469 1250 674183219 674183227
    0xb01091d160e0c0a0512100e090a140705060301180212010308040807120201201e01060306060b13030f0f0b0f10080c060a08040f02270a06030803040213090503 70
    0x1aa541100128000d51858240701c100040a1561072421940e0b5299203035101482c06e002d13025407084003140601100240c0c12080d2000030814184c115040c018024080038007081e6085242000b2035410424200d6016004510100915500e0409603411101500e0304064074491026023100280329101224102060140001c002c0c007150001820aa0b100c1008403440d840c1c641100d030b000c01c0070042d00240058a41c0c1c14599071800c2050104441075080d2040703a082c00b6201c00e100e070707000b600a0211205a95600300c10030501290780140001000140001c9140075184440e61400c80781d079020181044414148101c10010a10b000c004c18a4009114044a04115038a4035000d030080c6c4e804003000c560188045595400800c1200d4807440040c40d06103029041ca10684148000500940e030072260702c0504400340c2c413883c040300803c100703100300184549410700e070395420164007500d07420400e46000d40c1440051501d40440341c102c0d40441b2540c420b413084c910003501030007096a0040003804042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 674185719 1250 674184469 674184493
    0x11010e030307090807050102060c16110604062c0a0e180102030103030f1701050616020f030d0c03090b040e0106031d0106030818040207080d090f05030a02060412020a0b01091d 77
    0x501c080042e44c01001c281c030312550750b4400490b81c4e05002d40d03034030002071010000d0341c01001310003500c079000c00e10820a08500c05100400a0342607041580701314045540790440038a00d00e402011101d41c1107091800002044000010a5a000b654001c150314038040d031011500c0035131007003403d542d10b41c10f400007076641b0344e1030f4174005100e00000002d00c008180072491014a846400300214144c0c0d80c040c01032410001920442c0307501c1d1094038000c1c1c0e0800581005060151020302452800e10119203c451000c501440c0081005500d81d000521001b828002800f585803088140790440d14640360204001c000d071200c10401c2890030980410a40c60488000100001c107800b400d60700d100c41340c0c400000c0092400b40400d80c428001c0c0100402420041741010541e41c0e0300c4082c0b1140580220650392056684040c13455000c2200301d130150b0b000c10208400c0024000004925034214409030101e5860340e5501c1740094410f028600c2402d44405108440002c1101d030500d0408031101110045041c0d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 674186969 1250 674185719 674185727
    0xf130c12060f020313150207080708030108330a0e16060311090609040504111504150f020a0212030f2206090e01030b0415021c050a1b11010e030307 65
    0x590301101e080b410080e034070840090601c25280f01303004240c0303c80803080c0c0c2e650741d40e00e0280c02c1e045104012a42804100b02142c290720162481070b02c16410980e0700e5042c00c1245140441c2c1c158040c0100104154007540c42c566004045102da000c07151a100c04c2e1550401540a030511084042413446981c07400310f10035400d05204c0044483c0c5844c1000303101e10b500902d4440d44a00b204103500002c04009c000554107140e444154050300030000319014400315800181d840c402c1030007544050a020509211000b00b50300104c1c0c1b910841d05045019605d50f03d0042d48880b0350380c2c0c0c0a0712a074201c41d60100080c4082c030844600007515244103544200007040130740d0f01d40d0b104404002d41c120388400401d05600450030307003003560344162403c0302c10ba28680c8d07801030041000b0000c640c644508801c840e10046e40d40003a00c200b54080303806205000046107604225031009200c8007048d4100004500d82000c40c070500c0c3e99440543c40d04140c8443c440141d640136081002c90460b0b03c0c4170001c00c001c481d942c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 674188219 1250 674186969 674186999
    0xc1502010b10030c050a05030c1b0f0c0904020a0e060307051c03110a0f17070c06050702090703140a020c03072003060717130f12030209040e060f0f130c 67
    0x1c896401001c9402035045080320994134280d00031034004c11001c000c1e40c1c00380c409075511014031000309141c5160180501c8045d91340355040000740c0e000c209092250703d018428001c0c040d00c1610000c2a80c509600054600d170310301e02c034014032006c0f420301241d199203080c0301d550301078180500709599110f480c1b0f110b2a40e11500001c113400040407040108144100400c5002039150442c3d01250b45140b5500c0f50f030341d050b01d0100794444000041201900240c4520030b80c00041503540c5440b905e4011038014030602c0b480041c61700d010989003020803140300701c0501c0d8558000038165801616111094613591a62280850181559029006c04004030740162104204000b045d405d48031161103044007a24800c1d03280e1040b012841c1020001048011001d03001503041d8015145510740305481d860b40f51900303a0303003007a00380020b070000382c1d400b0746080138090b0f1034210105000510451908000089100d10060301028000340890302190290044220f50301140b50003c0c2d0b00c4520594982e8800010a5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 674189469 1250 674188219 674188241
    0x30c150d0b0109150302033409091506030b0f09040f1e051c17040c0609051c02040f1407050a080c0901020d120f0e01051503010209100305040c150201 66
    0x4100900001c00d940b00c0c110340002c131040201407455100f2003560650194000034500c1c0da80d043c0050800545201c1520400301a48074484121001110710000405201040c0c010030451410041d00c00021b88072070302e295045580a190001e0301c41d80b89000030302440403142809034044049828001130014254200e9001c600c241942d0b408c20005403a0076942070a0f5103c007074a40d4010b880a802c942c2c0d8442c2c801890380d002d0f17140c44010700030000580c01050702e050f101130340d0081c0f00040510042d42c01c540c403000030b480225821100d0081d201a0a0003103072410074000d001315150600383d41504510f8004e81d0403456070044209031860450001007450f00406000701c0001c40340d90102e418800b055003241e044000607030180075103a00310310003a515403043c40c0011144580d00d401001c1c51441d140310f4003a90780d0181001080c035044c4030142c240c4030361580305598800d074810420390310141d480c21070130f21103a00282008111a0345906118062102c25401400c0e4084d11410680e0078580c10340c088501c401d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 674190719 1250 674189469 674189471
    0x1112150a03050c030633041b0206041202030301050d15090203010603080c160e06060a120e07080c04141909020409080a080f091b2716020615040b030c150d 68
    0x10fa2505403820030102d0101020011b050116840100140383d202c0c0e0800031038002c0c0021034041c5101070220030300c7c4000203440c00140c111500b44030810859a2003d038040500340b009606650506000034000440341d040100288054041092450344680002c9602500203000b0840325540f0304001380030342e10a60062503d070284103850200b41c07a460300c8900a584503500f180d000c50b500d4501b40070665008000c4002400001c50350b004e9103a2560007404d06920f80e00014140142c40d104110b0724103400302542c988038a040c07071140740344000c00c0fa0030039501c1031600ca4130b07400200042005800800c15280040e400034207050401d0144044903000740f100b0703002560307103045940d58400c0701041d0300c0d410b035215000da8016101041500810803070000c0852801010310054412010810344108032180e00c000703807448450304018458160240031048421540080c0074685003039440b00c51081d020f0042948150758036034111703100792400c008607520381d040503021010780c3e0b0142c1e107055020380000145030742613 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 674191969 1250 674190719 674190721
    0x90f080601031208091f1a011e0c021210021803030909040204150e043f0f0302041809140109021e030309061204050c041112150a03050c0306 62
    0x400000c0c0c0d98101da8002204141d1006483c104890361580541042c00078410110220000c59000c0c2c606215808041c800041500030140050304a0410140150511030400e01082d00c3d8507aa172801c0101c0d80443c90265030550541c80041c140c4a40004c80c00000d00c1124094801c1500a41c003c1c4410001801c04000c18220701041543d00e200782805c958100c25500301140040c107054102040078860a041c01000c2c0b0f0311f546078880c05010448042e1112100b0701460107014500043d40d201180138004040342c44500024002c0c03800130007520a904220440050025447c42036045e10301621040003850340b082d95400001c4090034105c80b00303a6680f1074a003c03984200303034144229610b19030301403c0580d148078039000401021351580155505070200300551b03003440d52810010140070184568007103580c1058182240343c00111441c0e43d00881c03900340a2600d951b0307114240d441380d502c841845c548aa031000696102d141d00340c40c00c00d80150400c00702104103c00440d140884d8101030701142c140b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 674193219 1250 674191969 674191979
    0x819031406031b0a0503100b041107331803170915060a0302030601080a060e0d09030b040317010b070204050a150512150106030506040e1b060d090b07090f 68
    0x42040e0640e06a58198080400044102d400700300014506500821411989980304c2c0401e080c040d05081d114041c0741e841c0594102031802d0b10030350814040d030404490170200282c0d21982041d02801c07220300100c940c00c0c03560b80800304107080c0c000144001d9405010461489400080d5010b0b072580440100d1a032200c0300c3d50200c902da605030b01c52804a001410042e580c060781290489001e850680c00200003000800940c82c02c000803802494413100404100400f404c0c030b54212030001084024a0300081240d0041ca0350002900094a4020300c100c1c803561181d16060303840ea100c41c11003035100302503200006011b4005802404c03140740240c40074011076507950800c00449e402c4800144100018034030900ca43c1c20440e1b14140709200010484a80102007840d104082e002640100002611a410080b182c2070a024032021080131000801c400007203009450240118001d900340540004a040d001244040d0049104282c0000007043d46082c03440005128000038000c030302440c0903a84000407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 674194469 1250 674193219 674193251
    0x3071716110f3f0a03020d02160302010f120b0406080606030d0806152a0102091503040203071a120108030d050f04110405042f040b0307050a09090609081903 69
    0x10f1406280d194111018900c8074149040c265480345103260b012885281150b11040201480340b40c025002002d03400145840240f82c480804880003030049103440400061f42c006a10f80c3d448060b07801c110495400504121005100c40280c4540c03150070120001500800400c103180616010f6040d100b4049803104144c5030004250b460940004914810648220f203410240c10700d42804003401007502e000314103034449801c08008000543e5400540e490541c44e0131205c21101e1017540215505503c0c05400080d15601d46210b4940b240c601c0d0b1070780c0c1c80401d01203030803034004040c6541c201480e56114210300e0b6407a000103a482e0174046c9490042107403240e802c0c298038421b80d401399003c00c440040c1410b0202400e005842200d001402d00c9540181144810110744807201c100042e400002e060010072003984c200e42c0c1194000d400a4000340120344074449000242d4004a1000c1211030003880d1240052100c04400740840c50040b40703d10700c070351500c19074880282c0c02d907400344514002015121 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 674195719 1250 674194469 674194489
    0x9130f0f05060d0b040609020301090c060207050a0914270f03120604020705070306020903031b0a0201021513241107050607020118120306031502070c09060803071716110f 75
    0x1510000291340080c0c00501075801c1488010300c0500080740618041e074404101e443c2a4000c8005a00008402d000900341002c000c0000c00314001c003806180510040f17546030318405868000e4002103018060320700c0b448030f115440001074034011241044480c40d02d60383c1b42e401551100b00720005100100b4a1803801340240c80c04a90410007901c88140343d680c2e03900081d80a0a509601400103014400300e5500da003811245011141d0003404c102d070306e1840020f040214010800365040d20440c144059001c0a1280300304a42d80807800001a170f40400702655144080b00c40c04003250700f080034245001c0d0110002e48401c1c2e200d002110541e0701d0b00342060303003a03540d1840161401000d2000c0b050118a0111a42c40c5400241c100000d00d280c480c2c9074001e50140101c44801a81c1d00001d07404108a940c4070920700400d03400c1d204106642c1404081610791080000143c001c5260402c07200020b4208002c8030807416082261522900d018035001074840c014181c424481d1011035107501071421310018007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 674196969 1250 674195719 674195723
    0x11a040b0102033f0412030c0e010c020a380715090f0f050c0a09411608010617160201180c03050d0504030f0809130f0f05060d 56
    0x14505050310008a1030800203104000d4001e036903680e8441a130801c0700b948800020f12040800002c600e024240303010381020324041c0d02e00b00b51a0804502c41e440c8c0c00b482d407224486013481e1a1100742e0749800001d60020310b9804c180300741007034ac200a00c0400e0420620001150311801518280c021103200319505008100f0701800707807003000302e00450340e44003075000542141c0f0806600e841040315072582d1001c07403440c00086170a58850f44600301030b450b01c6003e840007403550000902101096286121281c0501c1c0700856101e030f070718200024a880804415020000e034a0038440140c0380c40d900645000154030744200115011500204038103220306443c440ca68450394802000d0303114a1500820302030a915144115545d52030040d80340c902030010750030b08174024010081c0c143e045003403850514082081c20f00504c5020402040000c00301030718110840e0300504c0304c903141d03136888012400d9100d22540c00182c10303260016007a640c0c0701550003441c44440400c0100025514130781071104402c010307940 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 674198219 1250 674196969 674196973
    0x2071e0b010f030317190510050a050a05030304050f01021515100516030c14191208130b0a1104061805061305040203100518040302010b0306270a080408011a040b0102 73
    0x3c40b000f0003000490b042c0c1120306d50310044200310035104c420301110b000780c1c2d200807860401c500030019850915a02009070104540f030b00300e12407402d000242d03640724038818180900c4001d03c0760b0049078020b0282e68840780020310040b2852a05a4215014441c0c3c00c08481c440e1552083c4031000e58460804c0d82c0c0c6155015440c000541d0729500c064400503c1c100c821a8124141d010221488000740181f219030030000c484070010b00c419242410320912501d48aa042100035401c12507a080e00d03010310041c1c15042840c110035a00c0703006840000e8008084801e80e0072500180c0010b0305540888000c0d4103004040d1342c210400d840b2010001d891080003900d9440c1d602107201480710340751a9009503003020b20203e0020b8041d94800c04202d031070b03880160080c3c5a48194040005040d0207010300984400304030f001d00860b2a020b032090042c808104220304207899034911038188940100189500190417841154403556114042e0b4042d1156014001c40b40b41c1d0340000508605050291910001c81600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 674199469 1250 674198219 674198237
    0x110a030c0c02010e013009030e12060615120c07030e031b1201020d0e01060335030603030d0f050921040b030c07120801030b06011701090c0302071e0b010f0303 70
    0x801121440c010401b6140904910550381120b411106604c0180b013452480204840c0d05a08014040800910700036004400014401c0e00c41c14001c26a654800f408483d031542910030340c4011084c0d0b004000c455000800142c040c0401103150f403001c0d1010300d02c20742d00c6080512010040c16103c0305081000031482e40c90440b14955403410410580d40b01c000303000014100f181080c5100141d54180080e95001c0c1d548060034010b119a1313002000200144441000d20301c03d100c800c007050307480d642c0c0300e084110320003002081c0c0c903030ba003841220480340c0b00107800e1003814204c240280080c0401c2c1e900002912803114181c250719840280c1c80004d61070051035a0034180740441e0780c0d1050340003c0c02c4000c045030411546c000280c6280700d490766110749907900d100660445c600240821009080c050600c0710b0700d0010f5030204150a8140c3c1500c0ca9620003003803902a44101340c0190146100040126202c1280e031080a46401c005001141c09515a0312241e42c1e51046094070044601028000500040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 674200719 1250 674199469 674199497
    0x11041b08130501060f0e090303100302010e040b031501090606030b01050d050406090212010906271407050a080c030c1504030f05070b0d0b030f01020a020c0103110d110a030c0c0201 79
    0x22050300d600210111941c4981d00301603071400d00715215030b000341c100c1c1c0391401d90a1183c1e405070314100c0e511681c110005c51440c01d082c6480f00b000d68103448000d041204483c40e091076a01c450304120301e8140050201c03240b12620b02c802501240c000d0140c0601d01d0314140340099210720a00401c125450107854030362074416650403802c040d0030010b0043d90340a403030307800040c01a103641c074680b085014894000200b5481701c0c900362040c0c030b02c11500c0c450300c1e07020903041018032a00010841c0382e141d4401007401051480541e910705107086035001036401068030300c0c0080c22940215180941210480640f803c1e5960401040b0105032800c07900e04200c0e5080c0300600000b03518010300b0003114000c00031120101c0d51080c1c2e403840d039807000d042e82610a4072041c1142e02420100f01d0f08505445030f030001c2d81441c07841a0025030300c0d40300201c0d140c101522088180d030340c00a60411608810f0314290180400b40c0d028403504095032040e0a03240000b450641e003450410320510100d86025416503072045000b444e5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 674201969 1250 674200719 674200727
    0xb0105040b0c15090604030e012f1e070f0923070c021009050306090601051f111020030408121f1511030403120f050d150311041b 57
    0x9015142c4403841640300c88010000300074081440703008040000e007911b00e010701e40181441c2d04441218184078480305455941c1c1528400c0603460b00300b04543c40d40c0030250388001441c06d414403844d900042244008100941c00120f01d00d03003525090038001c0780c940d985800300800c41d0396000d2141000b100c0141d045194041a80c1810341214052405214081a50700081d82c45c000c103070f6100300800c0c02c882003004281424020507502c00103040213424598540008600c481c10340c15550f01205032550312030350495000e0f1483d2410701c2e0341d440446180440307001c0e02c10010505880354021421421410200780c481c046c0c2141d01c116401280e0504182e002c0c141d072000850060001c11701440811084550401409090300062010402ca40035107406c0080c090407482c000501c030300c4950070402091000c80c21030010118800010301c0c24910040c200902203d260203a004001032b403a04244c1c00c10540c2141c0085030069a00030a0609040f80318a0108001c8a840c1001b03103e5038082c60450900c4107000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 674203219 1250 674201969 674201977
    0x30b010909021206040e010c140c1213030302070e010f0302270a140c0f19020a39080a03080612070f031b06140c0106090204060807120b0105040b 64
    0x106040114099840d02015001d903004000c8a020b840e00810400446140501903149200501c00c000c01c441c2ca10400d0017800c0b8160f15400f007940500004a016038414104060050615011555600c526138103184212000d0b8602c42500184101c610202ea10300315605494104c84c0c3c0025495a0946554288400114a000034904034a11600da0031800910a41c03003612845c444d8400044800901240059040000e454618100d0301407144d11100030f2120203c458095009500000031404103070124901a48110010f08202c080150501c0d80f0701e4441c4450b4018400307058031034a584000c0b41480420001384141079260380010444130209009600c0e854011a02600c07110403042c02c02080d034a006850b5202d0010346940d88030820502c03096500528884d0300c080740d00c6140c9850051b00500440b840240041010000255142c940c6025840740c8010b00641605544032036954401500c1c0800c02c0310b02a01003501041302035400b0125200b28400080161101414581060f05e07035403081d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 674204469 1250 674203219 674203241
    0x8070b030a0903180305101b231b030a03110913150b0c0706081f2715080c0102060421020307060e03040315020a0c12021c11011a06030703 61
    0x501d8948240184c809082c20080c502890040402d440e50a10b10800c0301c040b85882c121294000b00c843d403229502505660710080040340105940603650580710305c622581000404110030050050035000c008401341070414241d8030304000903090416006440c0c40388040081d0f11850a80f0581207044a0340c1c00015040308608400c0c48168a407001d0803200d920000c4000903951042104004c8158403000301c9501c100040b00142c11100700e82c0c80351a803503101d13014a406101001d00c1d00800c4002c1e000c15000700c0340ea40c6200744013620301171030301c1428000c06004540880c0510000034840354000100c81d80501e91240b5a002c040d094000300d0000c0c80b09162000d0700718001003020f040421440d02070300c540342c16900e024640d01c1e4a10302d0700b01c079007400c4810900d28060040c03000c120350f542c10901c4018065080802c405565050752000c03800c00c0701d83c40d07525a03107956540c404008681e1200500c010408114000c102d0304081203680000045034010543d44103000304002002d00e0303c05e40010600103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 674205719 1250 674204469 674204477
    0x30708030a2d0c11070b2203080a090501112a0a09141021020a0801050f1f14100215070c051506010221090409060b040608070b030a0903 60
    0x148a0798011529089422081e0044101c4030b0b0b000001c0415102d0200c140b48030f82000107030462000491605e801e298030480c05c24110124441c0d94050b118243c09502d031181c0c4841803012038880c5030401c840e412101e440800942d85450114040d402000c10500f140ad00d24028040340c0c50316041c0f1032180041c10700c00c400d122403021100b0520313282c001c811801741201071008210754915014407501c40d80018000d91a11030301c00020045542d0a003a0745000c1d503c002102644043d290003c00c1001050390311004c0a0341c6054100516001c000e660b890007442d482a040c490041c41d1000f61034180402d0255202941c1d001c1ca0200091401c07031b1449240c03240c6030058850800705190482d182010031100800417866440002041007010300048464032400452182581440750000b9965900307041c0118541142c9580743c464602a0f10542d5110341000b402441400074078600304000d0064468042c0c040d904126000c0392110005c0b5848050341e4070a68918203503a078405004002d0010140f040c0c00780 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 674206969 1250 674205719 674205731
    0x15230402041203030605120a170901020106151d06030114010302031e04140c0619050c2509140408090105030c07060606050307020f070819030e030a0b06090f0702030708030a 76
    0x29810ba140440400f0302036200010b2a900c0d2600b403108417418004268081c1c0c001301179950018400c40341c19040d601040200070f40313540c45140107034014030301c58002003070144020294240705075200304810114807581c0d03041440c2c00c10500c00d000e0140400c0c000e880001203070b10002c0300e00394800d50165512142124604040c01c500032050043d480c01660305450810b5051140b50000601300b090040c0e01600303a52884c503104080c0000080c4200d182c03a00003c10600103112803160300c003088000b400c692146075041c840d64010710005c2c9075a44600c80ea075a41c90520708003141040b0301207078051059400c511024030f090030034401102c140c0e000404030b40c0d521005100e010702142e8540320b003401801203905e50503542c0c18820ba010386400c0301c2c40c0d0022219400308a0502caa5100492500d020840950704e454810036189000ea0301d004120403074580510820014400b0300541400e030030700610069407401c2a40d141c00d8000700c15400100d070014007592041144034001124180150b502c422900000107407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 674208219 1250 674206969 674206979
    0x307120201050d0608160e04022b050714030708030c0309010503180609010624021b010c05030310031205040324090b130b010602010608100203070e09010602030c011523040204 77
    0x21101305400030000359016041603d14510301000c65000341c004034500b40c10a00e011381c0001c400c0141401003e1f448044120507002c0c900c00d0701190b510f19940001035441c0c4684540101040b80005400b4500c079216054001403582808401c40d600c0c2031105001d1440c0c05400c0c0015145540b010700150100b000c40f02c0070441c0d03c03800344082c0340644119400440d40918201c2540c2c038850301c03644c0345480c400c0310000300414190009010b0729182400d80a21120079400c0e130042e180a0001d10002d002d9010000401c0748400d40a01041c094034410a0000301964540c20101d540340624000140402c4400b0a00d42c1e02260704c43d01040303881005000400d0703107400d0399100300000300f090784c205e400d034907213039422a0230814118040c038003502c010f2000b0425a49002e210b1640d0381d00e1064008000b6500101089103d441810410b810075000b03012668296503e41c402980e070f500042502d0041d529082d62180c55410700f683d40411a0039402040f068514002055002e0044084010b98800e23030030000060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 674209469 1250 674208219 674208221
    0x209010509211209100305090c0a12050f0307150b2b0209150a1406160f0c060512010306020d0b09010b0904110a20070e0a0912030b0307120201050d 65
    0xb514a4454841a240d014841c00d41460072000820a03a01c0304000d21480c0d54a44400040392a500f040d85800300b03803901c0d0704908a04000071f4655079500070044400c003007940c2250791003030302c0c1e02c501c03c1c01103e909540d00195582c59006184004007004031846035001d200d40c2d2030700f02c000303040401041071f2002c808030540300808007014584450f540c0b0352030352400c05614003000c0d0607611500307400b1800b0851100d90f000500b9005580a442c0901102e20003450b5180c9502d0191500c0102c1c800c90100c80003000e040c800c4240e02c2c058021105419180740125041744903000ba2281a5400c82030f21150f0790956403160040e400207090131100d241c0c1c4074503032143ca0742d418a0440c02000044400f66550b05804180801e680901100b840f4141c0d0410101ca0803962200341810601d0421715040300001d1558412800d0540581c01184d03d4500c00c820b0045441c010f82c001c0300628404d40041296a40c00700007542912049400c0a07410742210340d0030001d0740100d070404d048462051518074500444944240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 674210719 1250 674209469 674209489
    0x50a02090403121e0f060602030a05180d030903140c01080402010e190f1d0c0906070203030d06090b0a080c010804080d0f021b15191806020a1116080304090209010509 73
    0x16000030400701605480c2401072060345c00e0204240d1007801543d04229020395a03200b50b1102c1c1c004c001000a81340d0072401000040300700c0840088c0a01c14400c40d60070000c0190001d0300051750824a000c48e80205030100250340e24078990103846030000c940d03554005460030003102d003160b0b80100b58513200d25001c05e020585540078140c089981030700e50b81001d82c091800c0184404000740039110740c0501c41c3d10342d03100c410307105000c008550781580c46000d0310100f400c4d03000300180303100120b08049002c50303900380c01d401c0328408440913a910401903944819a51380e515159804c2c60100d10200003003400300701000001c060402078088007050354514140e00c003040781d001d4051a501300c04c1303013111100c0e0b440e02400340d008410131840d580b00c42424014515015a072220f081d40e074113207075580c501e075114494a0111728110380d000b4504540b00c1040e8071000d4141001c034a818070403030068192018107410104050307410340d60700303600860a02d41410b40740d00096000404450500c10140306003001a91603410203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 674211969 1250 674210719 674210741
    0xa11040f330f0905060708091e0a08101a010e04270b01030c0f0506030a02070f020607060f110309030f0904060812040f08010c210609051509090109050a0209040312 72
    0x40b2040c015580b8000c10302001900f0584c0f040004000e043c020035091019511418012200c03481109514550491ba034481c2d84902508400c2d65000068807980c08111002c05003041501446000540700c140d084250325841b540c0e003c070b030703a216100d403450400b075002118400c000c02030000c10403440c4141c18026200c0440486840c0e40840040c01000380c02c000003001000f5030400e0880ba00c2c00d090000324503000003000041041d0380402d0001c107001d05810441c03540c1c1d4015080a40e11149410104c0c0640319908840b00098209200c800c0c0d50072040045900c41c000309800380d400d02c0801d0403000803e038031407a0f07070580c0103071140c01c0411100402d1004450f881c0d443c41c001681c447c64451099642034165010400780c0c3d02d01407901415039007005000c040f01d004042d1481d1080c03d04c40a15005003210f4001c0c05d0403601d80720030000caa000384c0c0040c0f060840c04690f0310285644808005003a1040d45800030100c0d00702a03010f10060a02d2301030306402500c0380c1010f40c0300c0d00b1600c96580c02c4540502c44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 674213219 1250 674211969 674211977
    0x17040f0c140f03190308070c1505090c0307060834020303070210230a0212280b0607021521100623131206050a11040f33 53
    0x646240c1c1d01c0c05801200141d40c0903405404c8860b6806504060300c51110740c090188007100300000d5105200303408072110244d00550721081d8255046003d00103010444400c4c1040c4186a070b192001d28001500c042210b0140d0746400c80b541d5022003190480f04d80350044070079000d24000341c0d4100d08914403c1c84c24500c10385c1c02151030703180c03860340207181c503160105200e00c0900c0d246208003500000d01d2203d410011880c40b0004644840740b502000b0310803090b21506c407801c070f1000d01841c200d0020559148121070110394a00b10b80d030050120499111580c1c00d50300c01020170041d40142440402e02c4c0d40360b042d242d40b590030030354010007030b10340710a40741800d0f0010815841000000b05204101074050800c5151004240303038552100742ca5070400e02c0c01c8080382e07000410008440412030040802504183e440360366011041c1c54104040c10082c0d90f1107180301d00b0b08501e00c0304508140300380c4080310b1001c1c201212a502d000106201045a5010300e00100a1460010503000c004600e10391082540d9075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 674214469 1250 674213219 674213249
    0x106090504320606040914160305010c0f020a0f170a1e0e03030d09021c0803090d0c05120f121501020106051909050619030302030a03150617040f0c 65
    0x1e6071002880c60380d00321180b55000d084100d40118000030010f034050030075500001c00c44442d0409407416080044082900d20402c01c1c080f06801804907e401140c4c4500000e02500e86855815a545c40400790041e006a01c407401010100d800c4800380d001c900e0160810880c820110079030148160b00c4003c01101050807030b41c482c220900d00108a048d1482286840640300c540c0c003001a80301e124890510000e40e032186415025583c401e022541031620304600b011a1608911b484445500101c61250b00c3c0e0080103100358270180580a01922103602c4409066007410b200c00d51203890b04102c100b0458000f051018454420f84440d5803401682106210300d12802118002800d48443e50002400b594074805a401a04002c828000580e141842d000c642c0f66a80300204200c9a00020220b030f49201803040042403540210082125000540d0140190181540e20032001c001070710501000a00f804000b003030040911074130b180c00501c1503072810440001a1a00010000b00360000d80222480c98 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 674215719 1250 674214469 674214503
    0x120f081c091109151507020d2a06030203010b1c0b060a120b040504030e0907050c06010b07050d02011418010e1204051c020306190f1103161407030c0302030d2a0c110f030106090504 79
    0x14412000ac1c45540b030207600d9981003610321003a0b03005660400020391109485030401d40c0864100d2481c110000c1c249680b00c54031190f008000703031002e10400714000c1c6012488641ca05042c020300d0301c201d0b059101c494080248100344000107400910300d074100f20301405107a008440c1841414000c001c403140041d21040181807550506101b80c071000150fa03d0281d0f406921a402608540c2c81349200d00c42d10052148401c1303c0d070143c9013407069038032103004030218228071801242c00340041d0b130030540d1180211211310351314824414208070044d50507400040050f0003506602e100001165500c14040750812540b1808025600811a142c42e41c800c0801009076110080c0300d00742d10b80400d0301c3c02e2000035200010503221031190707d801408000c1c100c0c81810038540204100c880d0103210b11400c020710004215045040132000a04001c0c2017000340d06030603000d104881c1912000e400010310b0201810741c2c0e00f0002821b002122250b010f54a6041c00a62440c0901c0358620440c0905007043c103e6082c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 674216969 1250 674215719 674215793
    0x1908060103050f130201050c031e04090501060f050f21070918020702150304020604050901080723061801090f09020c07120f081c091109151507020d 65
    0x200500b01240f51901001001441146007030420350302801c04503552114000a181144100b28032a8848000052002e4180515800501c100c40c201c000400182c0d8035554100c803011307408242c1400068003404071401d8810807000414400710300c00100d4640a000c0d401c20f1200c040221001c00101c1e90404081002008100200b0760700502c20800310b00c1c20041c1d9000440101d10300c3c0300801c004101000003001c54176980101d40252100a016541c50760f9a842620340c1c5200d680681051503550300e0100c10b0f900f03810307041d080f00380900400300342c2424040c02003144694881e285481c100100c5141c0060342d9000c9000c0e1b103004e024007650240c1c3e0b4003164000d80b49031160721b5110282c0b101c41c450010380490441411442c0035640b09010f01c2c1c0c1d45003001d403100c1c090014018010a068a4a8901003c00644018007180ca150950300f0144542d81d25881c45901c1800c0e81e078203a000420b001e0342c5120b148146c0010700400e440145000c10030714998a071611010010120700b074201c146905c45003450340c0d40e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 674218219 1250 674216969 674216971
    0x414070314030d0b0f100c0c05060f04060e1c140c09070e0f060a091701020c160303020d030902030c0f0627031005040c09050601030f05070e01110601050307120305190806010305 78
    0x2003500c010407103e54030008200400300b4035404a0422081c00d916400308108c1044c1c0a009100080003542c9400110b90720380341a0f80540314040224000c0c100d1030340c440c108012084004030440590310880301080e02c400c0003002601900b0000c80c054809000343c1541c951046c20701900040e950008850340410030b100c0e00702da44c84280d911406080c40410070007a40012240d003540c10280341419000c1000c501c0c240079010b40c40340001c1038025618a0214101c0c903810b5a02128001c1d822074844109845040d01154008070001c0d400d0340000c00c40000605103000c00c0b1030031845c050f000070f04c2c00344400b8238100c4034034140c0c84401c90005070824100340c926040105c4088481066000c01c001c0c02c142d030355584030b14598840d0354150303170f100c0001a1080c1c4c004d03441000703042400c0c1000d001078a40542c0003007051007c0341c60310f400308006404c1d10042800015041c1c5c1a1341300a001000c107a820f0852a009800071901e0403000c10004008070a0880354004203000c2c000d00c2c80e11011a42c1c10448005016190 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 674219469 1250 674218219 674218241
    0x4150c030506150723011e18030f0905090c0a031d060a050c0904021317010e070e0406020f070321050402030d080c1312120509090414070314030d 64
    0x1040c5801d000b91540c07a103910b958005082092607a4540b503e140400da054800c4a0f00c000000c400b04c0c9030000880190008030b00000d181c00507d82090a0101840840704802c00c0255040c04c018842c0e00060300840e80791a00015505014202a50342e10000304800c0e022a00c3c0b504410000c103114400c180c05010304200040c503050306007404169203407080d1381e03000020a151040c90322600420f54104000302100c5030414003400c02c0d0351f1516405c0400502c03c480b480b44c070034a0903201d4032851210ba41032041d5107003015524041c040c003910380310038244c004101401c241c2c0c041c1d43c20840721900188900003071841c20300c079884040103002c007000010343c1580d00c92001c0403414100001c110050350086002e070305e01029130404c1c8410b42c407410b85412042c0102084462104035816021074400c202c0503071040424800d04940d101d1031100c2e40f04803a03e0055036881c54100c4000b6012500107a11654624200c0c1d1101c0300302c030b80007540c03600e803820404403200210006810005000700c501c155400b8070911702c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 674220719 1250 674219469 674219471
    0xc1103040b190f080c0f12131a071d03030405180403180f170a050d020c0909030a05041811030a050f091501180e011a100207051c02011704150c03 64
    0x3e210140043c0c03c000d0004d04140f01c1100004490102d0b007580c0042c0c0300c404000c44401c40d1203140c061407030466841c00410070340f40420aa040241568510503906200c1c034056542c001d001030005083d2441a046410811791600044c080442c40707803603907006140c02c0710100c683d080846c02c8c0741c20083c00216102000001e00744e140704050010b03c0690101e00102c600c44c840300405a02041c5100d4100444014014081d00541c00351801c5030b50b000446540d01d20b4210380540d0291600d000542d5280726011002020680900080040c200390000300700d4056580c45000c281110301c4105004c40354021129907041660769414010019944401c079541308603060001c00f510402000da002c00080705108004881150300c0b8001154036050b009400b8094041d8000d012901151030f603001003018801c96540a42303020900c4a401910000e598001c40d0006031403c0503075030026044040c01e24038100140c0c18410800300004103490070b485607500c2540200c01480100c42c1c016910000d42d1003010030a4209 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 674221969 1250 674220719 674220737
    0x17030a0908030c07030f060b120609100212060114040801020a080f0c090901030b07030e330714030c250c05030309090f10030b010617010f12060c1103040b19 69
    0x1000000341038085d29000182c40301e10420618104014000032644543c0050b01c0c00e030200d400321000030740e2500402d001c0c0180d681c012030500a40d01280210000d4843c1c0d010000c02041da1035006110850b0108000d42605143c15129610725099a03c0100c01c000051030701020422400e5038450480d400031913020700c036032a0000c0400040c002200c1804007a041e9242c038000b09100724001e0b4000380c081461102030f244502510807140d401d05080e55100410030b0024190021070f6040d018100d81300c1d00303164940040c1440140d41c50002c0e038000a03d031000d11342d01044291600c028400072081d00b0340840b41c072103040008a1a117410a4007103684414083ea0040c00300000b590741304400c666202c04c0f0b0082d004400c0d03640c1303c2c00d40c1c0a543c59a0001d440106141c0010482d030f03900a1003119400121590b41a059030303100202041d004403072107100c80c980081c14079440003800603000781000035035a240081c90010301e0740810382160700a80c0002c0d01400e0014100c02e40303084c1c4403800c1030614420b080c45140c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 674223219 1250 674221969 674221987
    0x120a0504050f120a030f02160e091908070303020c1603140f0105150904050a080a0c060510050a0b09040b100e130e190c03050316060b0d02151317030a090803 69
    0x24482c514003000717044c0858011a048143e100300300d001c20300040003039980c00455a82c14000d6a1003c04d5802c16030a00903880000c10301004505202d0300380d40d219200d50b181039003940301103000b9009030700880035a0040307100400c94038000401100141d0f000780c400700d0185c01c50304207051502401c51024070707070750341400304004812810403405d080050003580c10010541d590f1a0890510003400d00080c26440082119040703540c0c021113502c1f00038402da100b01300c103485403410400312041621a443d405000c42e1000d020038010340e005440342c801d01520204161102a0009c0c2d00c01c0786084050f400583c9a540c580345603d40500e034424260310103c0100004421900c00c0703500c445140c000500c41c0014400d2180030840192a188010364211041d00e895a031007030740540b4480d00303ca8056070394600700b1203a41d01c54a4842c05203a18203500400e086c030390105030703001104941c10005c2d00c1280f5260f13080000400c50030100648115052441c085d41d42c0d003c02d04409010484030780c104251540c403d11400c40c0e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 674224469 1250 674223219 674223223
    0x3060e10090203071509180e0f030c0d140d050103050c0f0f091807080d0201020a0f1d0909030c190204140702060a1128120b0f090702120a0504050f12 66
    0xb0a07250f8102810340f40e5200c0203420b07200b40d21b156005500150007c0505034560010303601020304040c00909841e0040d0003603026569030301403100b524282d80c02c80c4202d80c00710f2780151440e00303449205130301c84d0b070034070201e40880c80403550242e20544642e04100c00350b00161a214a13522400c0004407040c0d600030b10701c0d90100342030b00340c018050807400c103030280c00e20b10043c0c1c01c00c103041c028980c0130704135080003808150003030103500b0a11542c80402e4a42d002c003920b46010fa52911903420501d00040c00c4000500100326400070003600c1c007009408100040c024080c800c0c000c030b0207017513034250000c040c6100c0f51060100f00e500303000502c20303e0701414041c401110703404038255400489002001c6451329942e41ca400e9076104204411380800e4030b0078081c1070408a200040000004a81c84d00f841948480d0010003c1d0743c1c1d07c1a05540c80154900d800ca000d2030500343e00342d00401d0b01c0c4102e40c142441142070a54030780c00301081c040416400300f0304110b80e260001d81c0146400041d20401407189906803165 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 674225719 1250 674224469 674224483
    0x161212052202061b0a2001050421060f0e061e0601121515080703050a0605240d09080d0b03150c1e19021507140a140403060e10090203 59
    0xe10a841c00259a040448019132101d0039900c81016914908024a80b20039403120224201080c2020641071003032a6001e4410741c2c0456002900ea07804645420f5988404105503440c1192826582e40322100210094450301e069111100020f10142c100b00541000f9904031201300b0304420b00050800440d40d0b442510342034070160b840d6021444440380c820002c482c40280e00282403d050071105988401d9002d000c003800f402d00d54804000c991a444109010742c0c0c08c0303001e01030700855001440102154940d2040303445c51008101c2c0c0d4200100c3c1208001030341c1000000b0350f207550700810783e089445014499450032501c00c400034090022a081c00300d5440100030b2001949050110381755600a9a0030001e80c1040c16500d2466501c217121000c030320021803150640741c014494581c02c2c801c0e40c41ea10a00c03a014110300d0300c80081c81c40e17007a98805030642c0000048000c0001c6201210072a820400190014502c206404110480185c01c03192405043c3c80d44e440c030030b03800c0000e20009a140032a43d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 674226969 1250 674225719 674225723
    0x50409030519030f0504061b110c0105070312020a050403051203010305070501030f090c181401030c120302070905090d11030a0c170403020612061005031b1612120522 73
    0x80b010104920080d401002c0108105440e00d00340780070002000850b60109158540010750360701844d8200c1401c8504102c1141800030319030000c1c01c0e4101c03560080c000b07040c50301e100c1d240107090a26403900340c400b40d800c40300300740d0041080410f007801081403c0c890300d0b064000380c1d030034103041d5891a2903071aa42c0b1100d21900703044c10b039580c0c0c1010100e03605400500364250000409030f1a81c0d81c0c0c0304400030046500080b04032440c42d00c42c01000601000c2c0c0b40c1412a0b402943d000308050820f00a01d2000c0b8440404034107501c111036000560318514000c40d40308488043c06060360b140d103180080e2070604503000340314098000b009240000740c0c00c400d0b0b031540e0940040c08050020107564040181d4420351b00042e41c0200086003040c007034041d07200c5951168030140e5501c1c200c03d040e0041903509020560700b078124501c0103604201e15203c4580585040e0090001e50162105143c4515141e071905405840c0002e0310380d403221508000d140101c43d0003001200318a251010b04200e191500c00d520400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 674228219 1250 674226969 674226997
    0xf0127120c0614040b040312060303090302090702012403030906080105010f0c1103160306060504110a032d0f0b03030a050906031e010b030f150d020108100b03010b090a0504090305 79
    0x5800140106036110024501c01c2041030007484c102403c209202c4401100e0807400952540861043ca001c11302516040700e0b4191210180c2c5411a4200103100c3d000070702c08011076680301e1407400c02c00d039041c40d10503440c032114462041290071070900034160590b41e0058810701542100401603664480e08940c54098946001c80100903a482c20b10500b0120000c2594507120300c007403052104600190803070441c0e2051104000d4541d5441c148401d03140c00c20005a1422005e001ca441030b68020303084840b07054181c41019152140b4816072030842c2004008d429912962485081520750082c810b40d41e0100007240218244251180d00400fa4861020080d00404011020582076251404950400e560000c007a190b40c0d03849544404094100300c031014001c480b00404101e42d61820324160f1400000070340301c1c00307100f140750300155621071002d01403041407213501c1070001d05516a4005140030b0139503901010350701c18074070041048a0406402c11446145403600c0b04000a80100480719403e103e504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 674229469 1250 674228219 674228237
    0xb0c0a020c09012105071509080c03010605010e0d0515040605041506050a15120203010b0a180f050d1118070e030303091b0d06150303080a050609180f0f012712 70
    0x64051b080c41c0080e03010b000c9010700d0304805002e064000381404203035030202048460350703900c603410182a1030a5225040c08260900405025424a01409070f1071a009200311402080c4000030341180d40c2044809480701c0703907620284000c20102c07941c104407104803407205120751400d1100103044010280b00c2c121441c1c81059801556a00030318406980700e2910a04545a41c0e65001c00079455205081c040d0002e015200d0300100788952280303200503541c40341500c0000c942080c0512000b1400e140094803540c03940442130102d50f460060003511020030446000140c2001240505050185422144203800a204100c081800011850341c40c00a440340c10f150303046c0c01c00100e005107e150318050701050400e0b0300c0c6005000c0030700401048911036903418000d0351742d00f28400308950043d80c03080d03030103085e007004100a41003200303a20200e080000151612126592032403841c1010f030052a08503651200360342e074071020841e00582c0300c45501d54010300417007006a850804260b2303c00390714070501071551 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 674230719 1250 674229469 674229473
    0x602041a130e060409020a121b1a0d090b07031a01090e0f070c02061209060705091f02100222081212040c1a030f06040c09030206160b0c0a020c090121 66
    0x5d0081c11000d81c0240a802849444007030b254100c018900c016142d2804800b28540b072018102c01c4081113419003800341c0c10785a5035520000003980b1425103e80d9090322980c044001c03403500344015005990f6524000340c0e90050f9500010010424160b10b41400002d04003040b9040b9400030203079010b802c9100350a4640c0e0341820030b654942183c00302a40202c1d0220368510f40a002150284c080e802d0304044034000e40d6448130441d8a441602c40c11604000c042071007c0c0d402c0e91081c1d2002c0d004500340155505d80c2c410005400c12600901c0c00d000c0d81403d1070f200060303600d00c0c081221020b446244042d0a203020b00c2c500c02601c074813030200200f4511710300174002400c0c08203880c030340400341c2011105100c0840c10740d1141401900300b030742c003c13410600140c04a01d83d4640ba01c9070512940300c030345581d40700ba8616001c201d000e0b00640c0005203404941c10003030f4009045002082e2040b444400d00c40d032140021000207141120f80c035030140c0500d030b212005100ea49102c000c191000410040f8074031082000d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 674231969 1250 674230719 674230721
    0x7080c030c19150c050405010309050c03060a060e0a05010f0e071205070801061b051216050f0303041b0513020c01021b1b03010603110d1a040602041a130e0604 70
    0x161107607100c50086a24080c0e0111485001c02d407154000e0740c4980c2500305940150b4122158445060003042003084200859402504203c0030140110f040c3e40c480b0b07450f40b003c00e013006d00450715500444e680c0e40090000f40c4280382c100e6004490100c00b001a0f40c104841d9015041560260060f103039212000a41403d204040f990502130078803d0501c151b082c0700c0005442c41400780075100c003041c1100900700a00c151241162001a00036009000904098200d0340080d40401001d207040e001c0c0b40c00544c0402d008128094a00603050001c603944d04d03103414070020300c481c0c264401101c1800070741c04002982c1c075410b54a0402c01307013a000680d1441c5042c42103009200f01c00390211a4007001800e03002c0400c3c04207101c1e405070140b0348014400c1d0305e005d042600700c906602005091a800f40c0c400c180c24100420381d01c20441c42070020381700c0a00d0034800da140490044904980d56074001600b030040c26100180d21011030f07101c03903915040c41101d10102d00045814020601d005c14900001101541d41d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 674233219 1250 674231969 674231977
    0x30c150705030a03060f120201270b04080607090806010303020a0615120f03030506030109050a39080106092a0e060d020c010b0a21060204030b070e030c03011107080c03 74
    0x2200c01103e54510801802801803c814410581c0003500c16000081c0c0041010381c991031181d05969441002d94804020b8922051891040000104101001c100560102c00900103040c00b88000c0440b4507202c14000c01d00c880340c0c2c00c660007940020b0300401c0042d4000510211a0b1780c000300c08500e040440c0780d007013800c4600d9440f8040360304046840704103100b5800d1102000c0390080d5818080d44d91044d09240c01d0303800c1d483e401442c40e40001091030115007281c0d07a400340110040b0844806480401a15080c681e90103011041991802e20810069000340309440060050003414400c1c403800030080280209a05910b0303000700c21980e4100c44061040c44c0080165000400d400d46610718905800001d402c1841e00030540c0d803038040e140b0024a40518940308848400d03803100e00c5c040400b041d0361035000084104841c03a039000c0c80080f00080000446500c1000e21b5501c94100440d1001010314001c3c1420100303010340d241c80324000940d06e880085601850f003010a1a64070412200d100303182d442 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 674234469 1250 674233219 674233223
    0x2041b0f0807121d0f060c04121703100e250f0207030615080c040b10050c010e1e0d08040c1505040b0a0f09082802030118080316020c030c1507 63
    0xc90441e40300220150700340c1029000b044c40048503102d080d0f0440a950740c0c8402d4032000d58a000601c4208440080110042d240521420850741592207000c0c11815542080d13541245618071040c0c184020224024481d612082c116a40704160b040d46041c1c1c1c1c0c2d0f21220400b20004c1100c071845241c3d1450081200100540d40302c1810440104461a06400420b10b4000c0e840c1d00d01072400d038540d80b40341501803903802c002c0040052005c16580c04003601c1d194840c42d08501c0c03d548903075502c54070100c2400703070420782c0c59400380c0d59011004079140c407400c040c403110001d0b0500119405000104182020442c2a07481e6004c200c02c96002500040d5903900a9a01c845880140045c054214581c0010101a03480042d141d4004081e180d01a454076a035604004480c0030102c0c0d0130540c10a02030f042d2604206002500000b00c64101d42c0326448183d120400982d5000030020501003c0d03001840e8003107500c19140302600e482d90b442c00010351550088903516101d1034003c590442000090412114499 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 674235719 1250 674234469 674234471
    0xb070503092e1a0d08130902040f17120c0c0a0501051201060f17010f090b030f030a031a0909010b010806010f0c08030901020f040806151f1d180402041b0f080712 71
    0x11058070b040491030303018503030001c80900c40360b10001d404001f0340262026100320030300200c209420b040000204060100741c52449103e2301101080700041d0301d0040942c051100040c15000030f50070305000740c40d80507910150400108102550002c3d00c152503144c1521800e28040c800c84440182c2101d040580300d50005404d100f450001501d0724044040d0340c21034420420500002d01c41e0000c15468250451492800360130401800d0b1940e886a40034080e41a8800b4081e25051041404610904021104014960f5640f80d00512a40c4c0000802d41e101c3d10910b0055414164140001d00b82d00301c4e050300138007046020002c596503100a4041d01c80000c81d4480b0345480d07a9a5100b6155519020354a2034820302000c0c980034803900740001d140034010b1142c40e40514030350954008940021b030500141c0311031403140f2102d2050707680d1303001c3e1112011405450800c203030910340100320494000140c2040d5111003c0344500030960407282c2d01c80c10008604200d0f13240e42d9517410683d080e10f030724013206c0051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 674236969 1250 674235719 674235739
    0x30b0414100c02010504170304031d0103060f080a030e190b180409380c0307020718091401091707060f06060f18060516030203070b070503092e1a 64
    0x201e40c15809240b046d40121800c640700810400c80107aa44030507030300500015035203d6040031401150122042d4440c041c580090b2183c1e5807140c400340100c0640044406420484440c0c00303165024880042d201000c40d6640e407100040034149001004912900d007507248003081c41c003a1616460400021800b0241003444521010301d480010a0b09021907001002150b00380a807850038000703046800743e254100c12044a4076440d080d50550307080180010214031858401041c4074040d0000b460502016160224951002e894100711311004001d0415040e03241c09090030125020602a12210303e1948900d540d410503801d0a03005040d44c804206903090411400040f9940d1121030020302c81c0d0503075940f9245210103035840306802214890032001420510040c1c40b140c41d050350030030a0a1090040368500883c0d0707034800703034100390841c0d0b914086203012003007000c242c20030b100c0d136041068003005d421a252000da8a91102181d405054102107035101580300c0190340d220342005104000500440070303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 674238219 1250 674236969 674236991
    0x5100212070b0103050607020a1a09160906090e15010b0915031302010e12070b0903010608060108061806090a0b0a020715150522020a05130303050904060609030b041410 74
    0x10400b0a2208441030700c10a000500680c3c4049002c03100150b000880d0482140c92200d048000f0384081c200c103081380104200e58101c1150780002000504a068020422502d00b500f40d100b2034510208820301500300e40400d48a445915401038107403001d4105041e21808000080b800c1e101d054520429521000401c1c88141030400c2c881c1c40e0710500c00d98480990b1003140701800529455080b50844581c0014000e014100411001d8405441e0160000801d41ea813000b049107400700a81c82210940c21050501c9441120b035a01d0700154080c1200901c00344c20116006a0f484480d800080c09000d80c407070101d09464020740442d0b07180e90708200c100d00c104441004000003002d0b400342c81504071101c0800000c0380d013070204c61080b0f545040002c505041d100303105000b019500100c00581000070802c44103140304002c951034000b840c081d070782e15030301c840680c82844210f0707045070801000d01c0035a0208200203044140155800350b4800b00c044800c5141c8140396107412a402030030120a42031002d01d90b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 674239469 1250 674238219 674238233
    0x902060d0203010f0b040e0604050406020c07060c02240f031e0f070914061209190b041a0c0702010c0203010f0606110634110601030c0602010b090606040510021207 72
    0x1040e00da00e4000202134a6880c8110801480340e03214000da51402c641c0041c1c501d28196001541c046d000b010054544211696407900303040d100d0301700c10f0109252607011015030401003011030340c0c070000c2050034481e1807005850604600400801708a64140000090758a41074800780c5003245845141002d15030805801c1c6c101c10340000c0340d403580011101200001c84028440c200228568090115480c1c44035500104100c04002802d0314024413034400480500040201d01c04450b6000e0208401d1174246403a00c10b00140342c0c0240d0f407580d003440900384410038500c0b008603200e05909082c103e0703c0b03416520202e409090b25801c52004585080000192190080c041d000d0810708901a0f800c0799450716000080c070240c03a4121503030035242c104944038503003e808001c05019a1400c00350110340800040518010013600200d60000440200f04849a0240507401d540301048030300342014501007000ca01036005520500d40320315141410991880c1c000d022021030705240031807203503030381d0b1203400d041d2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 674240719 1250 674239469 674239471
    0x1410060602060703090305220b070f150c3014010f0f030b01091d1b09070804030e04052a0a08090a0314090f06130e0702070b1209010902060d0203 64
    0x380c054000c440c001020503109110b00790780e0719415150300d401e004010604660075500c140140207424003080b0082a103000e8a03018280c01c5200e4030100b460b10070f0b646040403003810300c080c100c04030608113541070441a411156412029021228001c0000c44000c2c4ca840a600c1071f0800383c00941c50b1508080f16144a0044103040e90640e010044030305030780301310340c1c7c4030380156110190182c58284018007610000ea003000c0004800c2c00d2034402d90542010440742484c1031a016944440c0500c00704100a04050140d65800100c4d802e1503819440c2a46002e44851802980d40348280e5031100002d40c43c0d051403444090000e50003164035450304000d003505206500c10350148012a2061000031110000010380d03085841d4141e0300c8a110004540c20000b00f03802600107694400c200c2a6a40c8070350b00c5880c040c2010304040a0141461450051414154200030b083c0c00215000140240a140043c130300b295a0040e50a40405282e03942103050707401071800034030083d401000000d592880322413a402031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 674241969 1250 674240719 674240729
    0xc010b011404060801121118060a0e010b1e0c0d02030309010e0105010602120715090605150102030c0d26040b160905011d010221130e0c090d141006 65
    0x1559400d941480e151500030b51080c0000520340d040107101460b01e03600001c11842c03240c85000941240c20002480782c520703084081c0c0340a600b03401048050700d0281c01c0b04004041101c41e070380d2554185840000075100704d038202c01039003495180d4005018107850460f200040c142d001e6031910401d99200a4a0b0b61007a10780000395070800c102a50445018400d06040352020f030001c040444c1d41c40012146038200d2001a9000d4070007910f050f1310f80025008016a81c1d2080c600003500c3d203800c1004058691076140050704650084c0007170580144002444c5d00e048502d802c5c0801a403846034810380c5044c60300e04015003580c0c070070810300040050303100c10140101c84940f081e0a08100076402160703c807005110761400640281c85040c88ad180540c01101012010700c10740d40b44049414a0501d01d011381082548400b1001070400c0701c103d89549060f014000002d490011400c01050134a964001c1341503552084d0300400c0202c040080b002045980383c2d001100f41d414a0300390340115802030085d0720071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 674243219 1250 674241969 674241977
    0x5070f02191715010e040c0b0a080412080c030c0c0a0c061107080d020303012309280911040c05041509030201030b0f0a090507020f0102121f0f030b040f06020c010b01 73
    0x118902e0b900d012580c42c06089001148038440d03880d03d41c00b0142c1110180007518224200640801c000c01442d00404001040d034a03101000d00b440c0c900401008103440c07401080001040900c50228039010440e0b41008a07642d4080c0c0300d10186070b8007070506081c54002450210002c20000302641c010711158684c0d0141c00c2070707543c0d1a641f00b101ea03444049e5100b40c03c00582040006004907180b00d0480c0c00c200300c8003000c14413604d8000307001c1561441d0a40f40302d0545108072021030740301d588015018120121a04007805a5459959000744542d11100210b11440d1180944442144254191001020304800800900d05601c80181c1201c00d28001a4002400d1894010090030604001251850080d140c089038500d4060b44600406003c3d1441c401c50154044c40d1141030002d00161034803900344094040305080000400500c4d01886c0b603100410001900c041040c84042d04207041144e4000114001a03030712480c0c00c4540741c00265001b46a07510101d4800940382c8158000c0b15074030800e0300e03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 674244469 1250 674243219 674243249
    0x612062708040504050a090204150f09020a08010510031b050304120c0209061e1003020c070602070503100e190807020109141014070803160e06160305070f0219 70
    0x203004124101200001d41080d90400c800c021900341540611b9100c80b00d00b0b0006440941c40e8001015a03452441c68020507990420502c4642d80d100c10640050013080c00c110324104070400082c0082a0522030b1a08c5a0725840d02516494000d41201840340190034894015403c41e40d009011908140c034161440f8414407a03540303a9a004004200340f940c1c008040c0120f55072001e00700400074400600e49804c00c0103071100300000703450f82e0210300020050350300c003d40c071602050081c0f89481a00d500600455001c103004200d5510f0201b90304180c49404000402d6501a6a000601c0c140603107480703580c01c220744032556081c0070b0580007400c8814401d80c3e54603c5a41d40d004540100144052a290701200100900d880c8034016241d80300000d017400070310303030500e005615500c4958200311110813105030781066010203c1d502801e0040f40004c00c4801c6400c01c00186252207943c868003a004040c4100064100103000242c3c200d81c807803540c000c0c0306000341802c08403841c04040f000d119207000448441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 674245719 1250 674244469 674244521
    0xe03070b1b1c14210618130213060b04030f0819031a030a0c05040c020c150318030c0d080c0d0f0e2826041d010e040c0513061206 57
    0x14115081c0103d800c2d56020790741c3d1503940010300c046000d0203861b40300740300b0103006481003840c0e800d0038403e40250100c14008401030050044500030319201180440c5422800e006107076001042d1400d5940041c05002c1e41e080500e4a1200d0b8840ca4a18160031110128a0151941d140d005941c032203601c14180d0164140860615903595680040200071100300c21040c417290400e680401c1c1090160b10446100808050102c0c07008180c0ca645041d0381c10b000400c1000d09140d00043c106100f180400441c500348030b0b501d00603210803541051004002050010901e07160703042e010346801310302c96902045a03d10418101c802000720300d203159150b006100c5a205062800340c030030420f120751100b14802c402226076a50000e0102640300d65806414041407203906080c440140018108a0b01c4e8011000c800554a808000c03050380007095402c501020000041c0b01e40c0952000c80e1001d5074001001d40900700c80c40c0103412a90420981c6050400c2d842046c0191707074016500c0010b90f0039044402100c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 674246969 1250 674245719 674245757
    0x7080307030f08070804060b06071703040605010803070803060108060d050327060c0c040c0215090706030f0b10030911030f101803020d12020d0212090d0e03070b1b1c 73
    0x1260300c240441c5c8220006004034550b500250851800280414944841640c480540d010310200d40c100c240d40c04070801c0200425481240d0140c07072207400071800c0c6003080d80c469405110040030b45041140030304c0483c040751641c100400382c2030f900000307aa45072001e120410f5082400e42c13406c0b2028a80e901c040303904d5410b1a00841d504e642c509005404442007420500c4090000164000d00310321601d5180400a2500e0640740d000707104420213410305501d0540c004040d1891400400e60492811902c0780309c03503581c16103270481f544031420045016000c50401044054182044030b4241c0902c000c1407140300004142051405101e0f00300b000f150201c440000e001c844581002000360b0700c50026401614080c88214241c02c0040801500c4c00112290310310690b041051010789419080782800681c200a110303002c02d505680c40e05d8544c0c40d4024002a070703035441503c110100b20200045120180d103442ea138028038000c0755821580618074041c0034182103a030300d10320341d00001c0c0c210484020031841 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 674248219 1250 674246969 674246971
    0x480e0a022a0c130b101d0301050717070513290a180b0f040323100f050f2404020f120117010606050a0f0203071202162403090c030507080307030f08 65
    0x141130100c50945c1840c0c15514200007070030f80b06101e14020702c0c0c288907580074000c00c1d200d007070310383e40c0da0118500743c01e400c01d98221f01821002c14083c040c400c0400c4007400b9101c940840b4083d400c100c0043c115600d1034100350491a0000c1ca0309800041c0c0b07448050b8100ba11840101c4443c0c0d0703404910340e50303540104681d01800c403c800542c00700708000c001052528100034507611908401c05c11941b098003845140c2102c44081900b200e8540d01d0542003014984200d6502440100000c0d8013480c01595100d0040f0182010343c807405040900c0c0c5400ea01c41703605441e1b9842d5150521951a46014a484c1201c482440707041f00303000c0c1c40a240705242c001809203c0440f1890f4a4060900c04845000c1c1d443d45a80d00b80001188020f11110740420207012401a06100b290058030010002900071600200640c01042c40082d2004000c1c42c98070404011101c0000c6a10700028001e0311450449030380e801e5507202418600c6110b5000c5085035000c0020840c04d442902c0340d100040700d03154262940e041c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 674249469 1250 674248219 674248241
    0x30e0a0b032202030f07090c09080c0a061b0b040b040606080a080a0e151909050a060c08090f0d080a080a0e0604030c480e0a022a0c13 59
    0x80b201407450601122406900b51107100600b40d540d0207032642e80040c07909a85074840c01c1000e88842d603c100f041d80104010015007070920292040c0b000a102150259865200b03040410006441c010b03071080b40240d0748a01c00d90300a004801034200350400080b08001540d040d20158038201000500101c0056100c1c080c0d03038012029824915005400c1e20070006800401d604954503c0e13141d00120040750040002c071031012800900405110401070110505d604a14041d9510502c28070000350800c0381d400750b00794001a510344e10741d0f400020800c0002d00a0000e9085164440703a03004001404000d81003001e01031780da4036440e41d2841d41000a442400302c05141c50340000c004140840e00c41d541104015020384441160441c0d1a049180d021070a40e1480c0380c2c080089440d02d01c030b0703a110340c00c0810b20140012580f0070a810058a445180c0c00540041c403180d5000400c040e0300012480006d118050b162081086401c01c04403490b00c800580204520407140d04699400401192050070700580f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 674250719 1250 674249469 674249491
    0xc0304030c12031706040603080d14060a0803040b0d020c01062309010b030a05090a0209090a030e0d1101052b0207021908030f070c05091018020c0d03020a030216030e0a0b03 76
    0xf19a0021440084c080607000c0e03a00591105000b00102e00f03803800500700340103020030000f05c00d0f041000790b0004a1020305210f10541d6158010822040004299000c5c0d030320000020b5038400c1c0c03501e00d0500a1042001401d12542802d100080c1040511421850125030752080074090f04984100005007000b402810000300091004c02c000b03100390380c442940510044101c0c2c807021490380024000301002c0f2030880d006c0d4810300001d0101070b80300c0682e6421960a039450b070a03200240e42c42c40d58654002c1030b0141000b4021a400810307041c5a084400011b8400e00380741c4c2d2800c1110001000380d40302003000e9001c4c01d00f50085d0350405400800e1601101c416074007442c184910f8010410165100c124282d524040101d00410b1075914004054019003140d6400c424181c68030714100c0d040b40b01400043c44592041c000c00707000400201d42a03440e02e0380d0345001640c94500780000e41c000e0045280d403079101d0203d00309020400d5001114141496001c5a00100c44d0741d40d6650510144400c40d10300c041d10b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 674251969 1250 674250719 674250737
    0xa0914010602240a2c0c0301090203150405100501030303020d1b080403031109090c190206100302010c170d05101e090f0b120d090f06020613170c0304030c1203 70
    0x5003030f218000f50f402014072030020550b1404d501e2030189001c1030481c5500602d4070102107640f032502c10042d411908006400034040c0d185039400203916100921002c228002c2074000190410805101200b03070221985000c2210b5610b03414020300a400800c5112081c510f1701d44294004000880d0200351800c1c1d07540d03030201e19501e9940031000380541c503a032103805907000d02041c04181e40713482c030051145c041903010f02e440300318040095105d103454001103010364001405019019004460303d0068903020700307003804491501e241000b0100c00c030b2501d0070f158070710224941401001a400c50390140d401e000d4410319044d00c4400c25000a8662545000b8101400e00100485134071030704035184000341001c00192251415000c9140d0141c42e40202c6040c2d0095080c018465400003070b06005403441004000415080080196a4040c050712400c812b24241e1300c0e8004000d414500ca02d510101c08010580720313250352680580d80e420502088407003521481004c09d46001801d014400660166140051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 674253219 1250 674251969 674252023
    0x509031c0b091305100c05160305070b01050603061305060315070e01080609090c210303070206180a020a03080d06030210050a02060c03071416020301092406080c120c0a0914010602 79
    0xd2843d0546d00c0280001800310348254208041c4c030480c118040d4544650300c44a92030110483c11058218903c5200300b0703c1032150700d49a41c1c0b5801003d1400e01d0340003900351135210010b45042c0d420307000410509540010464041d9000d0024410400c00303072110f0180380c07170300d1040020501040316194269800041081c40518000030701c1e2000115402c1c47c40c140d0020300b031510b0f05542c422180000941e0080703090000b980103050b031141c030b03024001c0e0181c568440244c0c00203440d82d045100c003400d05c54010450340064513081d0711210045500601a484c0780024440c082e1990300114081e10140c040c80c0000380200b082d032003c40348541a1541d814903540d00100c1445e486402407900c01c00c0948015100304010f813801d2140f46034031340c020b0421203032030424114603203545a000c04003442c0c401d04140c1c08000d005000200c9040d44030741291144518840a60050325061607104003540c0250007908c0040c0502043c3d01c070580c44060000140c07030580e26400242d91304d5030401c0030003020b1800003e4541c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 674254469 1250 674253219 674253221
    0x30f0c032a031e060702030f07020108041505010320060903190807050d0306090606031e05180a1104061a0a03023a0c140d0509031c0b09130510 63
    0x10200c240c6480500700a15030000c640742100e2100341c5046a2612500b1a050351410400c40da40302000303200940c945500e000300001c590007072040003814070000b0008a0301b00056451010041c42d01808200519a960700f80b1090350789603c41441e40c8600594028070440c2402d4044450b421000303401003281002c5414080101c0100c80401c0e42e560005104960004070180301c1d01051003115a4041000c0c0d0500917581c0450707481d648080141442e0030740d0340c00405540030641c0404851408000340c1590b42c1c2101522100304008005814002c540b48501042140c1c10501c00c00300b0143e03410010603072038101c825a901840802e20741d07a103005011089101384250010300041d00410810091034200c28546811071201d04110643c4d2082d2024003c490300301445800607201107440d0140e021645025824501c2c81544008000b8036150f500046400100b0004c0b00c074440000d050b04602d80307011031381c4e9400400312040100e1103941d140f008111582c0441c680c11001030b070010040c0c1002400c10706810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 674255719 1250 674254469 674254513
    0x1403010b03060d0f113d18061808010b2b020d050a05210405010311042c0f0c16030c170c010b03070f120807061109030f0c03 55
    0x558840c03d070201203000190140b603403088041c814840703840d40aa2100801c00c0441d0462200c8054801d881d46200c54082200750072021000240f00200d800d08601404903801700880d441002413010420002030110303804419440ba140c2824030b2030b003c107a25984120b084c4e0340035206403070307005c80103100d804d014a003422104410b0704a11846195900320701d601040340b041c42001c0986180d040380740d84a05003d020300246650070b40c1012401100c003190200e1a520380154015981050b55420800101c4812030048502a119204802c2c000420800020140c1c00000d443c01001c5070204d03003c00c1070282e040d034038903014004c2400030f1820701c42c103070400d0395003042c51000603010803068070f9050b400b00d1103512594210100c0810f443d55607800c1040070a0a481851042c43e000e0360011004103e58000301d08200305a4070244500e4040e8109401c0100303441c0a4440050140d03841c0c102100c403011511401001c0c0c3c03000c181d01743c40c00c0074007200c1d909450b84008200c054141d0001c81400902854020447c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 674256969 1250 674255719 674255731
    0x10b0d0501081c050a0c1a061e090c0702040e060a02030702070b0703410d0608071a03091015050a050f090c090102030d18050c0a150e01051c0c0e011403010b03 70
    0x410341c103002c00e4490200185024045808560300e51003070180303506115200203410b01c1442c8a00030274005400c04140b0350f0000810454480d100070580c801190384980104c10301d442404103c580c80e090084074140258400c0e100900036214020300029180f1843c420788404503015185c90030908030b00c00200081d0310010140243c00141ca087c1e1103c01041d940140910844a41c003468541001001710703000c0300e605801455250b409104100720858607070041480c0b081240c1e84150b102d4a40711181e03444c0c80058411704010b20304054400342c20b04d241650070380840740d0840b048a4826a50010300503915480303441681c00225240000e000c1c9441d41005003822030042c81124541031160408508032641d0742070b00d00c0d80903002c085201c24400100507503034100c1c1044440440442c944541c4103000100318002d142440200682c04010381e024505440792400210a01c43c00e50101c0d050b544001c0084021107070118481017042c00f0954801e0320340c0500143d400c03001c0f40ca10390070604400801c0d04010301c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 674258219 1250 674256969 674256977
    0x913050109061a06070203070b0d180b0402030d0302190c0c0506070b01050f04020c060415060b0406020a050708030406090302090c0708120901050a020909010909140105010b0d0501081c050a 83
    0x155100051007481141c000c5030091000003410401d21105000701c40d40b4050403449000b062203401c000d65400710380d1504a840d4034051a5444a00500072405440001c2c4240f442e10b001d0034102c4240004240a00c2c4030714400c40941e80900d83c05d8100380d049008005e5102440b01120030072004031400340c0102004cc0d4000d17a85568580d030b88070002074450f0700030070741102d0300d01c210ba004016a04000308400c01190080720150305080070058120303a00e4900800251081503c0c03420040c04805983c8000041d10104130750f217a1722a100c10740a5620150080d04940511078503c0000712408040141c0301903034000d5468003441d0380345400308000703801c006d0824541403404020700000140144000c001c3c201c0a4840313440149000b40f080c2c1c3c21110010b000982450042003c189550385054009041d00c1940800060450350b0b800e04070020100c460140742651701c3c1a00101e211004c0d80090b0200c9400fa032028043d982c0c0768486c0d2910b1f00d0880b0060105000d9a5022110712406003024001c404080d280c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 674259469 1250 674258219 674258251
    0x40f0311190801020d0f06050102150a02120c090907031506030f0608030a02010c0801062102070302030d0f02091011071a0f0706050a0f0e0a030e0d061a010e0907020c09 74
    0xc2465040046601c80003030b580d40054094004070715402008925130b6224401c2003020302d07003070020b921900c0702580034422a00701c2c3d0020305450760345d505845000302c24003d20540f52600309410b0b411588003e42c1e65104104040004400c80e100f03001d200600d0400010b10010716103000301c2a40070b01841100c8507205a10303008046080e80082014000d422101d5001059441320b040016000440c1a041201084003030a5501081140c46110f106981100040140d075404541403c0b0f0440c0252410100d8160034280300700c0000d215034002c0c01440008559080003540644000e44020b1410914118180c100a03003c00407141440328402d01c1d44e540c02107461401407070090124284d404220100c1e000c60760381017400041c0400348110100c2c01c0342c0101c10806070240700070242d036a414218009082103400b000d41140c60300c444040391100f80d4010310902410124000c80200c081004c08046e0006000800c00c2805240c4100060b00072034230364014021400c4500d0a0201600d0300804648260102213 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 674260719 1250 674259469 674259499
    0x10e2815230103060b132907030305180a030c150b03030706140601210507020c0a0b1e25050316030201150b0a050409020d0b19170102040f0311 63
    0x2410081c1e4908003042509141d0700000901104c203190042e000b03410050010750224441811a88290fa074006120745013082c00b00440202d000310021002400c41c00810307910105601608210701802a034814803603018403030005aa9107054003400a0005200c528a03100401c071512403454044000320030114001c0640c0c00841e2a542c011081164075580d6001c1441c60303200e1030790310750b50012001d03e0700c1da6082d40302d0b51480c1c000400702e94201e10525982c4020071000741c000c115510300b114012b41500c03071559032500b02800ca50480515071030f8100400420310341080e580030480308400104038030040e80103040e20306421941d12500084400f84810030840748210b80106114403000d10a5002180700c2d00c1d00151000b007c0c1083d1b01043c6950400d111400c402a081001e07134083d0b403600a80140c8544c550101e0001600c4600c0b500e42d0402a90034078440a0303081c02c0c5160042d142e1482c40030203032180300d46030b01e401c03032159114040031a202da000c181300043c6641a142445c900051028000031100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 674261969 1250 674260719 674260739
    0x50109050706050d06050306010b090415081603050c10081f03061406030c01210c1b0c1a030f04080d021207030e0f030408071502030f0c06010e2815 65
    0x68024101080c000b044071000e00c5054005c0c400030b003034280c001e4110303945006011403281c056440c42c1ca100da9203c02c0006140e5a0443c8400001d003034680843d0340c000040d1115511138041400251348500820311811007609086010320601e80f060365403e521943e901700c80c0b42e280b690300c07042d400314034028a200202107044c6000e03410760b015000507604040e041c0b80c010985051144917070b407414400400d0059501e02c0c40c500305c0b40c240700c2d980c5901141402800000300d07a107010b8015503d92401d10007401c01c081c008000b00100c1034956000854030000280d456039802808101c0d946224002d00385d002400151504000d007480130407a100150070a444100c0044220104442d1240040d036100c040b01d0343d404040100340b06185409010754030f0304d410f000e034203502c0316500d024080d41601620600c0c29901d00c01c004484182c0283c410003600d501e291180d0a13107a000c00e103c0e0759106190600800c0700403155050130703010115120290004941c812460001800d03601c1c0c40c400c45038a208078002030350070310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 674263219 1250 674261969 674261983
    0x4090516060302031e160509010e0a240207031520121506130311190303080f24040b01090914040b1806010e0910020d410405010905 58
    0xd44016840386407030905c842420581240d000c1c0507480c0c40c0240f05100202c1c103075940003c460b80c507000e5601c040b00001650740b80c51120317243c1d0f04000b20680009203140240c4803c0c8075808401c01b050000b4032802000c030783e50001408013030321800c41d81a0f9040a18456480060022103107003200c4450742c00c0075507046282c0c000d036485212408010040051142003038200450302182103810a00302003c5142d10440d8440c1400001c00e60400080c0c5200340340e44042015141402c6207006090440d106d2800070403070721050b120140c554138414041103c00b201045440c2e007000d25800d0342081501560200f0018040309c0241d039040c400402008140c0c00c02e1401844441180424150a5402c0500d848405003100070444224842c15031246120700c0d90224805044a4143c1501002620f130302c941641880c003108080612644001004890161241c200404907981c02034075200041c006100c0340d410090074006411005100080c0780c05c94251a04d599420a01460000078400314650382d0500c0c1c01c107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 674264469 1250 674263219 674263229
    0x12050a0c1710053145150c0e0112020d06030c060c0c05040b061e091915090303020c150c0f03040f140d02090402040b04110901032904090516 62
    0x14800703901100315640025003058200b80701d40100b0004801152801405c519080081c803461701104201d281e00358a84841072a4101d03215040722640366514140410101e0300c00d0b9600d419040442ca900c035180186440d55180006845e1800748039000d415001c002c1d4090a08000659a56880800030980743c0700050042d005a440d0351004944606000c409030425511080c4920305000e07480400f0f866001c140c07070072440714100c45201040300250314186400392007030703c540066210304c420b4907004602141d18115040d42d40c80c0641c2c403025050481e042d1107280030203070140e070100d030600e0103504240c903070700300c0155009102c941449841c0900a060071110b5080c01d038980e1000ca024000c00c40c0b0004402d0007420f028410f41008038045000c070b6000c1041401c083c0c400e004501c0090195201c070f80262030fa100000340200038600c05585940195042900707200d000074501180c07801251f184030f450b402c140e40080305050b88100301404100140c421110100d51a001d41d000d0705503104161042103020344 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 674265719 1250 674264469 674264509
    0xb07031b030f110c0d0e011b080a031a0f1c02030a080306040c0c0b010b0706090b070f0f050423010c1401091502030606031305011b12050a0c171005 65
    0x1400812010780d1418600e504460300200040600740b04001407610b8422060300f1b1071840c0c0c4c0c03074550060325507107010780f03e102004807069041404c2203e11002004255800d450800c007620343c07081c0c00750741c02000c2105541c001b22000301415007441d00e524181d40d401d03020440c490071030840b40d01103410110851801c44e03801c5804824021640381c90300402c40031030ba070781c03038981c10944d400e4507142c03000310301842000300707000f00003509100740074203908190921500305d40380c2010b03030802c0c90b0000c26564841d4000b03000074100340780c40c4400c04e20580440b405c40c0c0001d01e2019074080460529010038040000983c14003050303040940c00619000c903060124040640009103d002d9030400140d000c03500501c42c0702c003a20410400109a541c6816680c0082d02d450f0443c111f03110b20b1070002d00420070b0281c40b00104101107691081181d2110110104520b80c010501480d00c030285100241c07031600e0310113400b0a80d503080102d40306004029595008240500e240b40159a6002017074410344030040c0c002e100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 674266969 1250 674265719 674265731
    0x41d03090a051507080a050403080f0a02060105040203090a020f030a02032b051c02030a0609050108100b0d08040608130606031a0907060504120203071a13170a0b07031b03 75
    0x15150841d03034407005000a492503a21290203462103070040c8580d038402484008042000c02c130551159040da400345a001c00c000d540d8100240201c030070790300041072402c0144a554008a620704260080c1c07802144c1e03d03802841d00348810f508010500945058840c0c062181c0c3e0085001741c0d404029046880c0c061440040300c485004000f04039400c400150f000900104000000740e28400205411042244a10040e220f890b040841d00c0a0300d00355101e00021418500049608440030580c4c01e03007030f2508001008011526030910080d0b502c2d14101809048040c0300030400b403409010b180d0703071043c0c407269803d41800e4650b44041c100c51545e08182c0c0c049814100300607045201a401350f81040c0c1200c01051050700c0c1c03900c018076900c2940a9582038802100c0c00b00d045440c104000e4000d40115503e5000e41418010f40201a1304211688240b00700300100c00a034280d00c0100191080380140080c1c50644c1e11070725201c4484401501c04010941e130f50803600788219032911b440c1d40100560b6804282 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 674268219 1250 674266969 674266987
    0x70804120c0b0a0206010509091c0305071b02060403030302031008071401080618070e030f030309010c2003040e061201020d050601030c30060503030a1e051204020906041d03 76
    0x107407641c036049441e40000030044010615000651203045074005c8078941900d81d106210745003040080c600610f000d003001c00031030b00050f40540020740720b004130f595100c08032600c419401c00003500c9120007a411840801052002c00d200c0d40065600440e15034600002d260384003401850f04000d0b51010302041e9910100105a6911004454100d030088506140090100c014294101f001500c514203005803005031005540303090040036010b0000001740d945038035141e584640a072428548180c0010060110726007050302d120b88449180250b08011824541001200840f41b00302038582580043d4010711201c0d0042c003400140340001107a0030202e03490428000140a907801d05641a0510034000c20600c507400b02c1d080014600790306580d905100351490030080d401491150042e54042c04000782e8401500d0f00443c400055400300d030301c408a0603e0351a8125158019502d4147d02c050b40140440d001d440c111500302d0700400001c10001d03150481d0003200758400702c0341c02124a00d42010510040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 674269469 1250 674268219 674268233
    0xa180e0a0501060302070b1303140c010e0607090609120c0b0f0d0608030f0f03060f030109231609020d0b041d010e03030c0a050d0b090c040326160807080412 69
    0x30040229007019801c02d8100d98407d080400c000b007607540440b01c40b5101b103050511803001d50200440000203aa42ca02d55039184030302a001352840c05901d0300c20398000c10b01181c8100c0c020b004850346540c501c1d01c03207420300407901045905084141c2e01e0460300b030404a681e01d00b050042c80c0c032800c4055043e17039416450800f101990807551050155800030b2100001c1c1a681100f11030440e01c0c406401daa4036540d410021720614035480c6c01d1905036181102d0001000020940c03540f2035006d019820303036024602510f00755201c99102d00d0000c0c0c43c00d0b139a010405c00020340c0143c041c03075010910210764007811b080030508545504410340c0041c200c01586402d10202840b640301c200c041c0d4170155240d860600180102481000140320801c03800141c640c00c900800d6010318000c4078018003554690800102c3d039130b020340241c0800ea039082101c5417560704031013a04006482c9104000c60700d07401c00120110b1070308160140881640e120100700a0343c0d001451000003403000d840703001c0101640d0042814101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 674270719 1250 674269469 674269471
    0x1305071107030308160c06060e01051c0f020f04020d0c0f030b09100b03340e0d26041820040b12060406080d0f1b170a180e0a05 56
    0x2003100c0d00500c03814404a98001003503036100d03001c0e03000c0c290300c810702190407030711008044005840c4074a08040421040c810f0000710381210001c840301100c4200c900a600040c10101c00002e00070100d5070044070050030441100880880e00030401400c2c0b0100546100a035020b280706140050340c00d540c378070340c82074141c1f20ba40354a82082d200300c0e00d05e01e0442e04030711507d1018010064101c00100000f24076108000212807001200040300910301c64500102d04001c2c181d062490103d06961056025824047c105800180d0401255150b00c0102400420144220483c4c02c40d02c890411000c5102c040c0b00c840610310124954002810b000d030880d5003402500d080c19140b1240c501084104074540343c0f242560301000101ca09400c194440c480080c00502003070b8040991401207550912446810990300d2481d260345445032000d2403050840045961000c000041403c47d021880403450f14402d809060160083e003050580c481c4d020f50509070a0920b54031220703105140303004200c8001803500030a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 674271969 1250 674270719 674270747
    0xe15040b1e0a02090411190822020111070909110a09060f1a090a060e040e06061507110603041b060302030c09090907030c12031b02030a0f030905130507 67
    0x280315041039000c98002007071409801400b95940100300d42c805640c1c1c542c00100040e41c0d9603801d981daa422000c0d00100c4e900003000303040c0840c03c0c21001400054066440a6018990041d02d41d00858140c0c01541d0802c0a00e140b05404e114179078000c500d0b84443d129642c1b01e00c2c00f4121150310009450100480d80e80c0c5038004042d09404c01348200049280c6504e114241d0b681c07908200c086540100b43c0341500e0003841c0c1e20a03071100c1550400909180c100403c4018060141c1d81800003d401000d1550f07034140507102550000b005002e405020807a80c1d000e40040c03071141280b580b90589801c00200590030030394040e04c4102d00203442c9003440100045160042026003401d500354a443d4022900720700903100041e000c0c0d800100003c440c014280002c2001d141d110701c03604049c0342c0301ca0803108607140000c0f046000c24103e001d484c07155200b03280c5000f20326500a0040c0540c0f09142d0f901810350011080440602880e5a80440c05036980c1c00d40b0840d042080030001803510f007540c0010252a009030103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 674273219 1250 674271969 674271991
    0x406051008030d0e2803121407110c090c0a1b0c0602062409060607060e010501141005090a03020411040b070f03031406181306060e07020d09080606090a0e15040b 71
    0x701803603000141d130317009031035070b00f500300340110045850201014100c0c80c0502300700707122090204849143c0148000c01c00d00d40010440308081e84e0f413014400c5d04403050750050310351700e001c0c0100047d0340d1052207000104034000c40c40300e42540050352041080e000c04d400c081c02607040502040480d404500c2c0c0c059040f910810520381d041d0442c2d0200301d8011020300564020940004c0100c284181a0400126a61003800030001d03980d5506e1070380500041000034500c140000b26540800a00c20400d0710700128000340a4540c480c0b13141d0802000b818088104220201c2c2840000782405c0c883e00600006409400b10041e14032007494020100c400005240d03031000a84010700c01e0f903881d08850105006290302070071b061a280c2e00c0d5a000b5000a660340246980e0500720040b44854004400c540944050b03002c0702d8005605500a8400350401d00510805a121100182c1e4a1a02000707180e0040e48003140012900414910b150903c401a090400c1d141c525405000811085c40709150344402c0c1002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 674274469 1250 674273219 674273263
    0x3100e0f0c04062a0f050105102105011b1121030708040c0503071712030702100b210102120c0c19020310020307020d0e0a0b030406051008030d0e 64
    0x103104069014900548041004845010000412100490950100d07080300000c1084451034003017084038040004903081c0d402e00380891042800412020141c540000005c075500940c1d80310003488402c100e109907295900c038100c00c500c00c4542c6038035a030496050740d0b46800e61034000e0310103882d2281d440034110801440e48030f210010301c07100b01902d80224082c03605101070b0304c0318100002106a40d402c1241d150240080018a0700d01d00e02c4c0c85000b0004e400141c907890300260340b409055000c11a104d50140e009841000101004e0340c1c03050090380790041c0803081921500d42070031701c400c182500d8030100ea0350015600c1c1c040d40b03c562035150701403415030340f6916181c504500541c480c840c2000d012082d00c915013890045603010f004443d0042500201151646440c0c035000350b941c21144200700c0070400d25007a26859040845000742074800c8488070300d00c1d41d00d8564911000741801030a82c82c9032a00f60b100480c00510500c0200603a855130100810030b1040383e039503d410704a601c0d4440b40058084c2c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 674275719 1250 674274469 674274481
    0x1201060203040602070501080c30010801021b15180319050d050f0103081b0102090d08070c080304030f0308070e031b0f0108090d0807021501060306030b0c0a0905060f040b03100e0f 79
    0x9c01c6804815800c17503c445901084c840301018154030342e00c000310b01680c0700d001003a241070541c0034043c6400c89075201c440400401c9c50a07500ca401403c034035045101071200141d2411201103c03c82d0fa010f2260032a884c01368a2001c4043c2034540009600000e100041c840d005e004031409010f800416500c0b400c1215459961800240d100d80110614802d500ca4031842c891072087d4180e80c481d80c00941100e250a24a107002011603100c89812694225034030004900f0320310010548060b65840702043c006c00103d42c40641703103400700515807000c00141740d00607002074405020110303040b0701c01548000090481000c0040048000c4001810042507030100300c401e510006a0004000e02405c041080d51940c260880c20004030b1281360720400c0b182000004c2580d459032204c0126402043c0c8030300c503619442104840e5201d482540d4000075992034041c001d03450120020505500802c5901c0e103410b0303540c41d07822130b190400c0310f08601808100c4402c00643c040c080c4600d50090a40440d50352901d010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 674276969 1250 674275719 674275741
    0x307091104032a0306110705190b01080609060601030b0f0d0c030c090b0f090a0207080f0a140708030402121f1a06040503100b0d020a0905070f080105010e1302120106020304060207050108 82
    0x252001400700c60311149503021b0101a41c088030310154001080d0307000d1840300305000303081104101e41190852100d01c000034040d40c2c0422401d0042e642540a400d8030b448100044024015a420aa070700064101d03680469954a401e00e10a26110310032000c1c0341491410401c1c0c401486620482041d8104084408160360b10480c0004092003110140a07039120001034200900408800030044580001c010f84d920802c10098124004c0d031780e03150026248104500c02550049500061000c402400481c0051404440c01480d40c1103032401c844003240c0c0c1100001c0c1a19642c0e822224681d6501c100c4440c003010100321026251055961b60320342450000404d507070341c000c02c4e16044095959102a55107544001e4030f086000d40080222220035140c443d01c8009000a580341c20108850240c5401c160340900c070520704a40058407851121003051091100440340c65544000e1281e0802c40162050019103285010b0041d80e0300460b122818201d029107004003540009050010007400c02110043c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 674278219 1250 674276969 674277053
    0x50705070212010e030714161202060307030b130c03110a020a12030e1501080c0901030c090207051e0a030f0c080d09081611041109150306030709110403 67
    0x10599105841c0c0e0b100c001082d005003107141c0081150b0000141040500010010701100c40c0700f500c040d03440c500d4000a0610001402d44100030707143c0e680758503030350142c40c00b41c020b0760b4489007034100800c607100704c0c0300003600004000111490361503540c00089500340d49427140e0610103030f1940c4658603000c4c8085002e5510380d03c4d01d40080000406ca000c040100344240c01c00703592040003804480c0c5001c404114103180e80401d0181410740e1080b00e80044403841d180c00000e049076001482c080400707041044180c069806900242c5451082600b0f40601d403072a426420720121a41014110f80f0015190041200b90b0498048040048042358080402c0c1144201c2e08050f0300b0000005128042e854921464059a0f00d44204184c1c161380080500109074495030f00b8003000c9808001103400e0b0320300c04504e4006c40c0681900881010700c00c03595030603c0350040d6000840102107907011a0383d00c03a00403e0f40c1c2c241303144507003100c0c0200d002c104105200030001c03402d500f00c0038458228298901440724001d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 674279469 1250 674278219 674278223
    0xf050102070305100e0a05160312030c0f08130f08040501090806162102030a0f05060409080d05040305070f0501140a090b040b07110708030702030706030209060409150b27010305070507 81
    0x683d500042e0300c45c1000700200c1c0c1d074603944082690269044c020001088000c548800d030f80740121407400aa16602c24410a1541c0340303c0e031200c40b001d031080e900490f14044001c021103407601d0f1004030f0790041001064030b002014428240c0d150b549040000041080601c4d6112903800c0d4400c40a11800040580c1d25540740002c51900c408003400c030703500c40c0d001901c50080c0105401d10000510088210390f0f04200145064140c0c140810f49540c0d0030301048481c1c40c400030300394400900100403082c04580010350018001c1c0f4010741081c1c42d54541d0040080c0142c0d04803030300da40d42d101e410b2070850b94081d042c0e8820755049080120b4903094440000205004000601803188140010301084c001d80c1c88030084414101120190354030781640036903982c412141a88a80b03e11000081d40e648280200c94289001400190800303150000c680040c0201c00341039080c12042110102e8a210f1300700c00342c0440c46410301c14814410341c13013501c481e600c0941002c090425041c00e00700301c452500102101c0c0348507 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 674280575 1106 674279469 674279471
    0x2030c01020c01020d051c020a05071a13060b041409070e01050a15080a1b03230c1803100606020312070f09180b100302040f05010207030510 62
    0x1040c003403038550050b4041d621403585d02d4800c6014151000d0000d201c0c1040180c640300c0c0e072041e03801034486400011004030760f460030b000c1c0d40101865200b0f0030101031141030034250220001281c0101c0041e1200d501c60440c0041a00d071584440350903101c5645917901c9040440316141c81d802d451040c650224400c80002c00c04e880d202d031281084a040c5018085d07044d00c5103009441c0e41000404681c03013280d0700c61054880c0344d0a84641201000c05580006500c0362456003058200110044c96095081402c100050100fa0300d04441554045079201440c00100c1d60000f40741c41040c1e079145c0070840c24210001800364000015000404c01c00110600e281c0c0c441d241111414103d901803000919015810003410200368403c81d0144403044010400c0c0c0c1d25040410f508440029861000030360015041208044460000303010344000d1000c0d15a0303500e103803510380d62000304208500c022 = true := by decide +kernel

theorem cover : BRFrame.Cov 674100719 674280575 := by
  have h0 := BRFrame.cov_init 674100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 674100719 ≤ n) (h2 : n < 674280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
