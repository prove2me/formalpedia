-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3232
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:03:14.277773+00:00
-- url     : https://prove2.me/submissions/86ed40ba-91ff-4c7f-b403-e01e382b04df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 581115107 ≤ n < 581294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 581116357 1250 581115107 581115163
    0xe010b030a0c02011d06100605030709120203030f2a01110406121b11010e0d1b020411160b0f0f0f100e04030c110a050a0510090e040c030203 62
    0x49941240d070303210002510261081c410780c05001101099641941d038505001c201000214100f48540401510302035640c7d181d00e0151681d00059a81c1c1000400c515001d00c91070007042000907025000808990a110441206200607800f142c803034002c280d2b4040042800140180e011988040440020b001c0005060300ea2100c3d80102c0c4102d40c00c1100c4c1e07541c80081c92032607a04c2124102d49203031401968007000c607406080242100d0700b41c0740661802c2c1c0403c0380a100414420004030a5a5800c4041041010707611640040310300240d0740704c2d655190940300304a0000003070400c01c034201d80d00054400c4906050003900401400011104207050070018402c0b0750342c801d0740d80804a0b0b421840103071104944294403051700d422110702d0303101d06000d00c0207054003c0c80445070b41d442250b03d920b0280002042c0054024184078042c2c00c00c0500c8414800b500d00b90700c2d01110303118585810030307107541e03113588a840e01d40e0281d40645a2105200c3c0500541c11f06004c401400c14400d0500072800303803084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 581117607 1250 581116357 581116379
    0x301d0703020121150902070203060f1b0306062a0d0801050d0318091a0f030d080f1b030a06030201030608060106170403030209030313050a081f020a02120c03130e01 72
    0x20000284815000c09103e68000b101e510510301d00b20000d4991442903110a406002548405e00aa00c40e2050070000303403140f00e219107107a10540480c00264004c0c80c181c4840040c0380c0000d00342c540c1c0080e0a1140d20300d0203603040703068000300100407000259821070440450408a50f0708854040101d640300510180d142e5420005820380e05140060540b0900c0c0c401d0940703154150001344a0303034107190215604010f100a90300b42040c04030f440034614002176003090743e681c1000744103501103503445000a26103030181c044140d011f00c5174021150b08142c0381040f840c0c6984100c80c10850b650741d6610074000d40d64548244030141900320000c218a504044000c0c146a852025000110440c0c0b40042c0402d4070980503134442000c0a022217850310301d01e01d1109401283e81c010725004c5d8441604c00038070f8020008030240b2a03008a04692800385004441c0c20281d40030600030001d51090b04172201c0c5a03400e80b4000d10014165034080c54540005480803406c0e1a803a81c000000544000c2c014000c0e04a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 581118857 1250 581117607 581117627
    0xc020402360103270302010b0a0603150b09091503010e0a0308010810021c020913060314010506090c0f1b0d0801080c06031605090f0604080d030609140403301d07030201 74
    0x19912144d450403a514049000d40310a00017203400c40043e040016096800d50811010505484440510f40d5211040c65005020b00c0408a5006110780007043c1c03001e0705180000350b1a14040d002042d1071a1402c01c0314504180303100110002010390780100881c41c800d01c01d6061400900c0d04c02d40c030709480000d5a9001000500550310b00e598005152070b0346070b5030980111203205c40548103114690780ca050402041c1e01c1c26401a02035400c2100003000c0d4030788202e0441c0b0960908400d0380c100b07101c2c901c0350203080e00103504d00414610800304c006846c04d000c21031540e6103442c2d0740e11082c2940c10110914144008100c01a003d408288103012500014164007500e4020b6864055250380380d140c0003c0140301d0042101382c1000c4005408030781b03102d000c210000c10044c41c0d2030500205540d03130080c00403642401550207080e401c4034089000203104d004051810300c02040c4041c070100b003400c2c02d0808000d00e540140703080d0b5941c0d105406031003095282103010560000140580d54955000a482c20f003c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 581120107 1250 581118857 581118911
    0xa15091713030618060f09080a050c0a0206122409070807120c11010b0a03150513150b0a0e0708190e0a11030c1905010c020402360103 59
    0x4904565504016940741d402190091418800844000c0a080c25290540011380307004d81046204451030005010f07282116900c100301c24030f13010000c10112460f800610911071180078020030340f07015030b03114800341000c9044560081868144207007424442260346000080000d03440300104020303501c241c00e084d444a541e05166940e83d4400004541c1d4035240c00c0300c1320401d8504100c8600803544001c5003904d100c80407008110b0807070060304000e84081907110040140000e0307a000c2c654508940c10280d041a41d10f01c040301c0c08000e0b40e4500b1549001000b80c90111030b034030381021034140f5188245400a250240d400b82440c10548002031081d28024010b8502403050794031540020155480348c8000c1c014441a00c0040155190a901210440b65810b1080c4515240f029003454521142c402c00302d40c444001c2401441d01c401135428116020099038440c0d8280112030390959143e002c17a903168001440104008000189545032081c16800a410546040070084491200e60184610100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 581121357 1250 581120107 581120153
    0xb04030b06040603120e091005090a020f04260d050405010503070305090f1005010f0801060807030b07021905010504020405010608150f0f1f09060c2d0b07020a1509 72
    0x2455801141c00f8285651000308101c004030203000b00c00307600072010014404201c505004a8840625a114041031405919400b00e004808541c0d40e84155008107003100c0018122424a13958100d405203a40c0072460440105510760128501c0400621101840c0300a40c104141410b0a09000030190700004004000b07251740d800200315074000c1004140c0b038403c003480480c2e0b140300da52440d4402401c4d080c41103034190071035481c01003841034040c042c00c0c050362039000c014040b003850b64440016058000c3e1030a025030107030307151000d074803208403840180d20f600403030003c00d4504191040c0801c0342c9050703103c0420024010700707002d00d1b00c5050f0382014403503078101c03119070002c100100059482c410800311585c2c80000141e8040034054039444061b0040300c661a032900c01d560361002038400d0780c041c0d03c00a1215600c117000c01e503c00c00580800d102151020a1031454030016510b12807024400d4a001016a1120b0508801c001541994410b070240d650028804610207694000ca0218501030203400b0301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 581122607 1250 581121357 581121361
    0x20a0308010501031a130b010243080313030326011a0c0a050703170f04180207050d0207210803010501050703020a060f1d03070c14030c1203030609010f0b04030b 71
    0x100c50b11700a0340030941c00625040000e4485d040304030080058099641c0507014004594044c100440ca00900c07809505e0f2214800c0c440c042d0741d201c00c403050007250754161a10300c2e00c0441d61100400207049942415800c1c12122815400e010300b14882d0040340d0068540c05408020018411001640c11161b270001001029903c8400700c0e0090701030f0a9500696100d0300e04402c040c4040001c068003103c0c011826100c103180c1d4100601c00c82e101700c034009040d20500300310800c01c401d18407030850358101075004010305102080e581e4a090441c074103c910010b0b0b201d01c0c001d200404400e5901e1031315801e000312544400409076250102404140300e8103040c040040b80c803006240c001d000400106074450000c104d59108407002e00010680c1051030003001946158035141d460001040b10a210303000b1200341009440c0000d0f4032031405032154010b0f00350007000942e0b0044d445604076a203494060801564a9213000c0c400c0c0306500d40140d110b0100300071200020060301d42c25904480580341c11200404d40c035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 581123857 1250 581122607 581122631
    0x31b030709050418240b03060c070219030807050a030e0a030302102309030a090e070e0d020f12071415030109090204020f040b0901021221060307170715020a030801050103 75
    0x44441e012000d440710b10545e0841c0341c1090b0608141440e500d00721820420301c99403806241d82c500044902028240702007164a0141c94805240704020b65030f00c0c064401d40d07880345d640202c0d135007000800719065440500ba6004040d00500303980d1044038165400440f203803031501c00035500d5010f0810040395595a061038a412107032421641409035489146080700d09241c09c4c103135aa0b40c441c0c0b41241c0062560040810013545100107d0300480c0d8075510311348168805420800400c1505204a030300940350400400f03191a03a0780f00210051141c0041e1210a14051720241811201001c0c1e61143c0d80d078407182450221000709580c156031030031000060b14105840070030001e2195055040345428042000115061250003c10a40c10280e081d80d0f4282c141c005031030f8140c0500407209482420065107851480100f40c040c550040004040f174800c0c2e40d41c3c1241c01c0344040c5404415034642c000217030502503450700180302c036132006280c40201041e1a01c1d8400400b0b451040c0212030405899050a07820 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 581125107 1250 581123857 581123891
    0x15060307090906020906040b0a020d03090b0a050703090b0a060f08120717090d0b0402130b06040605090316090b09092107060914010b04060902030417032a031b0307090504 75
    0x7182c005070150f503071152030723080405c616003281280740018429003c50300344040c4a400343c2148180d001c0003031f440d5030300d4036103885014107801881c007001c26a440c0300c0c0401007912040b90030700070640280700250b1281002302282102d800c0382c1004200741e201250041c0c3c410082811920b0352904400e18182110070b0082d508540e10401c0700c0350398400c402039192428003014241c40e6002d40e1084904d044000000c5021005540c58909443d5120405020800c003050103103000b041c010900030305442a1164680340300c62111041d400103560b00c1d513103101c0306290303040540b803168121110400501c01d042054400c050040c0805500c04001c080c08103080040144513000500f04551200c60b480403000b0703201c0e00c40d00802c081419280702d181040d8000039034181910843c1d0007950400086410001c964040301501c0d0300103000001600c03064682051441c0340c0e4208407416110340d5851503540d0905040c000401d0042444101c41c0a408009101c1710607000643d1030104c40c0151000300360340e501c0d1034034162 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 581126357 1250 581125107 581125117
    0x203070c05030a0807120b030a110a05060d0b040b060f040911040905040501150609050d02040c05090303120402090a230403031b120c02070b03011a090d0605091506030709090602 78
    0x40c80c4400f05510307611a40101e4001d02c503041c1a0f941301c208041d03020715603091b6510180c400350150406c0451b50b0102e08201c1040e05100409003d11076469039810100e841d0758403460040e540203039141d40884e40c3d03190502680c0c2003958101c80840c140500080483c85500c0389108010f00280d544068078001e01c0404203840c001c0503400d1080086180c9401c04a0290681c00e004a1b2980c142c2400818180c0c022618041034603406001c8070301014081c2d003408010941442000244402403010042a0380d081005015140310b89074002c916081910601c6103105014050480003800d00d01c1ca000c0c001961038508182040300110441181c8071800c050300105a0540e050f0702d62455404d911079041d401ca00b001380c0001900b00108401e0890040481e00e40d00c040c080c090769020204010080e06070302c00d014032822203188850515107000c64001400b45003103400201c0c0d80513161070800456034000d003d01c0b000090840c000b81151b00c0c100c0002501c034072141c003400d007099580d414240b06000c801ea05580d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 581127607 1250 581126357 581126363
    0x6090c0a1205090d021203010f0603050a020d0905030408010f02090607030f0c0516061803030503011505251a0c09120705041401050909010e12091f0e0a0e0c0d0203070c 74
    0x1250801c0c11155481c3c104080740c1101520841407003e1000c050386d01100d0403110790040c3c00300f034113041c10000c80c00350034041c01500303009400f070010345d090340400e1041354a280d1150006540d27561801c600d403802d590f08050080c900d2481441040c0003501c45a08403600e0a03032604c0c040c003030f5845c100c0d4152403000d00b4080251043c0b1070500402010090180f0704402e56045403283c440301414000d101c0e000d0156404024001501440108200e8005865001c000109801c1643c18030b103045010304100b05a80454040381c0e8540c00314003007400400492903000301202580b01e00c1b20b103000c0ca228a05481405115402689610700e5242c1e00311040c0003100261000400c10300044981c030002c1c040e50f18081c0542031061089030081250400305208011000a0200280c10000100042c400454110141e91500700300000c600c00c40b0841041991400d106454680c0d0300002070300c0c0300340209600d1641200700e642581c641402000c1d00a4802d030754040e6a00080035a4955802c1400c591844000c2401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 581128857 1250 581127607 581127611
    0xe0f01120f050a0e030c1e030712030203010603050604090f02060a0306030b01091b0215040201050a1e230c0309060c0102271c111201111c0f0506090c0a12 68
    0xc95030852194206500401500e4420b00c0800300f0000c80310b03220300c00d5812516240d0b10420400103104047c0d501400e0b0820fa00c026030f0304062a80e2150021403a1041d0035900090340003005001c40c035050710515411280903075080140501580d0342060503940306074064030500c3c020840c11040d80c4660400005107500403076000712075940e810740c0409010b0b82401d50580d201505e9515070254400649036030700171240d0750b0384400b5441c0d070f030015105540f042c81c124040081761808031504c4004140c62100070017042d9201541d0641144000384014082606d030745a00d04100030052548400005481100000315030341595130b80440315050082c4500760052500150b0503031142c00c00c4860442400c1d00e6401a1540e90102c1c13405141c0c2e8201c0d4040d071500070031221072450b0588190610301c190404a00c0c208000090076048410381c034140390070124040b10825002442c510160096000e0140e501d1640502800f00d07003080c40029205181c01450030324a501d02044003001d25111354049841039280200c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 581130107 1250 581128857 581128871
    0x30b03030f041e05040b030d0503040611041d070201020c1f15031b050301090312020a171f0e15130b1c05060609040201050307120603080d0905060f0103030e0f0112 72
    0x200d1000c0020f501c1c1019a4440ba1000c005001d0406014115003a107006018107507222840000f511190000b4100b60703140c1c0d0780c2c0c0880c4042c03410140010406041104c9050745081d0188290612012000703241104590062200c81146080090f9444052844518402412040340c0c010f030004c0c01401d10403064034030703000030020600110f00c84502c214409440070441040e1584249070030b0768810341001303000800046052008840c0e41d80039000c11411032a00c03010400c8100914403100b4000d40f071152020303203c03e01c0c4c802c5510010302039800074070010303881040901e001c580c45000d0003c0103842c540601c00120a910240107181c1c480d07848640024160020340f01354070001100d900c1481c2c4121468458400824020f00d0549003952085905954903483d41d501c04008940b076081c0282251000c9440e101d002c00041c95400c003801c040103401100041c42080d5090071450300401800c071f442500c40080060012a9210060155014080d150500340504420048841c12002c41c00342c8211417074155 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 581131357 1250 581130107 581130119
    0x60c11040903050c0f16150c060c031a0910060809030f040e06120c0f0609060f281701060309141e011a0603041101090e070302030403030510050d03030b03030f04 71
    0x500340d030350f8420040704c40a45c1d01405680e91070b00c070711034808010360702184100310150f11074800e0703001102c4500d081c0340001c1003a500c105c140c0d046080b20a020a0311100501411200070f41114140c076421078082800341852005901c0100081c042c2c03a040100950005a41000030022164600c10b68401c59586540c2e0300152031401109a4082d4440c101b001b00d002a40070300010401d884400c01000d60308007194000c100700860f4408581c240d00700b8000d0142c0000b0000c100043d0400c0c5054500440104010417000307a0190881d80c902e20600c000c943c450300403950a00c0090307065a529040000d951291400c141001c5403031176001d000e10b4410406c00102003034a000140040441400c001d101d40c1203141501d01c103081000da6002e41100b4180001000714041c170001c007804440604001d08159260384401c60601e50031601e581c00709030000188420154107109840c0d00034402c92102002508002c00101080248240a0b0405440c0c40440c50907a0303041c000c40d074500704048031950740c45a444c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 581132607 1250 581131357 581131367
    0x201151e1a030601031d0f10051b0f0306040b0d080904050106320408010908120a0612030509011e030f390903080d0e0d18060c11040903 60
    0x48203000148804510014241000166034540c038240c24680c68299982c460044009240000d0b03201119011842500349509081c0005107007c0d0790f11021340a60305026840906030303440946034180018500448102d5030601c0001e0724400440c68001c0c5580703403680300008024041401c0c520b0b07402a9040d1121003080b030154010402200306070303010310a9070b80c2c3d020241e41c0260300b0415155100d00c2070b040c161401d480c11031021403080d0018552800c01d40c40b0340c00d26084804481e012034902d40e0009180a072804410111648240280d200303005e00360400070418040b0344440001018864040340001c17050703000f10711003c8040122000640c01c2d502d50103000707003d0700814002c40521803400d20340781d0008800c88058000e08841d1010003100d10484441f685143c69205400004c1100294006c00060200c100410b5862a08c2c070700428044503144a03503042c12601e0320b0407402d001803c48038610510170710303680204488080c06e280031a0300c4681030441200c0e41c24207041d5482071030848148200358101c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 581133857 1250 581132607 581132639
    0x60e120a02370503010f05100605070501150909170903030d050c1b010506010306080a02310603061a03010c12020306030309120a1e0f0618080a02060f0a0b0906060a020115 75
    0x4074001e06c0580d18540c542d40c00c60340161380c80315041e41f01a00a00c44030740100c0041c00d18501c50700000611300350010320b00d1084080e03a048048041c0d141c660400a0000c10862020480c0c0b14030f0240b0724100080d00080d5882c07080c6034540340704130788420004442590501c1a62182058107140b000e4170003000f40094000c0c9403c07251180801d1420b880480d5042d40000d68204090380501034400e95400d0615130319400f21051203120301d0f4100750038106080b1000d07029400040d8440c2c3c50100345c0030814040039090491a5080302e011740e142234614882150f002c0201a0045160100142e480d150080403905611030120700c0741c0c0000400d90000211070300000e83c042d0312030140c0000180e2800f044000e01544210040103001103800c00f82c064041400c2d544000c0c007a50707484007003060807074060340e0710215074100160800142c4c0002d0100102c0120390b121050b032060f100c00c03040059180007800035214880c003502250003150082440d011460007580200c1c140042000905c544035550300034042e440c020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 581135107 1250 581133857 581133859
    0x5010e01050118020405030304030b09070f060203030f010b0a02100b040b060a1d04020306150a020a0c0e04030f05040501050d05091e1e030304030804060b01090e10060e120a023705 79
    0x1800310f02d259800d03403910945040c0e80c4000c01131803801e8510307107550103c5003001c0e002c241c0e1801141800034001c40d000c101c1c0002420700e0340196440b441d280c90241210f2005a10500c50384a0401ca08550158049007858411542c0c0000003800c1c10300c000494014901d41d0711035900b001c0005040e082098000c9040c148403030000030302001048600040c00141e00054a08540005d00711070620542c07003c10025100700070b10740c0304842007080a0b8403205101b245d140c0c4403030400490082400706066100b524045801e8180c03d100b4981440d2000080c91485440b0342029000e940380041000d45c0800d0216084d0000054003a801030108d1612041d00c074194144107800d2400190502c0c0c00c181c102200703517031040d60141c0b110700c0c3c6550386480c0c19001e440495400c504000208502003204003201c1c683e0350144d641c03003500b04003050900c04003a01c150744002c00076125038410303851046420301c006200040e07150b0540380030040e244081490109016080c0f8000c5400714107c418054400c00798030403030b0480e40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 581136357 1250 581135107 581135129
    0x10c05120f0c1612021c06020f030601030f0504030207051e040507170f070504030602180910090e0a0b15030a0f0b1608060307091a09010905090c3a05010e010501 71
    0x1d20f80c901182403d81510651208142e07031640b0700058a441d0111010009007200c00038030003400e954800007240d00c80885c1010490010043c44000d5078548255409000d03588000c10141c1081d4801940c1d80000b445403600c00c00c544000e511503950700342c14011003404040d0040c007860400050103840b8407164030742036019908280002e04c00c408502c0c402c2d4005d0307400345c55803450141503480e070350082d601030040f4141100756540c844209407070740310219124240f1010590040c609000c00074007601c04a840101b00707030b44240c258101081c00c4110194000c0d00500c40700c280203e451002c02c0c10281000800741800b407042d10280b0a201a440c8414403c01c0c2c1c019804001d804811000d80c0e81840c02e5841c640c2590081e50280f080c1c418946c80300d90501401d0000c07808207080704000942c00e0801340c200d2410540c886d81030054008082180030070506040b24900328248041c1c0b2440724054035050448040b14910b400d000300c003c100c81480300896009070003440142e001d100814080e14084c814110214 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 581137607 1250 581136357 581136373
    0x4090b090d27120c030209040b180a021c02010e090c2101081506280f06020a030c3e10090b0913021213030f051602010c05120f0c 57
    0x2048602c00c8032403050051811924041c1071880703011190a144004541140c030110000c03000d03945030040e45202d14800c0845480b94a002541c0c2103000324040c0207503c00e640101151401641e0b0039581c6000c1954104140d40910a18001210024403020302d1940080000c400d02000344694030040003c0c040c04004c11600780808440c2d0344c600c01b424800c0c6000c030340100400380d1030b02c20702d807142981094000b0f01d01100c01602c2903040d000114020032002984528001c00c000e000d0b0341c00a070780d0050903d030015014750078540c3ca01400700d95000d84c00911521003150040b506409a20803640b66040ba18003004018004c9120820105860381609209650007a00c2b1900c0c80d10403a00b800c01c0d9820244a03900b0102144103000f0305085c0b82a40c0c1d40500c0d000d002c81d034004103894007881c2c815515070440300c8408800341009000142d41da21240d007080710400007980e03425080d4a00614240e42031030003c1c0d074885181421410800740c4d503080d421240c0b00180545645400001400b0a820740500f40c90f500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 581138857 1250 581137607 581137637
    0xb090a11010c02060702190f0b0d230402120f011e05330d0f06020a1d03030306060f1902160b0c120708070b040804060305010b03090606060904090b090d 67
    0x142e100a500001c100081c0c0c0050905900e80c58039002600103401c07400f510f40648201000c40782e000010507000102e2821150b42c124010700080c11347c103c843d2070784044161031040c00e44100401c081c2c0104882c00182403c8402000b001c0440c1100c403000300202d402c50924100030496600c041c0303250a04001c0452380507c840c0c0001c120b800201140101600c0e41a00c4203215a10843d0110350b01c80d00c1d20403000081101c00009140541c8100c0d401662401512001707003240070040440c034440323805c4001c100082d480000807070ba045141103404d192100300c0c00000d4120362150000d00b28440344010686880150000307103a80021380d25488940c00c40d5250300c25140b69009158003050564000e0880441e8406100010814a07010b20001845c18540351201c0c0410788081d00d08031105000000c08101107907041c0725445c007410000d44403a00d9070401c21401e50755030b81d001d400a0702c00c910000c0e10703000d43d035500d60000d5601680814a80f00510701a040c44c2e07200d103194201d08001c104500104c61300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 581140107 1250 581138857 581138867
    0x2b0506121c080612030f250c090f09141e0109050303040f0c030507081015080d0e06090a0b22060801030308060102070b03090303070f030b1c0804030b090a1101 70
    0x9005410303803150244160035004880b00d400142140b0b81110780841c0c10024035005000400c1c401c0780070000255190240000694001501180c00d092800004800c0380000da001c0d440804076100d00700c002c200403030001e071090018081c681d001422000c03103407990700c1c00c13000c0882e0005075802c582c1901d980e60301c5403100141c08d0b0b8a00e640c00a201c0d4004100240000e064400c1c1460aa4010100c2c442442d480c0d6844c2442d190302c50300899050f80c000040000100200c0c00b03648008403244003840d000b540760201c126500d0b4034204c041c9062180750720101c6415100e44042c0c48070503000900a8144a5503a11090404e5000b45410a000090f403800012101501e45050007220303469034603101c86a19544048581920103440e90f8114018400c00242502604010b1401050404003a41e80d070b05115a0150115a44414003028107003071204e80c861940d03c02852110080d640a960b121840181c0380c4100e16208a400c010040341c2980d0a00c17032502d4001610311030103482010001c3e5400d03075280040d60 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 581141357 1250 581140107 581140123
    0x1809110405071b05030405040e03121b07031d1009061d030604170d0c0306050907090f090207030c020909060105090f0c040302040b0103020d1406210c0103022b050612 73
    0x404145844443d00000501c1c0c00c0e0022944d028a0980303041644600000b415102000051183d0764408542c4540c641e1a0807100d50300300b080c8607908a03030042c46401240c02402000d00181c10f0040040200f50340c0c00c50f84000450001c4000c281c0440c04c0c88000b0007401080350b40c0038100c00642621007504e0892040b50396642480002001029035540c0e0b0f80c0c40c1d10a1081c0e00c00901e505e4907052040c004054058021995078906903240428580d090900f0321100d0500244503104002c07160008009541440180c24107a440b01c1c1005030ba654500e040554145404500013500022064104010441e01140d0103040c1d80302140c084500380c9030516050f14020f010382c0d0024080b041000200010319041c1c0c030140542d0810305003d802c104d00180c01034200c07508460001229110307002088458a08034482c0140503100c0040340b00b21540461134141e0300d040c0900b5103414180e00007101e05098004040392906042640c000014106803900380c02c000d42004e07280305d8003c00c11030358240440711012031010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 581142607 1250 581141357 581141371
    0x11b05010203101710020a09030f210309020d060b0114030103081e040303021c110114040b0a090b15180907060909140a110c0307050c0f0f010f080406061809110405 72
    0x300c40d00c40815504025401400c0180238804e400000000141c00b80303141c20f04039030040494061940000c0180e40c85c038450700c1d401804140c9802410001a5111a8500c0c13505400c4600001c1100420300141d640d002c17a91104042d100c80840000b00f08000130b4000c2407012400f07070301545c1c1c400b14000f0042c0240100c0c0001005038000c0103564034002102d09000214038458500347c40a2541100110f007118101e000c0513000c1c40540d001c100c03d03c06407000854115402920800141c00b1a84805805c5000600b42101c6040c14603a030709819030343ca80e40d11880f071100710101c0c5c04500340f10300307590f0380c848040c401c2c000030070300c210400182a00030b482000c00004401e00b019440390340d40c0da5010010001c4803d000782d001c0062080c03511542d000c1000d01800c9101e000117144001c414420000c000c02e949041a218110796240c03040c60703980c0281718604102e241c1c05c2c0810540c07114034003e0080c0440f6042640007000700c0740650000d800f0303a0012981180542010701d4508e0565090005440c0111558 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 581143857 1250 581142607 581142613
    0xd060608070903060e0319030e1501180b030f070f060e10090605070f060f060302120105090705010513051e041407080712020d09110901090605031506011b050102031017 74
    0x3000450b07985c0c0c1221710b204000c0020b0b40d1401030243c002c01d074010551500340b00041d50740c0a41781552101000101520350740c90801e0310144d89410303c03030f42013804c003608940c2d46161200c1034203c8a403010001101c1800b07048095901e13031a00c80704102c5610455104240004000031004802401c11100400324181d90382e44a40459040060588455000810850700c07000b80c0212000480d0152183c400e10401c0d43c407001c90501c0c51070040010000500d0f04100440c1d01d800240305412500150710303000c8403003e090150b10742c0300901130800d5100322548043d80201e01c0a208007064462810005c4680c038040b5001c00c070602b0f1114a480034500d040742c4001c04038604002140c442c5018004403040400b0b0b091001d0319008403006c00300203959880c5411125200c0c0201c8521440c40c0c00803c1038054066182c003040511701c0c1c040069036034050458166400181c0324042072060740b2507480009040d80145140da00048035207403140c000c0d4002c4810306500c4181440c08144150281710a02c0b80609041c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 581145107 1250 581143857 581143859
    0x90303190207261204051006080c030303060d080f0a050d0c05030412080a0207080f030109061d06012303071107050109050102060f091612030f0f20071a0d0606080709 73
    0x43da04582e41001ea900001c00b0312070220600c1080440070b108a11580181000070320035604681655401e800c02e0443da0001c02c21000141c400005880c0d01c00d03022503d00071501c00b40d040142e00c1d17200d5110a02922600055010076040e00140200b400c135050342130812900000400c200c9007400181c0380141045080e46590301c0349403059051641180210100501d0100b0076680d0310020740c854103007106038102c00b000400c82d031941c1e449021b00078000070f2100540000c0c1180b02a00031800108107605004030350700001c9006024052110320b841400d0030040c0e5031b0030300c8840038068618a190702d42040c031880d030380030900b544525402c000310b8030306070010191a1100303010010141d200605106a52040c0306168aa0386031200c0800000d0005000655600c0840e00700184060601035a030000d02a811041303c00c02c590180d400c41e490403102c54a480fa540d80c070302ca01130509240ba0722840010701162a80b48034444000001d050440010340d042082587c3c1d0391050341c0380e21044404c4404617148002c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 581146357 1250 581145107 581145143
    0xc070510110f1818040b18010f050108010902130c020c04020706020702150a02010c020c06040b09010309080318011b270810020a021506100c030302090603090303190207 74
    0x40e0a040207001a690b00308200d0704100b05840c1c0081401004038865680c1c5035040d8200004a001c851400b900c1c21042450641c4503100c2132a0098038200325003070300c18108121360b070082d4000f2040c00382124003445107594034900507000c0c1c05010000d0b4451074007440d005145240511800b00303441002c1d0013070607880a0010400009401102080d64030075002c00c0781c0c1005a80703910620360780505854680e0b0711008800c4c0020b00b11040103402c2410f641c0007401e15020742c0c2d106403d9a0843e05031070042d0b42d840120b140100d002d84640790000b009040c000c07044c4a6040304030100b0001c0324400000030011f800201c3c40300400d5178903000c001400302e605030030900703581c3c1202942c90007086c110b118903001d800d80e504035440c17510141051888403581e02103401d0340c0c0c20760706001c40c8480810721800181581082b00c0021f0030122104801c100780034142000c0d008141c000e805494122030010845510780ca408808651a6801241e900f520100d0a401c882003000d00c6100b41c940f51608200c0744190454151 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 581147607 1250 581146357 581146361
    0x50f031b0d020d0503030f0103050f0a0c1a120f06030d0503060a052707020c1c02011e110106030c0e090313090209010c2316030201120203101503020705060c070510 72
    0x401d040e80c000b0909802907010840c01c000840c01810b10144000031589541011410448407215814058002d0600c03100810300c0c8500300d50680e40581d05920b02202e000e010980d0a200d60700700c1c03c0003942d1030010022410094962544903140a8043c0c481c0729100e15401c90303540c03100311350155001d1400316040c0840c6c10b00000301e4135691003d912104d402d69000d00d03244840350041351890010b0384642008091814940d0244a00c00e103201031586000352aa40082c00c800b1101945400c04006140c03100b40e00d074841c071440308030034040000130441d4a8403030400482880041c080c0728000e100301004a100c00c440001290b05018016070000e00050502080002a600c21005107040007110888040460100c040304250600104020455000c440c10402d080468102c442c00d407507036100030200051307600150041505038030f10000533903036522410440421390182d00038403d181c0311542e1442003070707406900504070725000d4000c0302d40035650382d080440c4502c0344a6009200d600035400328000c2d41616 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 581148857 1250 581147607 581147629
    0x705011b03080f04031103120403170f0a0f18080702100206060a0b090f1c0606051c0b0603190c08060a02070c17070e0a02090a080d0507030807050c07030309050f031b 73
    0x2a10b4040311806ca04002d00745107411410039182540b184c10140000c05810640104600c1144045c45840345446e40083c0302c0360f01c00528400780c0988444416180c00b505a01c02c1d044560f103000342e1a104000c0d828944240d0b00000380490181480c031070785040c65800003821502c108001408030098508107040313413400741c00c59055260400990802c50285550700e01010705480c01c480d01c0d201d4290007606284042e9078850344071500908284489a160800000c05403001c00e4028a800d0342d142c50b900c010034034100a55101d80c030070301c20302501c0b0001c0080100b1150b0441c2d00043c201c4640b0380320070070301104134800d4802c000d0460843d100e080088914040944034051004415070340c00580d0350b41c0c0040300fa80e00300c80c1d42d09240d50002c0c21000511b403400031640074105000041051102e4008040c001c0c0c82070100c040c00744401c400018030041e2042c41148c8196041405170f600644c1c6c0c80c038018081028074002c041c4118039100242c00541800101040215120355500141c5c90031075040c4111003200c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 581150107 1250 581148857 581148863
    0x2309061221130605190c080f090a080a050312010f0f091e0906020c19020f0402090607050a03080a1b2c033301121104021b0705011b03080f04 62
    0x38440100b807070800c0c4020380010000d0f40c40b0030f60f84460f110000e004482d80500504244440407030300c4004180d08100307490381c00f400c100f801d03a40c43d446040010449005a406020944118a03c45080140c044050840000ec59507905003590300c0f1162405000341ca802103103444441c60104011102c46900007211100002a90240411100754881d05461240300c003a1350a680004013841042420041d01c820080819203070751650a540d400a0303070802c98100d10720321403900403805410554a4400302d0302038030781c4001200c040ba00d2034a000382030744a048890003046458404421902e50380085500b84501c140c2c1e4445490014000b9141a802a40d4001c4e041da01e0741d0b0b50f104400750720704001186400a14084005001903244070740c52940300c50201506150415500401c5074058004000719110b5004a41a50b00c07917410300458000d010300c1d03180e01c0c402091701052490303280010403060290342c02070fa61010707803011216100859103118080200010f0003500000c45121118000030f800c01d01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 581151357 1250 581150107 581150173
    0x30a020303310309050a0603110306040207031b0605090706032d111605011d07030b0403230a02070e1005011809020712020d0f080f06010923090612 65
    0x41d550120740c042e490100450104d80e002d0340c14440c901d4480c0941000f0240c81c9030511500c00040701c0403d1500024040b6401240c01151100406016000303080500d285420519540032103400e01c60090030080d551400b56002d00c00002c9202442402040c00c144180d00c00c03200b00c4681c100c4100c84403441001620111030303481c40d0340b110b41824080100711030032101341c0c00b581407038140c1889821103401d00800013903110500c81651406201050396030489401c1180c8009555407800c090720211200d240140c0902c0807918065995141c0304041d2003440040c2d0300322018291180044142c0c1a400d071210071f994070f05054200944d600c26080b000100341030948a25020341d8420540d02641c100c40070855080109122407240030754100070700116081c180c40e0100a1a020240103444450013070109070360401103400040440c3d000701101302c000c181c07040c191030030585040c4440b0030300c2c2d0302902c4107032081280741c01152041c07920340200041d420858018040c0700010121040107524000c92114902e0307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 581152607 1250 581151357 581151421
    0x10203041a2101060309060e06100608150402040f09140613090f080f09330f130b130b03011805270607080609160305090c04020705010609060503030a020303 69
    0x400204442e500800b10b6441c0403031a401ca03464101b0603207164000c034100c0c950020040110a058001c2700008030340d020f0504d418a621006440b0b861303103554030342103070300180002800034181d840f0362490000c48600d540c0800c00044030000503c0541c00030341e42c0c20b60208403a4410406403106500003020144140041c3c041043d0a5031595010740110707081c02103002d004248080c06c2d0801300e10003000140c102ea6040100442a031070007070218400b00d61407914240128140d1502020b4030125602c078407803002c3c0e0742d90380340d954081c3d444213604c441c440c0804600349410010b80608c40da015a03058810f5103100304031021035200c0c2d0b00c008000080a159031055000c041c0080303800302c074185c035001c61502c001074010b500d48100082c00070307140940000d01600d2250308202c980c52000c1d5410091131aa45008191074482c3e485080c03a1404105060307510610019085080200560105044440c00301d001d1160316a03610405840c1d0082010300c40158000300001800a280000620175000c0781d403011300c4070a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 581153857 1250 581152607 581152657
    0x621060c0522030b0702030a12150519080c03161502070f03060509150c07030806030c040c02030408070b070203070603020319020d020a11010515121507050304060b010203041a 77
    0xe031011200920504001105000b84410b002110b5807105c1980011807504001180c002d00880d4001c10418180340e0b22004203120585000040f00100001001c0c8080d400a404405203801001c1c40703100300b18821400e8030303601d6050210f0b440107604400980d4840b45480c2c68154455601c0f80081c28046010f410408500e8444011014002d14040d40f0001542d1a0610005d844e251078030070045407041991041003441c2e0005c00441d90b0065147c5000742031600c903c40440d00d0b01c0324203140302d40d1141c20944680304a55000000e001156603080454406594900c881c0e5003a105e0440040e4042d0040d660500105000e600156040010f10040c40085202491901e00701e8012440e42d0403103d40008990b008554407141c00302a20241000070030260601c2c00b58030141241303942003640070350310311044000003010500c811652038140000c888151300c1d05450060aa520495040742c100d0302d0035140400c01e520020907201941c0101c54400b0341404400c0b600d0119030050345244005103581480c1e1150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 581155107 1250 581153857 581153887
    0x3030f1804110a02060105010503060604140a080d110c060c210702040204060f1205010f4406070809060703020711030f160902070c0317040f030c0501030621060c05 72
    0x15031000034403810380703c000b486002818090103034001c4d0304002050061040c240d80b02c40440d402c4407000300c00c03061540030040c00318100f804107501505603801404503d03c00660061404c0c01d9410a038010ba441c105000410000c00d401103207031055650780940c0480008070441003510f091401c03407124040c10805260300080503030f44180c100c40b00141b070403509240f00f1900404000c42d0a0720740e420603c20382d0304064000032031954a10800e81041d0740300c4201c8a001700015581c0c2c0341d00621040315138409018061107440803490340e9241195100e1440081c0d0313450b10a240b924081c0c0c5e089800340485448006003200603400030042606c0312440d0705480145941d00304021401c0020301e001070548042c00f000750540d00003055006801e8140100b00410010f11404440001e49621282e0b914502080410066060040b900b201d2611030180c5004000d01038041320820480300240e8085c401c40b5141c108441d5100540c110704045141c0c035407095800142d180d0000350b452078051401909103200038101e420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 581156357 1250 581155107 581155121
    0x30402060921030a0f031e02030613020d060501110f030306101205040b09010608030c10020a09030b040b0402090c0403110f031204090e07080a030c0b040c05150315030c03030f1804 79
    0x28103510004d548000700e40c004543c0690724809060411640e0345c44415040c50400d00d1440300c42e601c2d4004000350440e503800c165084c0351800c2e00000c6445189070340041c0c00514640c0610750104804019035030f0184c50009480408841c504051421900c400c41800409030300c0280306000d0040100560060446900c03400d0700c036500410140e01d0740e041c0384510314212035494108030400d800c01c22000c0100480051a4000b00000840050791079840746c0c0101d07440000360f00003c00d21580032040c0401d00041e038240794029030007211003642544034400c04d00c0740c1c1e1040d40b00051241c1000380ea007440f64500100b0b552160304010f03003030b142c0013254034890f803007140c0c081e0308012640b0341c1d03a1040141e45442044850041c100351380042c4079103942e40d10003804050300c0d902c000301001820b00c0000d041140310502400108405041c0c00010642030b8030382074058104a405142c111700e0100780c038902d0703d80012890084800500a14a0030003000400c44084e4800c00f5030148098054854080540320b51284007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 581157607 1250 581156357 581156419
    0x1421040e0907030f051b120706050313020315160e09040305160b1024051b010f02040303030209130b101b171201090c05030705072f04110f0304020609 66
    0x48080c01c40d03c440040c1c01081b020000340641c80e6440401c4a6a034001008401c2c0c810600780305840707a580c60425045c1c6000c810b0002d415004102140300381c120320242c0300e4040d1214040223100d01c1ea0212003142c44500b44000306600c40c00400c00700b0003080c00744008040302e40a0050801442d034450326404900b18003500d0540c11500821010400460001050038007140500841c8503050b1401d01e009040703000305c08041c0050b0002080e0182401000d41c0302d0581c0d034074182c80c2235448071307501d0401a0094001c4030619026800138800343c10100c880703214a00303a03214000c2c03407083c0000d1600c400300c412031286801c80c048080780410b00004164040c664502411200300d2250b600c1c0032201c507003550081c069009688160400c00b0341074516800ca0305482e072161952401585440741070414460301c3c407800d8860070011105500c2c000d60a03000c0f0303210740007043d400d072414801d0031080059a0628071400340811242030041c004100149400c2c001002c50150050160011920b81115a8042e80d5014026 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 581158857 1250 581157607 581157613
    0x2011808090102010b091005040b13111911060f070302040302031504030311120114280503070f050d020607020303091807020705010f080708070315031421040e0907030f05 75
    0x100710a6a09014500107803074107079034400560074003100c05c0402103800d010702482030341c0381d80b82590541c451001002c94155100c0d03003800000110b200459141d8440d00010309160954060b0040160042400d072443d860042c0c01450161743d10a84150450406440c9000300b54080000202580d000c00c5080e03000010181c9551a500b000c2c42c02508845074105e500c02c030600280444c0c1215080a050346044400d103000da0b604445492001030504540f05640800e00200005244802b105825890054034000e8045400e0142c850407240555022445040d41c000c0041c0c01c01c01c0141022400303401c0603440601140d080c13031049000034074860802c168001c01002800c08000907150b04001c2c18000706401c0c03c10ba8030000250340c2c000c001d890001d204506020521010800e824860780c06040310005105044004a40368030703091215280002050001d4440e0405c054080384801444215a404811701c0f1407a00746071070030075001c2044c01481482c043c02800c0d000000310300090b81807903c2c41c0c499406 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 581160107 1250 581158857 581158867
    0x302010206240d0c09050a050f280204140a271d060403021b0402071505091e070305070b031302101103030a240b030a0b0a0302180f01090b06120702011808 68
    0x805d90460354000c0082c481503040605100705108909035658004004000600100c82031800e04600303100e100d64500041c03840068001a070105000aa41d821682110103484203030380d13003610a0001910006011000f0800c00080d03450b0a4154031140c50101c0146d4240c0c1002200d0300c01c2400c085089030b040e40036812800000450f1035816203401074086040707c0440c1040901d40f2040d03885e0228a507018a1103a5a0000c01c9074a4420401c80e500da158030f50198200b4000603144a848981620086a49105184000ca040c294210035a0300c940018400c2c3c0f420410079408204d44a1928a81241441a20300b001654a801030008502c6407001ca4404580101c00103442030281201380321040b000f50340a131040c0140e08001088a8110348408404903101407500e00080001c101640000d40c81403a003481405420a81c12005200c4c20743c0700303d50042c90b03036141c40c00403d5512031910309500001c1048108403224200d9003c641001117480002401100007490b43d101380003000e000d84091001140e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 581161357 1250 581160107 581160119
    0x1501030b0609010803070b22170c0d03020c0606010c0807211409030615031002210105030d0e01050d1404030903120c0b0a0c0228110a0302010206240d0c 67
    0x200c450040c804000210715003600b82e00c1f8080d0458028042d010510082d01e40e9208600e420b0807100e000540007085908006413003041510030b41c0c8041c501c13075000d0091030701e40b0058501910076a020f224040010304050707600c1c4401104e6214200c03800302c4405d803083c4003040c00302d1810450b545000c51850200d54440b0440140030342040c01c0f82c48d201c0c80310b20003041011807646004c981590007500c29100002080e001c140020300f080070421a0303101040c80440c99041420464646070072550090415031303400d0740c0b1002815120080c0c0280100800d16a106625065110b040140507545007507038005145411204810520b5409440035000541701300c809009100500c0c8880078803128034186003205a042c2da644540050340207152041c40c643d15003450b469035009001c84003841c00d8220350910781000380d540c2d10625080000c07080d1040d020a0381034184c40d060810086054980580003852282d603034000a0b02042c0700601c0880b01c00d07480d1a1f0802c2c00c0d40b0780d9040e1388a01d5105100c0608410700f452 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 581162607 1250 581161357 581161369
    0x1050c07060f1803110103050402010e0409030c0b010b130b072f0102010e060105011209020402370503240103151503050a06030804050112061214010506030a0b070309051501030b06 79
    0x1200b00b00040040503c00c00005401400d0504402801c0c2800b0440382d44d00d00043e01c40030805019640c005041c02120710825a20408002030f042c400c3c00c000c00c2c5a601c0b055000424003900e6400440340340c110760240004c003000c40151018502c1218411a4070b4030b8029907070304400c0c44ca4441ca41d42d000d00086500e040d038081c09082402e000b01001003429614040000300448e829540700040365980354914000d5484940490f4545106048200110910307980007041c00c40c1c0312424450310150b044241d031186071003030741100d004290f102c8a01c0c2c2a44010007500121001e00721105050548d203084002c1c0121030086190024080110140e00c0715680d20702c007a003a110018210000c0701e1070007000f403000a0001c415101a500d081c80c006050b14198072003e4018942d40c0c200c00885031464181d202000805030641e443c09440c48001e00c05525150103141d40c424481c2c00c0185020910000101c1c5c4900c02da1228249501807012180a0001030003008014030003a041941d454240c0320801003681400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 581163857 1250 581162607 581162627
    0x306020f040e160914010306030c080607021c05090f130e010203161b081c051906082b090902030f0403030b1c0b070504081507030c0309110f01050c07060f 68
    0x2903004502035564440c014100c049030b00910100d0344e00385c00300d030b000360344240d110001540e0300031403901034a51190007940e6558000c45200d40188545264040040000c81c4444e0034002c0c0c0380c03903481c102040f9008110812500c07038901c9403c03900d402c400304402d030014096403065004000005036242000b01c2100b80c00c80942a54034148220400000030204900602488654018030502e4a03210881100500180c1c0505542d03003041c241400d10102420842000d07001d2a00200100b0210743c1d50401c140e120703900302c000c1c40c4440401060200102c1c2c4400380441c10301702d203868440362070b6807200090001c81c0c2041d0303600060580380108001c1055014032031010029021903840c0451007080c40e10b418040048030000341429408000300e61401e024900342c0f805401000191991100312503a000035103003045030ac50001a0908400e41c4503540a481482c0e40950030a80120781c40c0145020700001424440c0d9140c1000400c100440e0907260601c5017001078a45903030307860a00c0002c204010055611 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 581165107 1250 581163857 581163871
    0xd06150f080703060f0b0a0f05240a0f03110a0503010e071b140c091e071b0201051c050108030c071a3703021b0a050a0b0c040306020f040e 61
    0x1844080c4501e10340080c000d030840c0c0d07010b100814902140c203003c4024180042c0616004025030401060041485800300d045d54420340c0e07007041c0c4d6241a0b1900400d00110203000c2c049100400040d1503003441158072a4110074103003408500701ca107404d40790103035500250749000003c0c000b1005020b10710ba1380a10315003103642c500e000c82400e174070303e918410a0031114400400601c101592480c40103001d11890580b160003e04107560703460090002d45401801d8008041c02226610000700e0003400f07030f01c24801401020f00c00403e80c0c46298019281580000c00c0c00080038540c100029011034540541c84c003034500c0e178011f90789418030000390501e002d809401800c2024100b1131104805111402039a04c00c00300c0040c00941d424104912290807c40800308900d0b0600020701000030f40d406400404c034046c0d130041d0120405007110b034969120740360940010a04e410213503809020035000341b102d94000c07144624552901d0350b2951401c0880c0d20000881080307246c0454204280c4040301c210691140d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 581166357 1250 581165107 581165129
    0xd05060a030f2a2c07092304020a0f110a030203031f05060307020f07080316060b18150a06050405060301090203071b0501050402040507030219050c1906140603120405040c030b0d0615 80
    0xb01548040c019003058000c5400d07c544880030421490560791441ca0843d6020f4021552141d0604004004031000c0759100003203140501202c4a842001480310f15650b09580a10b085482e640c1844181c075403c0c002043c2e134280c240c03c0c040b0f80c03940c1c0c18000354018490f40d002411104c1451503518101507256001c049103400c10700411a8200600340d00c0c0c103c0e82c1d441000000c0c600c010800103141020b48581052103000100d040002c1c40c100c49555842c0c0031021100d03120380e5503407000d08864038492405030f9a0407100a0004000140c07880c0c020396008111402c0c005104180242545458100348070103a0300b680d110410b000650915124907900402c45190562408500003941800030200c08184401c003d0700103042d0032241000d00040039402005958900c40c1040343c00d0540217050191499641c002003100031442c503103000501c2d03d1003444008240350805103003004001c01802c031071180c1c40506480e01a90490380d602c441c01c03011060f209010000d80101c414407071450140c1030750030002c0442 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 581167607 1250 581166357 581166361
    0xf090d090602191403070b01030606050604120f110d0507060914011b0201030f0911030709090b0a0c090308030103050f07050303040503100207060902040903050d05060a030f2a2c 78
    0x1d82c0032031028800109141981c3c180d003024580302c0c40140080010b0005408040386280401500b4090141240c0c09518240708080d1502e0030032085114900c0b070a0181190300720060001269105031146046c083c0415a504896110200f17290050489045905810400d814408a50000b0a40c40a0300e501d44100508050101c0007a20307203c0d00354000e02c1c90b0424600c1c06c100310380c0700350813401100444110501c011126803910121840744000d64034130a0040301d10226480e000e0384603032004d0302e801c502d0500c9282c84202d40c59000b0840c444d0128100710300707504080003060900300154000c5100790018400740c1001d21aa1341400b840d40c20291103500200700800041e0360026035480040750f031810040c0d80e035910345005402001403041c000d410500f40101041415002005041d1840985c0e000703102c6527a0f80360402a0105040c00010010380305c42d004c20012400072140c0006100d5004201c040a50700c1c2801c000b91074084e548800711031000b0180e2019144658501640e100d0049003950340c0034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 581168857 1250 581167607 581167619
    0x50c0a020f1c0c060e03041503051f03080703020309150a1115071b02030706080403080a0e060a0e240118020c0607051c14012402070303050c01060e0f090d09 69
    0xb00c1084000c2d080240c030702409024401164032080307061400307608480c0d0740c44d580c441882c040c24010b81c603000420300c0e150001340c80443e400d0400d40140f075104401e00d91076065544100c4030307821554080c0c04600c014803800c9081c0c0c5a0002a081c0d00340490341d040d0301d540c65190000c00000c2000c0024819030012084890007001305070f04250001540d0520710850306100101000301854800d0103503261041201c0003540b160071201c840d01550081ea41d45901e56561b0b5884020350b1070050003000f2541c1f1030b00c0044c8030605a6403028a1542600080c0c0340c0500f28209042000c488094100540703184c02001045840060f1200100c82c1d039801e9425405c00480d880400d440d400020125002d01c4400280e206441586080c004180a180c050412111070b510881e00d803070701c0090150f005005204808030400400419040100070016801007a0032303403d40e0f40032902034200724000203a070f40d00e03240c001c120b1000080b0039921038014200340704080e260603422280780000074541102845003840d401e100e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 581170107 1250 581168857 581168893
    0x30504051c151d03030f1b030412050d091b090c0e01050403061d0604060b011202092d040e010902130b0109120203030f030a1d0606130e070801050c0a020f 68
    0x41410202c0d000108600091001d000800040034155000d0200008000043c08a20102030103810764010304201c181006900865510081d01c2c0500b0f40d5103140400380d03a96120b0b00042090104001000c41e050001da550f80f000110079104070342608880c04400e22080c0e60302d10440342034218a162044100c20000006002445240000740003281c40c1e41c0c64600000403074980c1c021420052017240c1c2185040c0c10400028520000d81a0000c0c0d01440780da80c1008450003030f02c10402c8010400007401e4081d11703098001690070341030746960080c1022901c1060791903103d40007014141344000300d0344540d103104100b030a80d010311250150030f29001204503e0390b0300c4013148040e11380181141c1c9008940e80000b91441c0901ca4039583d00c2c00c0000b0802120712119000204644062000c0482c1c0307000525010783c45201c121481504541c4a035914040e0480c981c2002d0203d0b01c1140690b00003e403140426403d40e84100c2e2020580c140005203206126030401c5034201c844006030150820040104d1480c1ca = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 581171357 1250 581170107 581170133
    0x40926090a031e080c06100e0f0c09010e1c0c1a09010c0302013911120901030603391202090612060106090603060b03060306010605071e030504051c 65
    0x20039601d0356a00c1d801d04200e6085200580d0485940740d101d2042401190b5100706c1101d943d40140090100004c007000680c150342d000e242220b12080325942d9580281c461038001c001aa810000c5034003001c0741544455848010040444500c15200f0402c0d040440010784180d1000800703030f070500150a40d2000030030569680700340918140c180400380d030504a01500c40c800303441001c42000d0030741c40b201c055640d07894524011741040c0d88180d1151080c0541c0c0c0c2c180c03d80d032110300d180c000740030000b04000314000030b00071004141000951a070700c907207845a01c4c044411145155012555100d907210507400c1c6d080c1200d100b580a804140d904003400b96070039104102d002070084d200c0d41d0200740c0560300e480d402c0d1162a56481221000c1d0396038100200810104e2003060003007072500030f0104404800d10122842340c80d0140092550342d203400411a50ba0384506016145100b0841d0300da01d051034841191906940640c0e14107855130309060420000302d4030400020400f0702c451590f200080d94941200c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 581172607 1250 581171357 581171363
    0xf09170c100203040b030c03040308070203030402031e070902030906060f100c030509040b040203040605070e0a03031e0c12110d0305040f1b0504230703050c0403080c030405040926090a03 82
    0x810707036a10072410ba1840c080c40d0403100c5015804010003481e02c1d0300d440550311986c044d5a44c02c0701911500402d81e100c0c8010784019400da0400707203825801104183c04100c1030034410040341d690b01d6a8016107012600162680c4466030820341c20b00090345004012001c07046000c0300c1c45080c0d003002540103020b2807401c0710002c0c103003c2c001c1688007407565194032048601c000900306555078070b4940750110003400c0855160300070541c01160030126041c17142a000c203507589134480c03100102400140d0b1661501c0005568200940c82d907803400050500320003052207001680365140c0ca8005c1103180b50412403048003940c1058030b400108004111071210b110003050f0410403030006903070000c1070009030890f140c10258100c0c1c1010001c02c1019100b809800980e491412240250f885184049042d91810755200d5207408042c0401d01c0417414080080c03c0d15420001144d02d4503a0b2280480c007960f401c04800d031540015540c4901d074480011069014500c006034900303240c00c0c05d00000902c404000c0c0806 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 581173857 1250 581172607 581172619
    0xf140606010f03150b071208012412020f04030c14190506070204060f0b1b01060b030f1812040305100e031e070203071202122e090c060f09170c 63
    0x801607404a8013900c4016003e801c0103e41e403012181800420074490080401c0011120000040d0b840c100402c8444604802503141140a450190448000c03074501000008240d0800c0a049110842801040150302c01e010016815240880d10400c803034802000c98040e920301000b20800c10b49031701780388050302c2003102e22988a00a03030001c41c0040076283c10624080080c088003094188010000d01250800c641511425030040c200c0c084c261074580c82002000030050000c01c01c040031495400340c1c051610a40301a5841304510024030f03004880380d11101c40000024180140103051010142e0210034510520850b42403480b841c1e900d204038400440014010501d4500c182d1034101151070050b00142202c0c2c8517500c40da0f02810410050302c1c124424190089801001b080110750b14509400d511511508418039610b02d811590038065000103040e80c440f0418002033605170601c0160034079644100718150204009004090305400c0003d50b84501e03070030f8448941c40000c0c040b501c0b08041d124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 581175107 1250 581173857 581173871
    0xf0305150f071d090c0c1204030b0f061302030103110112092d05030d0218010f090506030415020307081f1a0714071409010b0f07020d15090f140606010f03 68
    0x85003c070010441e0360302030300f80411301505100401c040c0800c003030060207960000f80c01554409a510462000410a40715040020195042c85c40381943c0000301420b40c1c1c11380fa0b14164100101d0340240c10071645a0b136101103503111564003020700c8130490000d404c20080d84005494640c2308000b14511b061001110303010030703c05d900c25040d01a40d0303c0d5000c001c403038840041c540700002a42000c8055400c1c041b94a032482420340c41045821840080382e1100c031281401c15040c840f42d0790000300103944108420001e00310110161005610802d481c2d61703841445e040600c08030482c2400a00c8401c05007500130028007400b0203480c500c241e00a24011940e95544451078030401c40150009801241d00030200001007148104844107208603044482440301e0b030300e59003680e0b00c40c0104100003004000602102d0010f01344410260980c0e4002d0b008441580c8143d03d0b07a1003902d0185078200ca42181e282140ca04000420000d12031a50080700500360602e00b1100003880201c9a420150070540c1f0750b50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 581176357 1250 581175107 581175137
    0x11071104020c0d030e0c0102010912050d2003071e05041e08010c080a0606080114010e010c12030902041401030b0412030b030703030309050606150a0c0213060f0305150f07 75
    0x8101c82c40302003141c0c00d44203584140a000b4004101c140500381581c02070302002e40c004c0d032040c8109907203580d00550070140d101e0465030850f03454102891058025079079100c1188904404400031800d148600500399492501602c002c04200d011204054504001085c0d03030b0b00140c0160965060f24075181a120712400d000c2d05451821196900c0600303154078004030381c005542c1c040001880f800410205010b8a9946e10007114190024172408862002141c0040f42a604c24981c054046505141100c0724a81d1600c032903101950010481c804640d8541d081000c40c01d00d070142041040b0045a1029558596158051010b00040005141ca0310101840322210301a40c45446007074405001c80d04030701d4036850098000c150300e100c15242d44c0300b107100103441c5140090130164500c01d814a01400c01c49402c006950018a4a208070392191034882c400e181690b003446128020b0444031000c2a4a615600f02141410341c65002051030800c0e403010000c2006201f5400b41d0000c0140c5840b0245d002800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 581177607 1250 581176357 581176361
    0x70303020904020408030415020d0f0507150e060702010f0b0907050309150a05070801050906030c12330106080c12060f0310050601140702030703080a18080a030206070311071104 78
    0x3001403a8403e101142c0440e600e14000003603c10380310000702c00d05810f03885035016661801c41407070010010b58079480d65111070344036401404107180b0400001102e0701c1e0444020050752840340c440109540b02000300310100c0c1e424080c5800810345d01004020701c440441c00728124060060841040c4100040403079600e4000b0400c92103400e126070500c001c58108400800c02030102510071100050b44c8c00000300300303440d0500e0114001c1500030010001500d8410901003408100700710190103000da541c41c00c03800380c980b100c00224540b8801c82c000300c180401c40b10f03950780d42040e04048100410202005600405c0008680010400c50102000c41e9135400018145491107080e05130540a240c2411042c10300e15004275015001c01d890f01ca884008100652810b40030310100603605500034082007001c030f600c1c00020b10b50010700b0310b04448551046541e499044d501940010103a9001043c8001859414400160030020b90326091102828690075403480b030107503100c094801c4d00182000680e40da101c1d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 581178857 1250 581177607 581177617
    0x30402030f0a050a06110f0909271e1614041e0207050c031c030b0d05060903030108060c0304020a0513060f14091308070308040c0b0304060b040c0c02010e0607030302 73
    0x180c0850b0040e100e589025603e403a840c403c1102c40301d0a000703424402844080c240e038120203410107041d0601c01c06604201035803401801c01d4013450281c80d41d444d401c040d441c40d501b0407610302000030155081201009010500720301d0030060b035504902852501036003021f40110894910b011490800301c0500001002080031500809140960100300c080f01009600a084440d000c0c00075030354401c082d0000d143d00c1d103403000620955030760781c50001a0f0890190b48080c0a05c0780140c20038540007420344c6d0380c51a01406940941ca142d0000c00100001c140400c400c50703100c1d90250f041e90035820560701140240c44980075152290a01d242507000001c620f501500041c030044003000b1206070385d000001483c64025003154050a08100050344004c18400516441d60340b01941c0c51500f030040e2003c032000b03040a8012280d00a10303400c00641d10040102441c0102d001b0280021041214001c01c8102c510802d500004c0c40201d5002901503130304032200e81d201c80700c1650290390382c0550f460110b009104e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 581180107 1250 581178857 581178883
    0xf0903040905070306140a06050a1112040311030714060909070302190906110123180105040c0e01151403070e06040b1806130501050a0e061801080c120c03040203 71
    0x40c0c40c00f0006082d5058011901702c80101113880005028807060080ca81d605009040109000304290441340c5d01c21403110307200d8494001a00d18980004088103002e40c071545c0300b0b4034140a4400b03800040d00d0180200340050044844d1844580c03812000300d00d00e030080403507441c030850340003000880c101d000350110f926182000c04000e02c0b0000b00030000d004003400c0c2c02040e000800382d511410b0014014451108403119140c011200a9250350b0f01484000d0024842d68103000d00f0460f501422a0074090940950722651080d1041030504032580440b510580c00084806104440c002c140b03504000d4080f00e190304000070b1076417556403034402c2c0c1e03e00142a030241d80280001400107071180d42d8030b02078a020b8903003201c800c450035800010007003903020310359a01145d258286010401580504002e00041003075041c40c882070080e80d800100319410a80c020781c1c00c0404000b94801e25a40b1401313090b8003d03503824405052254850b0001050240141081d185840010118040d9074080040c0310304958 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 581181357 1250 581180107 581180111
    0x51e011205070b07020a15170901060b070f031e0302030118050103030e010804050f0d120f09230a020402180f040e0c1e030304060f02010b060405060d33050310050f0f09030409 77
    0x7072040d0020803234500c0045402000d441c01010401c911010f00a0344100e414031000d940c1070030303038540751005280a4007030104d06000c0c01c581d140c60340b0940e4092240d98524551401612036160082301c01444c40d2148103400c5440c40e0000501c00290441c04454441e0001c0c40c100c443ca513194501207203060089101d0382c83d5881840c0b5024001741d40001a52080c820076041400140141034242045d06c04030140105480412060344c5800241611404114811303601140c01d588a96008a8101d80c0700c01000ca90403e4138841920701401c04d010b24450110060307404010410f140c504950b01d0b49040802e0900c21100e4a00d00007501c42594003030200c02c803005094a5a1706e5403000060101e0304c8a4400c40095401c1070000070840c030b44041502c0c1180d402030400c5290103410241c0c540100f06c01c24600c1460400c00c0e41c00301c01c070103000441024040b80e10444845203814a81014a0203c03803841229a15050400308452203030482260b0fa042600100001c40301e4442c0c1507018118022074204100b0b41d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 581182607 1250 581181357 581181389
    0x306040b0a0b0c010e1b15160c081b0a0909080405151b0d080703020d1d07060215090d080403050d05070e1302030708160210051e011205070b07020a 65
    0x484280105883c2d00b40a008006020015005507116803203a03280315000070749002c0c0e8040c1410259056003500541100b00c5240c9500140310f58080304901d0340c10703034640891103801c1c48108070812154001903090b2240359545981000010140303040e0740035841402d0f84600c8000e0422410005580190800520500d1110200041c114a542261036107010000c02412165079204010408055842150f9135042ca955620842600a0b50064243c207048550b1f40c001036030005082086d0405100b440c501505100f480d21400a02c4c2200d00c48062803074484610922800c00000644210070203030030300b00b4005070b5a0340d04060300d26000d00c10a604080d8103040401c415250310100c80c08440710112101c400c02c5118081401c100d0008641c44404500d842313011034200c002c0e4141d004150310541c412103484030300b6603407110140c4100361151144048a80b550000e04284200c8645c050310481003180d01c0800d00d13849103980c07040b280c07080300403e8500040391002d5464989041c0017500742c01c3c101c4a044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 581183857 1250 581182607 581182619
    0x207060f05090106171005061c051b01111c050403020a120b070c02030d03240f090b062502041808031b04060212030c1b0a060f020403020d06020306040b0a 68
    0x2502044442c12259464a5000b03d220b401c9113000c0080252244000c3c0782401c0c0c07909002c4010000035280307540c4440d2014110340a0000c04070280312241c03149000c0c00c0f1030140703212500601c4c2c00008040c2c0c14844011010b0001250020f0090903000c116401880c000380510f1095403075201d990000303504015180d001160030000c0002450f00c15110346100e03071441ea2110002c54403a201030740001d40c142c00076412820130a1080d0401d0692510500d000c40c86250300300b81c6500e04080315441003440307804000d0100000401c40c070603020410b80607503100b03182080e0000d481407504010304860003112110707514002035403074642c000b240042500051b44081c2ca02400c01001541045540810303c5d1501202e0b800b20b007000130190f07000c0340c40d07903002030a00c2400d28040b14141e4000914240e0090403c1c0407181c002101d03074202ca48850705000103017400b40202d0a0801c10384041408480f03195004004c02c200584400c001c1001c0179400800041c0c803500c483c0f0004001d49561100706034801c84212001c944 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 581185107 1250 581183857 581183861
    0x60819151e06110601030b15040b031b09060f0a150c1203051621180b1f0b0304120e040902091f090509210706050903040626070f02010207060f 63
    0x25102c981e240c0700703820960540d074169a5402408000e001800d40c0000c504552404490044007500050010480c20382100100303103001c04180158207030010035003942189003480301c201c0350094000e8440c12880003040340491242c2c5071910902880103520f14549a8a9208500080394a03074800c0090390044441c0740000c020b4181603d540c444040c01c040701c1c0c1c2d4154000d988c69208140003c000c2c200451592a0080007084803007610f0011070b030000001f030001040002218400c078402c00d809080d8111440c410402c5003195001595961300030000d0102250000389004401c54013442c10201c002e0303207880403501030f003c1e8000094224042c4810300c400321500842d01281443c0030391244006550b103108020030b803001960174a130f180d00000c944404aa600000905000100310f005500e421225594a411a40d0444140e10141c00120301400f9843c1c2c450054a4058142080710714a1441984d001074a00c80241114007888180182c440034a4002e4040c4d400c8140c00000400401b812603c81c040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 581186357 1250 581185107 581185109
    0xd030204180203060a090203060607020a030c09050c070305090d030e0907081909030e04180c030c03030f0914130e010204080604050f0d05030a020c01060e01030602090406060819151e 80
    0x10004560300000700c500654070a4034841d400c000c045003011460440000d0003075101030409034114408002c2c29000d83c4541702d000000b54812225035520900d05446181101c1c405032a020305690108030500100781d20400741d42581070104c400300994129484d09856641c0100003e50300150240100081d441e00501d606215600d10024ac02d0f22526034042e94045234146070307005000c60350306010014982802d0f40b2042c0c55a20307900007510820300c1500c542a902d040c40c4d00446024407070354014020185d110030300040a941c0342c1441c494090400564802415448020a020b494640c481c050382109503002400442001002103545a41b078904080c0c0b80c0301e0031507082c3d801d48035442402c11424000144820308140940e220380c250344616038090060b5000368a002c03d00d41d02c030b50000c038840b403803500307464021842400c0050340c840407101030200781c503107662140c1c0a0040081c2040701100500d4420f110560301c2c1071f800511103021001c00c004a03c00f580002c0d07410f0280d5881210007080907981e0324 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 581187607 1250 581186357 581186369
    0x306050901091b061d0a0b1903180804030303090609060c02070303020c090c04061107051f1b02060901140706091103060f07050711130c20030405030c0d030c050d030204 74
    0x10f0f281d08460803004403090003031040700001a070311030044070001d03030243c0b400c142008001e00c0b03a0400c1f0313a1000c2010a03604080c60103a20800f440c2041110580c26110b605419030701069590240691500c5514903402503200c00b505241d1960070003c20080c0c540d2001918130340c41740c3c08101441110704000d50b200d33100d0100302c0c0944100d0200c00c0c3d261910418151188104111b42c910385801c203041101c0c1c1000f800c0054026214034000864540e44040d400a074480001c01d101a000c0c8070807100030140c260340e4404040144611450310050785458040340c41060081c00d06110200c1c1c100c07800d1905101e2402c01800782d601d004884010841114402c0d070419104600322501c0352078008021840b01d90a0f0b4080e00070036400c010010001d0b44040c00030f112004014985002050104203880c00c0c0c0d00d04002e04c000080c0444c0c03e001031030b401c014903940500c01c81801941020304003401301b948c80d840743d04124403648105444408040c81006006142940f00301541c0d44e55401000c040c001c2d4006004003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 581188857 1250 581187607 581187623
    0x9011403010b011701060e0d171c0207050c06031005090f0604142e0315090201180b030a0504060b060c0c0a0603050906041202190818030c061909030605090109 70
    0x9040c40c3d807144030312800b180d003040c1451041d40d2802c1e03800e513680581403e403540c000c0c140007456404198441402c600640e1100c05044e81c61540e24000044c20855100240b501c81c814000940420400a180741c40444107480d0186e40e0f8950000d0510300840325480aa4801c0c100307000c010343c01c014510802c0c060034040e241480156110043c2044a0008503858010030140b003141c10a010004c0d00d40200016141c0c0c1c0900105403691114003964029410f050681a2905505400c6592203000c0640b40b16175a0302500c280b60410010b01c40612001c5c102c40302441d183c00105d4240305a42e131020500c060014029507842d1124004191149980c1c1c42d942d2252043e160b00003266400390148a2180c83d141011381129502e60751034000c1c1c40c0d03110581c00c0441c420000e01d0001c2d43e403424500040305000e000155150071003403180c0d0341e001801241d954000e820610b1075145548484060385c80e0041440d10321302c001c0b1150042214658241d17840505001c0c104010b10880030019401444418001c40708 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 581190107 1250 581188857 581188871
    0x705010e06010b04030f0807031419080c030c0901031109030f060f090105040f020105030907091a041a03120c0c0a090227090705090a030b0103080c0d08041e110901140301 75
    0x514840340202d205c00740540581407104000104504000c0820510a0400c003554480c0c4805c040c005400c0020480c00f10b480740ca41c03c000040d0003d04c55a44001c400c4142460f5180800084105000b9000d040d41819101c0108544c01111501642c024010150490306211500300e50243d0703800054500c0c0c045070380040081980710006005d4240300f1500180e00190300401075004403941e62005044084038000c00c88007051440c078a0003201131070b413200001c0520301c0b0700080400084441160420081c821828510042510007090420042803820081500da1040e030307100b5410b20902c40a0b45911184100d030100d000b1a00358094141c01c903202c0d220300d440f00039040966003588404e01543e03608c1600880000d03902c902c24001090003050181c54030200503541e40d42c90b07101c00420f8208441c3c881740400c081900d40b408009840b1484050718144400b0300740f82d00c85c203000505055803008091480c49000c4140440520310420100029015001c15a90340814078078429042d000e041c40b80d401c04407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 581191357 1250 581190107 581190119
    0xa0c020111101b0219020d02060909090607020c061206010c0f141006090b0a03020910080a30080109020315030d0f080a0207032001060b0f0a02062d1b0705010e0601 72
    0x44040b40302d0f60405c8403010b40e00c0c181d020055194040d100803680b00e20100050042500d45c038140d5070190320301c8402400e80d4200050080d04100d9241c541d20300139136042c02103068801e00c0d0704a1540140c0b00f030811040d4140e072414005420201d100c1c0282200d1340d00d48c0038001580c400640c202902021407010000755032503500c000240c456018070740d580201446000c1c00540f50640704d403030300a00882c1030401007a907a2102541000c3c0d00a0054440b158465424544c081031912400ca0b02c8188030340c040c802a166140c06041d514041c05400b000b00d50101c0040e081d1242111030b41003480c0010212418411034200c0200464290000000050f1b810408200108034034000c1e03602c01645919942c0d410036031800c07041c03075800c8840c03080c030321640d04d96100245104641c80145070703211903144015550440d4983c06458204041e01415000d0a040340f484110040d2001c09048124400d050150f1030f251f10b145401d0000940c2c1900060104c001190402c1000540c00300550b214040140c0340c190380d07246 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 581192607 1250 581191357 581191363
    0x120213060602030912010e100506090606040b04060305070302091e1002060c0a1b0204060b0d060e0f06060a11030f180303090102030406080a060f0314100c050a0c020111101b02 77
    0x7204180c0564018480b240301450003504840e24112100c4c000a026410a01c049182901e0711406601e02940c0380107102039420281051703a0300c5541070315000d103490b10b001e00d07a500c036228500c124003c05541e0808a540940b180c4c04942e420b100050908040801400032004003581c0d2040d001e10644888518290a50001c10300f140705444900c0ca0713130709156604006a0306481c9559507445582140b050b0b041c0165558403c1c60003902c500c0b2440350700e44040c900410102c95081c0c00011241700b1082c01c104e180214003080c0c81c2d21002c191640754a56030514000d03a100c940420f0b05101c2c50102045c25501d0300120805424070401c016001200c499004003459224030607025080d006030001c00c0240207043c00707484110f410000c0941c00203101561505441c10f074034601c0d041260f0b144140c00c0146080c031010011040c01800780041000341c00c1d400d06010341144036170b202607001d0103603016141e0250ba006d054110050341018040c0c81944620450f040000c000c11440404035642010380480c200c0d00c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 581193857 1250 581192607 581192609
    0xf080c0a091509152610060e04140901090c060504030b041127070e0a05060d020703090f03050a030314070905150c060f04050f030a080705030c270406090e070510050c0712021306 78
    0x1042501c1c00c142d0500e0307070841e0f118100c2d1980c1d54109d51038222104c102c0808460403881114030b003000040c0c0b0401e915242e4401c103042c2d8885001c00000348424000b01d44800d50142c3c00c0365101c510450f8804880c40454000c801502d00e00030395115041d0a400c1c1c206020411501c00c1015684e40c14a25000c4401c01c10880c403c1e00a0b241c00c038105124203054401258010f043e5035010342041c0140701d554010140070a081c641040f1a5500641b0300f1404064140c007920700c4030100041003040c9882c0200c0020310405a07072049504c00c02c8000101400c8001d0b070821a0380030702c0d2043c1940c0003880d11503104416450140c408840c54400c0c446d02c010120301c080142d805142d241d0741e03000100e446605007203a254001500c0f020303044008006518032080082d81814a0f040c1031b901103040701800302e0812007101c03a9070340500301c583c1c1090001d250305c48006c10081c060381ea00b21080c6503001241034040310342d0b01907089542c00500c103419000c900011383d11420158140b0031070f901c0c0c00c3d522400c1886c80c15242c1e2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 581195107 1250 581193857 581193871
    0x222060801140a09141207020a060e06030411150a09080c060406020a0f030207120302010e06010602010b0d08030a0902150c010f27210f080c0a0915091526 68
    0x35202c0410a40100740d040810154002e18002040d60a10140c060074040d0403600195100c0c00016035a0860034000303000350043c00d207070401505c4400b80c0c401040780c1d80710040005141e82d400d26140b05403942c2c1c50b4280d0344038203500c2d1032880e103510021101601c498641d0080103050710031a40340100d586005012074055540a5014160380150b070b03611a601c00c2d00008084041d405000d00c003282c0702c07040100014100c1d01031341c004034203002201c050a0a107401070700b141045904019508504da00d408400b0360142d90311000f102c1d1340e56185000040145500d51000394012800d0b003901040070303941000380240580e400300802585840000c0b00c0e088588440504403008002010022203c11121990b80c072a80220024000c1825844503a510041c45180150204243e4603106032201da1011031142d00c91903005503a49040c554040c0a0a0303241144907000041603038840109280b8801e00c100c400500801ca5503440c039805011010703103405001c03007140046152400c074035801d54948020483c00380f40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 581196357 1250 581195107 581195141
    0x10306050609061c09062c0105010e18070909050c03070603050f010e090f0f010e0d0c080f090310020d091a0613021803150702160621090222060801 65
    0x4243c0700d0744424902206030302c0c4203055582d1001c6011500d5070244441c1039074003680c01c000f000f82a041c560b1f00d45d050b0f0100c0c10510303071405005210100a030101c5d0354200342d0035000710803000810b121052900d02c05400c9284810306141c0d40030701b001800a126a100309045095481c2e04e900d0700000c4040359800ca13480101c0510380801041034910319603415401c42c011509603801d140140514625200e03400d00c003040680c2d034800c0440300c40c480510041200300b02603d00620a030f03010b6200c03008140950b03190b581d4070a900107240c00042d9020040012040102e100548d2945d1400c2e8400d8010880080c0070b58008003140c45440d402900c04a2192060400400c404030f10301c1050340000c0250031203901c10347c0301042d84144e1012941d0400840721805070450090301070342b500202c0241840001300e50115403110b40740c014016950030246d4003800e00840c102d0b256030340e0050610f030b5010b09041d4074007940103000024203008281210305040504840a001800860354038041d20742200c2046c039030994888 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 581197607 1250 581196357 581196367
    0x5091f15050708130e090a050c060c01060e0108010f0506010503010302010f080403180f0f050d0201090e060d0c151e090608060f1002060f07020c090402060c2a01030605060906 77
    0x81008940140d15844929100c2e0402c1e500d41d440e04465031012004880b00c400d1004100403034840048040d13488080b1030050070400c2c0d41799641c00d69407c0c440c15000d120f01c6011800300c8526409500c86801010014100041941d40320301c0d641c000c0c036118004c491a2428540016115401034084a0480e82d040c1d60f003c001c108030207011030f04c0c03c0c0068811010060a0000060840284420b060242400b40345103030f10540b60203400b02d11269542e0007203000d0483d6002500160b0f070400c2e94076003142c038403003040341140d075031440040c28421941c03030000c0421406540c046100e41a42607541c1d00254551151080700003200710240c45185929920000030b02c0a540502c20240b0400c403c9400c680d010700b0500d82d07450487c00140c6811f040c240c0000050f40f0010030041c0c0181d82c00d0382c0740d400c00130b0360000d41911001342010800c0e425002b00080e010796800034080000100c20420300c3c02d80a45502100d42d604984100c000c001c803002d00400740002c0c2401400305462920808551000000520180c601 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 581198857 1250 581197607 581197619
    0x40f0c060f140a121a09060409080f0c0a06140610080f01150c0206040605030708130c0603050c1210081614041d030a050d050c0c212205091f 62
    0x155000e49403c90811955144144115449004004a034240c00003d0020304c1503940c02c0c001e16000c010f010607c41d038180401c040101d6484821100300c820101045a96910941c03042403500312036440c010602031034045107001d182407020009006034002c94035600460052801150444015600b500010007020700400440d580c9480d891501440c0c2d0504810400041d00007400c190459800381002c82d10000411a8040d80100c50590004101450b403980703068039105c41101116901a000030b0550f2200841d44002c80340c015a454003080d606121490700c2d1a170300740c02d403291443c4211102440303902400804030000d828800140c50390125800b0080c000d8608000181a40e1440d03c0d28202c0300032200c2400100600c02082d030914240c488541e0307402c10001e000100d40c0f0042c40507aa408050110118041012074001d150104440c0c10100580040117002c0440c4982c48160242560b9401056601e00ca208481c600b201e01c112021404c9a03250b9410148035412a204103500812202c000d00c07803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 581200107 1250 581198857 581198897
    0x6011706010518130905070611030f25110a0501020a200f0a0303020609060c0c061611070306050915041a0403090e090604020f0f01090302090a0b0405040f0c060f 71
    0x3c10b22000030329100902c0da00001c5100c80c203642d035181c11065203404d9802d082c07000030059400107024170b01c0c0c0320641207a2610781a481b80a070f0f003006405140d000070583d49507030700f5001000306101202401c1c005074980d403a000c8020300c0320a005130b0144440003000129580086680c0c80041d801010718000d595440c1046248107005080e81c81c2d001d5180f00c01918191299440c0714090351098000f01107608102c0900c5281100003407140403807039810032559440700c0000c43d8040c2c00030b01601c1034904103030740003505441d0803c50032100216840707224000000d00c23600c1c1c1c1115010307900c800180c40004500e00010204040200c3c1c01809010300b4412030888a800e004083d68458040d10304100c255445031004805800107540702c80069000000303000035860088c240304050601110800d03088006400040d0004c419884040d01c50f864200c005120801e144d0001d085007040140104258945890700c40e00c0810080b01c280c5181c00315100225200d03020b5940d200ca115250f07200e1050070a011888810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 581201357 1250 581200107 581200117
    0x51e0612040f0501140403050a080709091a1507050a0b0a0f05131a090c040b01020f0a2307050d020907051605030c150c07030e1210020d05060117060105 67
    0x6008901080954405180c409040340500d110b40c0d04450088100e08043d429101c24154018803070b03403501d0034800040d03088821507440740303007070b04205205648105055450502c554028449075051170035510400b0f200c000d860040f118110341040e07485401c81c10182550040c240f0040440e80300c01030203400b1070881c40d035095001854500218007400010764800607150161501e071030341c95042c1c1c10001041242502080300c10510020840d4a11749000300c1690b4604011115024950310040d00c20b00d64401d101e5112582c0e40041140c8001401d072800440c0400304c66040300442481e034001004030280441c800c403c40b0320007820fa070150a003a4080180680c000750841051060805c01070000d2140500500d00c51401800a551070743c160b5603160341054500481d11481c0045541046141d0b01a881501d40182d05440d129058002076004282002d0400c80446040d100d160240380448072117030010504c00d04400028009512501300545003281010480301b10100c40400044281d489030010f0a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 581202607 1250 581201357 581201359
    0x8070207230f061b0607090b0309250801060b0a0207150807050318060f0619050a121a090a3003050411120102030402030f0601030f060e070905010801020901031104051e 74
    0xf9281080c0f240790740c580c451140c13071082103d0f0401d10400003e03039085144038000b00040703540103203103107000c3d00311544419140794007400b00c02407281c500c06090544c1c00c41c1c0c800352100d44020805540c0f180540c0344c203a00010b0b0400c005201da0400070500c03c0705000c808503000b201d038442c200c00743c07541001582c1350740000b8500407080f079240040603181c0004004050160548002c08a101c1c204038050000041100501a0851160840030005038440c0d13030b6203408403103400032126111001031405c11024000c61075500300000e1450140305800d80003003090340300c1c2031040c0c42000c107904a11400b5842e1003c02c68200a00640650160b0002c0d80280c011503406031268140c20a592903610010b202e80d00007151482d0701e698044204011414100420303d41c420540004007a207601d995160281d5141640e4001c29030fa4403020400c07003000c0b0410485c1d0151100410a12680d80c46a00641c001c0d00100c0303603140040d0410921840c9508034800701d90542744054200d030ba1680c4200104541c400c0425245 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 581203857 1250 581202607 581202619
    0x6021b030c0a090506030606010e030706111504031706150a11071527030b180a020409240b130b010c0204090305031b03010e070f03091208070207230f 66
    0xe80c000703a880409030b10242000c40c8001980341401d81c20306140020041519040c0026982c5140c6036540000b1194104e5009207498062203982d9201d0a050542110f028a101c50404050104140e04083c50201c40b91403120400000e80e698410800d40d00118034900c43c07040002c00c00601c803944103e030440c000d07003800c00444131055550211292513004001c0c01c0c000185550b104404100c414400d5842000f8105240c20455400d50301c03040d104640280101000508030904485000010b12200340b8980d0010000c0011440b030b41410f02408116031584003019100401080700d25620784142d209002002d012490250142c901d041d00a0042c0015241440309071400036006030b83e5030281c803500d9440f85c2d50359510f9040c080141490b04034001c0131280b69490500051100580d68801d00303510000620784000800b000304826001421002d01c060005110300c2e00c444017242e0072045040c041d052641c200c0395020394810068107000c01969510000324550840c00240785455074002d5412a802400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 581205107 1250 581203857 581203873
    0x206041a09030703051e030c15041e110906060307091401110106151701060507060504170d1a1e0603150a17060a06030803060904060b180402090105060406021b03 71
    0xa40740c0f00f940e0384100c586900c0400c0d42c04d0440514510100f4440c06840250304041c443d0925540300c6003140300d0072071502c01040c0010140312240d00e0300000d400d016a8098080b02c15410078a89240d2494107081c003415078040443d66504100d81101d00c115140c3e40e48441c00790030940800c0f42541d40c155010b04015201c00700c80040c00084c451280140818110104103100940b400b40105030880d01c0c190b41d0a0b054001002890780000803a040c940c2c0c461781c00240703a5160310300034415030302d0210750f0609802c0100d003600090144c1d13403100210740c4022054801c2641c804042003020700b0103030b00040d031071005507203030a513a810000041d68101d40004000740f0100d0789103010614140150f13004403900c01200c643c15000100601043d034026107403200a02119065032a00c001d64407000d04180e016050400018043c000c00380d0013030f22110300051504042450002c0384a80f03107001924180d00c55080c070000041c091400e0411503088030400c0d0060050004412103400c40c070b01800f0704480d00f40c098034076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 581206357 1250 581205107 581205109
    0xb04061104090b03070803070512070309031202160b041413061e09050702030f07020d0c0b04121b080a1b030827030d02070909020d02090408070b07020a0206041a09 72
    0x10744003806a0003400a2a00b03e5201010b2908415910681c1e140e042000310030085140410400c001070109000c07103a550380350380b6044410700c14980c0f01800c001c10001d05070000790f5001c01c02c649200644800b0340586038599002140b6441284540204040c2d100c10414190030a00c0a0b0f00c07003600341c0300b000680c441c0e5441070701120f020030440401d101030441109201c01d60080c0302d0650041d00c50320003907003801c0c0812aa0055407040c20806407240c041da62400d8200180401c0d40d40c050400c06205070b844950319980400d80c0c4c0700e00305080300d44046a203a610199094082e02900b180d440c0390003041030b45402d45620000204c6682c1ca810b264141000100101d03d005000b82141c45001d105054200300c10140f040000e00034035280c0c0d100b03801c420300100300c46500151800a403064000001442802d41c4001f40803482046002500301c0301c0202008188103518014258080c05559495030503510004101d8a82e0340c075040033540032070203001c00e000000010f03507050000e007181d46100b454014860 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 581207607 1250 581206357 581206391
    0xe010807050f2a010b0609450702060121020d1b171204050d170a020c011d09010e091906060608101a09280503190206030c0a09150e0306010b090d0b0406 67
    0x4080b1234601c2c050391070f001c1041200c0e64039541d120b42c0902c050901541007454000c80c0024910b008030b014042d45101c0d0046d503441c01440c0301c031558000005030384d080284440e07030041c0c0010311810058004e00c101e00f40460101149040480100039202d42c0751074203000400c0600c00f40c0100584410044840b84655903000000a20404000c1c1c0c006000819454000402e5402841c6020500e00400701040900352118800c10b4191380b020502c3d601541d50350010185014510f00600501608602c0c001041c000c160307106100383c0f8410385d101031141d920a80910100c4209214001d050705034009242d90032051480605942e010042107402d014071814502451000b015002502c0b00f1102502045203150402880903a0320012043e40b0000c051600000c181e40030080582e00c10483c002010400d240c49100201d01902c80c260800c0d00011000000a0400742c510840501a1141000110f0702e100c020095444811000b050f04260300c001e41e507080700003203014200b1508141c503510206284040300f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 581208857 1250 581207607 581207689
    0x1103010527190b04060806070c060e07060504050a080c130e0a080703170a0b13050603070515070c080a020f010302090312030108010b01080f070e010807050f2a010b0609 74
    0x4018000c03500701c0000c108044a8001503c28070941c5013103020000e1000110f2000c0e803119143c20120402ca1003810500054450801290000e01800d0400310354203402901810a032002940c0310900280c9860b01750b541c502c00e984425510144040c000003454401d90010004611350100b500c070194040c0e65114410b0b00f0044007100400c0c074000906481201c3c2c12003150f40039440d0042444440c900c10b01041d117002e003c801200f6010385a00004100e17490800040006000141002c1c416a902d14804001e980003030000f100c0d4541c50417800940c99030001550070303e0507001000d200c00120100010340003075105400c81c0303400d4094945d003000c202c8085400f9600900c0620300110301441a1400100031840042a80352082e00f28400e02c110a94014104a0042e03020308045410340c45044003a5820702501142c43c241c40c40004130065464004200d011002500c401071100d5021920b107000d0a9990070315040350407100c14040c80b402880d0040940c2d06100c10f1358a00607401c484401c030000d003c051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 581210107 1250 581208857 581208871
    0xb040f12080a1b0503070e0f090405011407020109030e100e03060405071701110d09140a08040f17150a0902040e0a0c050d0b04080913020c060f0105041103010527 71
    0x800010064900c04a00800b400900304001c0241e036643c490402512501014282c0b008101c110801d0b880c5680780e0140c03444048800074042d081902c0c151074004d0280c030600262140d84000c21010400742401401840c44241e07050700c591786459500b0050040901c9404000020841c0215485200380c03024400d860090b4000c001a01003c0c3c2004038190036030443c6030140306039031b04d0b04060303500944041c03094405d9080d0100003c1156038890815400c0c81c084c400300f200c010300078030034142c01300000390000300101c44a00c045c40410558403241c4c41ca00c5403900d188004103420009091504585d9102c4032540120320090008440c0b086801040480d54020300740b9103260700903403159003440071111194000b0321085031001412140744e940e10201203005000240b0301240031425071003940c2c8680500910481140c02192200004800380ea600c2c030080d550004800b500740000309103810300e40140e01381c0d0050007590340d00d103074645028084d03540080c07031071003141a500c112400d070762583c40070201d405406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 581211357 1250 581210107 581210117
    0x6031d100209012010150501120f1b03050103120302040602030331060917090d0f1a040b0f0106030b010203070b100b0c06250f0f030b0901091a100206040b040f12 71
    0x5c0f0f00f8582c40c0442d02c26520005d0480d0000d2010403645e030348010100c8190122102c003050a10101c0d1050001d0403681400300d01010001c50308201c00e0f64180e1000341203a00400c14000c10340d03001e2806800700e00c144e014445c010382042000a00c03141c242074444072190080b6032104000c0a800006402941040d0022107071aa100c00c401000d005d45041e00b84010105040407518081ea50000130300a604188070040c44071480000d01002d00c050403a003a0504441d07800010040d2605181c01210000e00700c031305040042c000c20020840b41c1c0320744500c0c0030791501030b0003d40c40e01d07096031116907840400800c2d0302805c0403c4040880c102c600c0c5405400751443c44401040d140c1819040c00d030303105881540400450000c1c24103820542c0d44140003240c007400781d00b0041800b80c08000c0803005480f031081000d41000341000005080d00856103c2d0000710118401e071402c0303c41e05802c100712034a0441a16005074010408500807800035120130350002d11400c900c00002c14265200c0c0004c1c4c5c07110f891600892 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 581212607 1250 581211357 581211373
    0x8030a030e010506400b1309080306041802040e0a050f06060904120201091a071b050c01050a120606030515010c210201020418050106031d1002090120 66
    0x340c040c007a203900d503610035009001138580100030504407410307080360201012200d1454440004a03c6051034400007804038140581c200d102c07140007403c00910468000c5072034561000e0707004c500d88500c0c0c441d594401c1c81c003440c3d03844030800c11024100240010012996860003100103035100d02c2804602050784001c0e09400c1221f04006061010490340310803070750441405c001041ea01d54001c04d40c881c0c1d0001c0c881c4486900d06404900400820100a01c000008100400f12660180c0d2403841016039035200d1401d4901e40c2184190500010f20062082e4003040d403400d0361350700800c090708e00340000c0e2800142c25410292540143c8400f03912440c00310b50b80340e040c0300e1000540350016007602401e092420390080365554107070f070209000b940e80c091a40758180e05040700e0702c00e404840003410300100d5016030b9021001400001c00d0f081c490440482d1915504052520882182c03030400b4801501418920b045001da20b00a54040e5506074100304128618841200d0949950038a4541c00d0006150030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 581213857 1250 581212607 581212627
    0x9050f040e01150e06010c0b0408070309080f100612020f131e0e100c0e040b0a081510091119030207061d060a05130f1a010b0a090b030c0d0b15040803 66
    0x100c0c6005d00450304001c1c00056900c007241c14003501d140c01a0703010200981e100ca05c0d0804a603940e03541d401c035020078043d243c03090280d41000600d12262003d0780c40100300709580c4203800401100443c400035003000400d0685440fa2821582450340107240c0d241c00700d504250365103401c03d488084440507580b1540e0300103100200074100000c4d244c902c61040100b040c658403100286c03801c0f660703c112a10031600ca64046890f6244c071201c460041c2001030889444c4513000d00007004d501d00031078100c1e22990405800007172100c050700900d1312001102e0815860202c1740c00820803418600e041c00001e054003008800c0000307805119202e00180b451030141000c09500007907509100b0f02410030080f180c18082800300400c0c42602a41d0b01c0756010354070850000c00d625017060306e044921070802240c0d1408000040311040d240042c60300540fa640d46264040c0c8400042015000559641030304d10b00501803404134540545c41540d100c40c0040c0b44002d140740c80e5948124075400341c1c0100c21942c01c0811a550b403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 581215107 1250 581213857 581213879
    0x10608160608010501080109020a020a060c0e0102160302010f050a0201020c0a0807030f08040b1602100e210a0f12021204060609150e0a0b0a090903050406081609050f040e0115 77
    0x18107a0340c902860154035000000300f11300c2c410b000f014102640044c2150b0480d00030004001c849500c4a0300348030180e49007030013034100f030780c0d0a00301070150103424010005a40034143c14001e603035058490080607500c401c0100d80301d40140301050305540d070070000c0008042c001c0004100303c910071401a0340d101131900c0d008000c68090b20402041c002050180300010344220716003039000c008480d07100c24020750303080224540502d9002c0c0300c525502c3c1000103401e04101040400c0024a051480e4180c0000c0001d194800d119100b118800107103da500b45045c507108503404590034100c030380058284030203c1c4080e410324409039000c88034985e0380d41c800c000c11030141c06001e0b008100c443e600d025051a190004112400050010405a95611140351309554000e105006400c1c441410001c0300d54510300507260b0780c0b0074041c0d240410301640004050a40c03454443c0700c0703414181d550148941c50a000e00c022818903020440c1c0c025291050088103440c02d105044c00c001841c0c0080091034604840c1e580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 581216357 1250 581215107 581215109
    0x60729091b1e010f0201090816030320031b09180f060303120c0a050705060406060302041a031e07180f14040f0b0921070c050a1206050a0b0301060816 66
    0x300030503201a282c558900030ba240c4004602c02070902504008020008900401007500000d11884004c9032130004402d1511031400220b1198508010100030800c0c40d420440286901404801d4200300051006c50701c50700c19400d403020b5900241c1404003400003e09200d80500744400d45c0d018607000c00ca000350040c0c007402e400138000c1d4051480e140c2c180d68682c028000c0201000c100342400190380c00030b948240308550384590004160340c1035081615182000e80031910040e80305034184480740040340c1185000100c00c41000340240140d40403000c650107000440c1080c80064061440300050920740308030410301c0d8004022700041c0d40b220000390001200d01c01c810000e500429501000002a030b40ca03c84070542d40c02c004441026500c10381464606049600b0f1812858491514030880c600e9203406040403900c034008031319019454400b803002c00d1030b00b8031a02100c004845d03180008a40b042d031001f13420510f207550115802c01481d0110303080d0b80c440d0748078140a92180e049028a294180d110b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 581217607 1250 581216357 581216359
    0x601060e0102101a03011d1204150827010b011202070c051e031218040e060c0d02120405030403030207060e10200604110f0a05060729091b 61
    0x2105018400003503441c2101d03143d844445a84040079600c4090020055520001c0240240544046210020380d011030080e003210044c410508040040c1c142c007410380e000d6525140a05104184122040b03030075407005000d004158503c1c6032060061030303401c0504140a0840300000c5050700060f000100342501c4500e00c0c00f4018414041d0000089014800800312901102d51130b02c520b124000c4900300c0d000c0821901d501d4821781564414107944500903000c0611034040d2a04c141c140841803000f603911400c2e6001e02600601c0c001201c8004e00409080005803030306006080c0151041c10140030a0152401d403960b9001080400400d0350401c80354011700914900300025440c46c1c0007040306002c030308204509000d00b10705036040301c04000003406100c248820480300c140c10716007414a40b0406001c8018010f111000c0800440d0a01c070050400715a4090003482c500301440d201c3c51150200340050301d419500000c1d000000c0000440800d0044011801400743d00070500c140e0301c82d01c12010545 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 581218857 1250 581217607 581217617
    0x60f03060103202d0702010e011e0806011b0203060103120315031119060e06090d05100e010e010c23072004050f070203071b09060b0403060e0312010911120a050603060106 75
    0x4074040d0409413066034066030342802d10740705040007000182c40c0045040c100d000e60141203101101e5955114500d02d004280c20f8945001c001d5180700c04401c0302d100e14002a4061340700c0b100400c0001d000d0610001450320501e00000c800d0184480d0700c0861131254800c2d10904600003482d2414074264004034050a40700d403002aa0a143c008041d01c0045c0040500d803158401040304c0410342c550100071207829138000c09507416242d40251000080140c0b210140407903107042450401540144510000304009480b0301018420000d85111400e4920301200c2d040601481000002a030448404103030002d040b0070ba280d002030907000e100884d000104150920f00c4d4401c18003990350b8010084a03041500f14040c01c203841c4000e40c81101c5518103070302c840d2595140030707800282c1c1141040500240d03841504280100001142030700da0740d008140080d411509040010005416145e1020001902400450b406d04c11802d8005600070000c981030178026841700304200461609100c10740c05001d01b4140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 581220107 1250 581218857 581218927
    0x10b0415052b12020c04020403050d0f03110f0904230103200d0209060a0302091302090f010b09120c06030a0603050d0f02030307030207060e03030405010e07060e060f0306010320 78
    0x10303615202041d0b00041c14410307200d02c2150000d0710900031000e000401038800d554036a528500250fa504200001e0000201c02811440e0003034400d001d140c80d020300b003410703c50401c005401201400c4d4006242036500c50364884603034030030a0244045c070420817505a04a0900d40c903505004400d10540d2a10b4160714410214101a6079100d0825440198040d2603041070baa0301c00d004114074004640010703500c040a08100702102d103d245848016034800e41d551111500c801c0c0c488001e40000b070155aa07403800900411003039090494402490403054402c48820b48018004980254030540700c049459464400600030f200e81001074100c60092880c00248100110900139142d001c064180ea08040d0002041014020b00b500b141d283d02c8030308800e5941d03030b0900e0b15003603000380540e40c5015098002e140e030008645001c0d10a0b41d9005034060000713898400801601080ca5100500d801d05040c1d881d11000e0b00c8041c0703444c06820342c000d000c40e07181d0345200210302001055000c1d105d20903600d040c104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 581221357 1250 581220107 581220169
    0x301060f110d050d14160e0d0b15060409020c061015020a06020d060e090f060915041220150c0a050f030a0b030f01021e072102010b041505 61
    0xb4001c8041042881c2c000c0d12501001285009008054070881a060f401424028a0080e0321744440f03004402d621058041c00340c40d01484084030454101030b001d14800400120302071501a544000c40f10014116480d00e61036030640e008a07002103010700c61680c4007104008d00b07c40c000004801034880d16420511000c50180025640c0c0490500101601d402180c0441c9013940754010368090085109055a5860407200840d6143c110b1403910101c0e12131400400c025510103c6c40381c0468202c2008a07003240d17102c0e120345048080301501e2a003004881100d940707001944d0b002d550800c11127840035021811031b110f00364000c0c200240128000100400c0454440c81d0040c0c01c0351000c072201d60a03161030340d035081e0b510703402070078101c88241d0103003e4403c85000302d403011f60003003805848005842c09454400d50080c030490007a80d0340104480d4280500d104420041d51400441d400360f0310000c100700c8200f40200e82520005040c600c4009000c580a112620b00240404030102003641c0c443c00d05807042d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 581222607 1250 581221357 581221363
    0x14010503190903051c0f0605090717100f0608060108010b04060f030b1507140105090307020105031305011104080307050c0d0807082203080403020102150f15061e0301060f11 76
    0x8030203411540e541e2541002050300a00c15507042c250000f172800189040b89014502801c0380c5d100782c1e01c44a240c01c601240910740583d41a0040300c0c035940da840242e443c1080101c00c41000b80883e0742d00c03110000c1c000344910304402c05101402d50707991011554104180058030505060f00300c0300350354000340000c2c03214030341c090a120015070940c03a0108000300810041241e404844542d9a001200081c50905001001140340400307030403000208030b070b556071515050701c0f40240100280015010408110364650204040040d0b83c02040005208810280da0a500391b00c139901200e21900003156400601c9000d004680305c1101c107035042c241c03410840c0c2d00d42c4030500c038500b00200192070110b100c8000b5032450030b140c0b030051143c10300010542c2d100e04002c4800d80241c0b00c201c0c0140b0a03c0010310b10b06145d81e100e28010914101280903c0d01c94503101c20010181d6107445070014010300881c00090a08e403e03501daa0004400300c01e640e5414008001e002d0508010034205008008083c690142400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 581223857 1250 581222607 581222641
    0x40906030303230f2205060106020610080102041a0318063102060403030507051f061a091e030c0301180309060215190e011506030b190b0309030705061014010503 71
    0x24542e0440800c005d901c020948241c0c1d0040a4180d01c50080045401c9400242d620f0142c10744030b80346003600343e0ba403401c6400e0f48242d000700d400134600440030308140c580c0c0c1005581c2000ca4480c1003803035070010a05162610313000b10341c80048401103103003810180c041c044501b800d15501110810b41001c0c0c41e0080303042e92145100080030007000103000b105010003800164010b000f00400c2d1865a00c03100c095201030140d500803174200d108841030600561014404490110602818004003044500c6c0482c49003000c183d61103401d4001c0c0082c3c210310307070307020301c5901801d00980004080302d080b07030f040007001d54100350400419580081021503910842c9610250710280da00b00e00b401001d050b2600300080d240c1c24136030030000e6092540807001e80e00b07100401001c0d0b070210341c1d0070081100d81e00200310a41c2010703003510340c01c2d0b40304840034402203060742c000310f40c0420000110383c501415903a455240a40442d5020a0b064082c3d1040c8150080105010781c201800d1034114214202040e4001e017019513 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 581225107 1250 581223857 581223871
    0x9181314280204060510050901121b03110c0111070c090507020a0618080c060f0a02040f030f0609171b03070c1e03060f0e2107080f040906030303230f 66
    0x58071524030455546130404409000040c001c8100c02141041c0039210750401714180740400c49600c815814540302d0720035040d0100403082c5801c000f1b10801c03810381c0244058400d5000a440c101302410340c240e024000d41c14800c6002810592700e01031814615175541e00c0d9000704150078200343c24400380c540d0000e0640d03c2140c002100140384081030b10030b5482c01c1c40515008002550118054a6042000c00c3c0c480c070600d03008100f4002d5540e010b1030302007207104a000d1113502c3e01d81d4090510102d003092440f002d40d20302c548030010307110301c03291100160307010441505d1408400018003811092070881890080408880003075041126554a0708002c56035806080e4065000e4104100442d01c03407800f0800954110a0030803030050340300d10440c0509518a45a02c5521425000f40c00800840c10340c4da020b035000b180c00e10b05141c110355404040d0741c0305000c9441d011509110125036481c0c1c1e803040704021803003900c000401e04044c040d5080d021610100c1c84030071081002c1001340144000410b194400b82d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 581226357 1250 581225107 581225173
    0x130204121b12060c081b0307110709020706060503150c0906090f13060501021b0907080c250623040803060301020c1009021c0c05040209181314 63
    0x16070150001060034140d01c140300c01a4041c2d0340400380035850380078106200c015641c002c17407540d5042d0084981ca019008461514000308000b5030110320800740d4500b1084014240d505a5903121480d81c140c1e04002400d0340c0b2566509010082d6140803c00a00c04050310119500c881c40d0000b0443c2e62030184507075941c01080d0005d80091a582c07014a420180344000344030001208504030b240004202c030340181400351050031102d26a212004401407208030000f4003079900b03a941c40e18221407818002e400082c2c12901400718070491040e142140c4903641401ea1004180c48090404006a0350150345089112080105018140c41d00b81d00f999405034200c5412a43c0b0b4440001290081c8202e03540c0e030710140203003100c80014105c186c010b285014000caa0f4a18605040032030601400c80440b801001c10000110820180c1002d0b009440355044c020707c071441e940094049210001d00c00c842003200180c105031190100300d400084010711885150042004000b4452205200707102d021128040507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 581227607 1250 581226357 581226383
    0xf010c1b150f15030611040b03130c03020d0f0b060616030e01020304120507051e030a0f0510050a020307090b2b0e0a0302061501051204020609040f020c0c13020412 72
    0x1850341e0b0804203440303107124030400c041c2d070103c002001c1e081c640780000c8a099062403803050806400780c068a0544401103402440d46e240c0c0c0360f1100c000c11441d40110f4090a2070070000026a4030a05410305882c05480128520103151a00f40092500104030320711801c01031020140e09401600180c0d0003a915090481640e100c401c010b0b07140d409640e002442e0558101000302c100701c4080b403a00119a000e4540e00340d43d0200e0708082c0f2a040b03c026110f9003541c003c0041c8004a4030401007140c0e4540600151000701700e06001301b0081d41e00403142c0d00840d40c0c001061202d0640d020320b4000040c20080309a074207180c021035200d90340e00300a00034a000f4603d160403041c01303105140e00c0705204040c44011110f00768010300d80603442d068110b400840c5460b101c5804550b5502860842e01480e0f1117450541c031a07940c540c01c20401d9040b42c900280c01940d91140e081c05080f036840200003010303180004028105020b410095800801c440060042d1700611003000004800c80c031291826602c006614158 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 581228857 1250 581227607 581227643
    0xa0504051e070303020118030e1c061b11161502010e0f0639070f3903080318031201060801060908010504050d050d0b040603050f010c1b 60
    0x81010744507111264030484080d00d462003000203104040b00d100f074000b030003402c00d03881503040101520b040142c007140c00d01c403241c1d041d460182c500c000d0303102509000030302400d0203496500458000d14400000151402e10701310040c1d070001c00c181c40e0383d1010300040401e884030719a84001001c4510031030225400415441c00b51034002e4000d00a16154001200e004101d41c0d4031440c1d40f80c00640c0c505244948160030840301c8500007004151403207003050883c0c0e443c88a10008040f030392040205035030300ca0805512800040e01e54400c0c200131084a0900d403034603c00070490300030812155003501140c181e0b500e000c00018010f4070640381d2280d09411a282c280c00340790b81e198150710074007240c030f203036170340e1010001c6001600b200700d05060314220794480c010152580b80c8a400c880341920064143d40c0858103901e180d603c100024100030030240301c08100b60120401103001e892041c1c1003110035410245010342d406600b4412000501e400380340066812030b0751107455a000c0d8040c4005007111a050205d207060b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 581230107 1250 581228857 581228863
    0x90906050105040b030303131b03080d0c14030c0a0507111809060601020c01020703020d08210a0c0903030516020109050301090803180a02010813031707110705060f09060705010615180e0f0a050405 86
    0x840d00034bc081c80e80c50708a051140b004054172080e00c400700c1c00c000781400070035580c00181e078425030a900c01c0c2403074046179010039943c1d40c0129008903119010140c00403842d4480340d10018008800d1031036040c540c10034218060501b1401020319045500612040120741c0e4002666000c0700d80641d203020021b030301800d1840c62882480e120a81c240030108004100010740c0030000d11a00480400b00300c1c48501e001d080b10030784000e12019002a205100c840040800c100204d00164814103115900d10b0b03440d400b09080d038102440c103444215002c020050b941601c0481c0c2259440f40d00080c1200321010390018240d2107000c0e1000d52b501814070301100400d40070340d000c6203210310700060311401c0c0d1802c03000060220700c0004c400300160003040400155414030360f040d60041340407005014144684c1c0018071046030414501a1499921118002a8010341643e5801c035031800c0e035070311140b01103440d0f14007000c03118590105008a00708030821130740c40b0300700c140301342c00104c000e20202c1c081d101c50170881c1c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 581231357 1250 581230107 581230109
    0x10030c020d030c0912060f09050307060c02060c0301030602090a031209050a1a0f1b032b0509101104030b0412090e090303010b0a0309060e0601180b0a0909030504090906050105040b030303131b 84
    0x1111074070b080c48c010180a0000701510740e042c840c52040c80030003c0c0c2c80041707844001c02c3c1c40482100038180012b10000310720b90044c00e40340c1360162114841c0d81e40c948a00364039111781c01c8a000400d031145020b2205060103407264000c1c01d4000e40c0f0700c0c481d50803000f51400d103106480149c10010000316001021030a00101c02c11040f80c0503007181c0c0c4859001008000a001c4982400e83c0d9041134140d4000c00329003130281c54402d80000018140c90340c03100c101c0c000a0202c3c4610315440b2101000040001103012504c140551f001d0140701110031801003000e00080095008180d070b04000904000803002c0020440e8155585a42c90315111100380c2000c0d80949101c000040c1b00d982405034241943c17070001403460480d02e0000c1c0301d00301a2003001d02c0c40700700e8458a06180d04000307089024007203540709410010825110b0700e0501d15065a0300040c10407070700800341c200c0d505a101c01c010005860203000300c011001044004d5480d5040091008142d01d2013003800801250700007190746e030608002c1000c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 581232607 1250 581231357 581231381
    0x50a0f0e07050d060f06030606030e06010509090316050d020609030705060103020f0a150e04050601090e040809011e0815011d220603050307020a0608102310030c020d030c091206 78
    0x22108548070445c844091220780145000245420300000d0381c40e01c41e02030565942542c501421899080c80b040c405090b500034400012481b04018240d02d40405001d81c7c200617009030043c1c4240c1e031902c00000d09015001c4c101d074680350300074004400403400c04548a41140c1c5d04680a804020580b4041444002c00f94840031640c208004c1c0110380702e8010319130a8850008440c00c11141c4d07215001035071100e1441c0104c109105e411400034000500e1400113241e029814100b0880d00c1c5211800201020345c6120030500245100080c402c90006110b0340701c00760502400c166510302510640d00c41890512410540304008160058038000d046560b90000c0790712106d0103014994aa04003180c0e03942c1300c4a0200e00a030b030b00307100005003503204240b0140034566603a0b1450f405864200080f6107905c400c509920810380000a00d082c60740c951119160a011544001c42c2c03400440001a05100408241e401898201000c0e4002c1903400384501066071340c030755504038030800c2d60b007030070002080c04110003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 581233857 1250 581232607 581232611
    0xf15030d030c030b0d120905040513110411030106020a30030504021504080a030801141012020c061509280e1204060305010f240e030c030a06060f050a0f0e07050d 71
    0x1940c10301a50f011540106e59079078640500c4603554074140412501300700c030446014078800b580f8100099070300c000c0760380c903410080c0301051440c40c1c42e018090030340c400c1e44403d0141c0d00400c0003508000e000c0c03514500d02c0e000602c0c10000c281c80000d0b6404482e0350078801d10205603460b0009411550381d402c480d4001d440e484007003a220f54482030490f9a07054440b0090b40403820b02000000c1122004c0107002040e640504a421100b1902905407040321040002c1036645400f40142c0b41e04600070001680701d0440601d00c001042054820701c09204406040c0041654001034081c0140c4001300300304816103c80f0b07a000602d5280300100c103041c0075491020320003030b5400241c0000c600d43d0580201c3e0584107541c6030f4240a40d5103003a440345401700c04210300200011107000040f000c0c0191b00750f50710f0480141c03e444040042c000020700f48821490211110390f036550b0180322038240c50601501a10301507600b82482d50800c4203088050b9040e116900c0d01e84582d50000704d005100700c0503288000424001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 581235107 1250 581233857 581233879
    0x1a1606090203190303050a1514060306012109030e0f0a140d08220608010f0911091206161d0405090114130201030b010f080a0c0e03150f15030d030c030b 67
    0xa014006c1a910791001a00b0007684a400842c0c0c43c42030400c803501d41c00007501e101c240740c0600c045608020b298605005400c0120344054580d00701350182007080321000148070210345806848020204c64541c041e0b2420300c110410b0303031646006c0e0300655900c43e459200c0700101e1400a805030b0243c8600500d080404600c8040000b01c44690042503290000c0d541403158844104903034031a070901c940c07481c03002e0341082000100b076203500102c62070054404451070418000b02080004043d0785000010343e002004201000034459103252000b009403610600d2190211240c62080c017030071407180d21443d0f03503c0104007251000d5114038000100d1900d03181862a00745410400c106842605901007414102002e889620480c00949542d10030349030700c03482d501c400d0040703c014018143e4000c1071010950b0162a203a500f002001a000904c02c40f9114528041c0b514a01a01c8050010300080355841c1c07500d00c4684e4042010407021009150004940d400d0314021406044851415a0000781240d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 581236357 1250 581235107 581235113
    0x150b030304080106080c03150c0a031b0e0f03072d09110418060f14040605130914071202121f09050d020a110103090305040f0b041a160609020319 64
    0x3d811198801d01b0380ea48060072a060507266101e4600103d0318128010001c0c00643c4440041c00c038120542ca400100282c1c600c0d030520080940410b24404940801c45451b081c4c9401c2d5640c04074084164040d2040a14014440011002814102289500407d80307a10701c1804010b90134006c00110034240441c2183d0380300260030340d0050140001e0360200c130b284003040d0505802280e0450f80c0608040025034648944e42d5501e403140c0c10350700c1d40300e034540d0000640c83e41c4201486480c0d9100180c005032a0003d0700d000d45e809a42d9003000305494122600030084008a10141f400c40d640689244802c00d0248401c1c90400741302d582244046440388a9000c4a24007903070208890f10f104e00215011207841002c01d030795079221020010000b1407076118040c100e5100ea000319010750700c207040050034180c98250100071080c00c0e8012820548000ca010003404807006105038400c22401c6005282111714040306d00c80000407903024140b136846407032240840d1001c100071102400703040013107004009680707 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 581237607 1250 581236357 581236361
    0x301050a0204030506070c0201020601050f060d0509010b0a06090305100213031e02040c032a030204230f061303080318100c030b01050c2d0a0605010f0b030112150b0303040801 77
    0x40410340d028805e900c002001e544c00341c0e4450345002c1c4c05070003c0010ba1b2134102001a80d00030034040f590000030a02c1280f14010350741c0106800740320b00000201d07000300d4420a0046040f2103a0150b0304010101c1400c10200b0004190220002e0005070701594500c00b0a480480c2d0020f20351000300342c06c0418130420300c0702c444503222642480c401c031414052008807081c11001c1d240b884a801c10300030005000241c00c00c012405980305001d5070304000d800d055850084124164082d10f00d80a0a21800402c00d55132034001c4a0000c2e10070210f42d080e00b07000510000c0ca00c1e82c840c0e0b000041001c071000021400111510580b080052113610441e80301201c600b0b442c07000340102004a00201c0c0c101b1581c02a5036000d4400c1c1d480300754008000780a030b02a410525a41c070b0450403808490781080e84200d810192050100640d0140035038008206545000484400844280d010510300071341070006110f0707001c550800400c01c80d000b5007103079543c00f21025910000d20410705410307032502c4006030005800d403040d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 581238857 1250 581237607 581237609
    0x5250b040321020306090f07180b1911031902011503060e100606121a032506090308041509050405100503011109100c030e031002090f01170a1a0301050a0204 69
    0x6525840200c044440286043e400300f0f07901280c0c002d280e00002440942d040c4e905980c4502e0b0b42c0340c895610701900c014030090000036008540c000000085001c50314882d001402413448191820724501d81d181060a84c880c02030900d00a1255505151f0007140c40c405d40003120440360b1407209175500e50340c83c43c090303004040c19405119a0701580480c810466281e104002c00ca03420b503203a8807605c01b2119000c2000b0142c180c144010f02d1a1403880c42c60b5070302c04124208000400c10480e000c21004038285807209840c0343c0c0080100007002c10140b0001d140d04080da02100e18204440448030b05420741603682c00c60035003140e608207180c101084024100310190000b10380c02a0002c105003013a03510200c0b0b85120380442c2a821504003040b4041c4d440c8507030201c0c02900c1c003e04c0c0082c20011090002400e05462240b0201d0f0245c000c0713220b00c05454418254500001c0908003104031031204e07801561006001001c0c2244140d40d01c1401d900361380345c8034401c840c00000400800241c60140c605c2e500075002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 581240107 1250 581238857 581238887
    0x20f030f161128060204060203090a0f030309030221010c05130504060b1812060403021e030703090b09190806040c120f1e12030501080d020d05250b0403 67
    0x2000c8101e80100d0300440400c510401c051010b0054680b981180c11000107480400e9180d581e659416400422a03070b1000e4805010503501131aa03d0f06444100f2042c1d20280d0070801d690b9481240400009400a18020403258140c3d1550745110080ca0215200c0c05205d501d00d4055080040c8084c160354007130002c1000200060758142c4454a40c0d081c0030855132903020341a5605002c1103070f04001851000c00c1105480018014605074480c100d64a040c22030584040313000d0382c072940a8039440300e0307482d20382c5a000c83c00b00002d500740700c4c540c0c60041c110310640c824000c0d071032400a0180b03000d4a0b010502103410420400003011a0381d515a180c4e5074100465080d2840d041000c1c010031300c03d9520034075040702900407008036000802c680311900304100c0140441860b15202030344a00003104485d40748454922520001440e40c0b61407403c6090249072001c2100715041001c05810440d088000d407212800c2c9400786d440005440317040d07940083c22000740a400250100b082004041e0310480f54101444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 581241357 1250 581240107 581240131
    0x1707021c12050906041205071d041703070503130302120708030f06040506030d0509030a0b010b0901020f0111070f050a0c030c1415030a1a06040f03060510080c010c0303020f030f 78
    0x80d03001c40454031400b60b440300584c00382d0100010020702080e05600c1c248540914240e61010f660381150b801c42100c40394180002c100004100024003041402582907004850001461840d060070010000e1000a010340366035408081000d01703042c0300304590b4150000c0c01c44426510419810320100c1c0f504111441c41240f50b0550020302e9034182801074038005c00c0060018a24014501011f545603044025015014070907600c03204003242d07864581600800a1111a555843b03a48000a0400e1120400b201e12a0b0400b0f10440310000c100f81141c1c0c0c881d4012140700070a401c10f25183c1d040009118024001954810020043c4821942c01d4401c4824180c01003881c1d00307214050182c035114000141800303001c00e20008802d01c840360030480d50404100c0394403128038083d500240310764009400c0981549502e071002c0c000c001c410b101c1c160f0401d03122540340940f1071525182070740d00d40000709614100514002d0400805000780c0503540e80820841c034060720391503c0d8800c0c2900304000c80324042200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 581242607 1250 581241357 581241383
    0xb090103020103053115231b070606150807081602010f020d0516020a080a1b020301060e1506040e01050f120a0b0633030709050303070f0c08060f041707021c 69
    0xf034092191f032804c001c48442c00c011241000545002001c8000e0400c0c1c0c03858038500202c1d00c01b0444100404109108000000da0b140c180000951002500d00280c03003400ba442040c403c52a4108140c164032a40c119030010f5010118201240906048800b040041e800030030015a1504d02d5040707107211703141016042c0d00e01c021500b004c03680c8100220f8090700000c0101310b24502c0521030340c40803e0709003070400c20303000b031003920b03030100e8211429075020094200c4518103000c00781c0d85070b29040307030f040d441121250700703090078050541c0b00d500e01031040c20310500603104240d03500e84491848801911061007612424200d81c207115012180c1110144d2080201c54100150038240c014002403140b141120032444443c0c3c00151003641e8030141030f02081c07000c80000060107540410082c44214842c0c0b9842d22006003d1030500003000850f0880c00381070300078900700208034104012042e17000350810260241c5542040b66407100d88038407a0080e40011244000d411110010a41c0012040c0700f03440400f210 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 581243857 1250 581242607 581242643
    0x2041401060c0b180f010f0b030c031b040b0a0f03031b11010c03020705040c2a031e050403020a090504170309120705070b0a09060e040b0901030201030531 68
    0x140024000d040105800c0034100340800c010950150340100841c0c01240a0045009030501c0c0c2250742c01705840d00c3c0c1d190b4503500315580c1d0902600c0408041500284058041ca20010303458824080301036103100c5610319000a10390340c40d04541c4803003001910f101070807500c0b488600e0349229580400c2d030114040026540d1041c1d07181c07580b001440d4002200700000c4640b10700450b03d0460f40711080d411446142c0020481d50b459202d10f222050141e10707003100115509078000c01081c6ca801051902c0134081c101800400e4101114011101000c3c0c1c2c0311220000d03240054940c1e014541029400071005000443e1413860f5511440c09280518982e400c4481030042d00710261000311100d07030140c0c002c2da034444115080c000240030720030b10030800d44220503110007440042e50800111303c0f00080740b1610420809800007410841c0320030a8038213104000e500b1020500122041c480241010355900005160f1401da0901100301480440702d0010300341d4040210a400701d403d0001d541a803906540d40e184 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 581245107 1250 581243857 581243891
    0x40e1303020706080c030415110c0a11030d08010303231309050a060b0a0e010e0d24021806182d18010605211003060507020c031f11030f040204 63
    0x455198101d80c42c6c036540c1d07075542e040300204821904540316a20396a243c1c406401100c06022041803034001410000900d0824154071603801c01e40328040e0300030b40207440c5c90580c0801c00c0c5065a80604000c0d0f0014044041511540104080560742e6200400c03040042841d0701c60382000ca48503a8400d00641d2280408801126013074451060b5a1104000602805028480449500a05050842209004402142126207446000c031080c280d08021007203c41e50f00c0c2c095400c5030313007891021400d00d18105516078003040021055441860003044100070044140d00d0524002000b8058601c00c00d5550b102e1042031030005e4040001d6640121204042d090881600c54071040807041e16680b41d18200c402d8585621943e641c02c2411440c100e07200703c1c01c050040d0603010b40702d00361686000c1850f42c11308808a880142001c421500301860702d2210b5030780000c02801c00005580400a031406a50201004000d007080c001c00c1e2031008010032060f030380340e20f414038032030790007070340c09000001000006203c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 581246357 1250 581245107 581245111
    0xf0203092103040e0414211e040b0a030609110703121116030801061704020906010e0a0f0e220506010b09040204050402031303030f1b05070602040e130302070608 71
    0x203000074504144205071004050400c58800704041900e10303050b12116941100c05003201c0a44503907410810601c1103110800170314142e035007820141210400d154401d4030a511422160075800161442d80300810745040040f100108400310030f5075610300026a01601401080c420781095a1038100c0811078000c11034200c5800710360680d1075425034242840044014001181880001310080c070410f41c9081119005d60300c843d009886801c110345c50000d0043c0340d0b4141c5c0d00d0006121003040306200040e11f99565064100e4800d0078000c512001d51004540f40700f00d41d600945014501e01d50000c0d6510000381c0e4180a01c001090b5044080d03d8210100c91803911410b00821513032201e0010042c090200b4050000041c001300050718095440e00014140d03001234a88003014454500840101a05445a401c091050910510890000170610940c030203000c8031600c14842c001880608004603035040b1400351030f04d0942c2d0241420094400700070303186141000c40141c403e4a901052280c0180301d954 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 581247607 1250 581246357 581246359
    0x609012409020c0703060207031106061e040b1f0309170406140a02190606051201050124030902041406012006070302073f030515040e0a140106060f020309 68
    0x3122149000c80341d00c002e600c00c02c07a01045019139840400016802d0000b048018026580d01c402c1940d030403080e034140100580b040c0d11580305008044071a0f100300d07a640ba5041ca040380c0004659004c0f1010414059981c055000038280c480300e0030f0002901079114a14071406110400142050302c0344000c864401c40c0150004905800c04480d4a01d001c140101100450f91043d01c401100000310450040e0500c0750458855444100c03d100c1c42c01d00c0040030300016040d070000c2c0324552400c90b0b5183c95000040d5864002500007552820440c06138008030038465001d03000700720300c02d40020408000740090f210340380044c806d6104e0020450401c051400442e8045010301580e03100d0718001d50003540090000c0751104208084029a60a6000300203020000304142400e14142249407910403182d00380054203045c50001030284103011855076011091080d100090412412002e41c2d15207003110000030f1080c0d01d000340e8a05003400c19040442216455184c4400d9801c0410701039850f405160f00007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 581248857 1250 581247607 581247671
    0x40e0304060f050f300420031f0c050903060f1506040303020d050d090b07020a031218060f060302120f060f0103080a031e0608030c0709060b03150a050909060901 71
    0x41d1540f400640310078982c048460407101c003601000203441035812800c840c166650306c402402c0318585551401f0f44100d03c14203d018012102c24900303c0c083d51805080026010340c0d40700c232140705082c00317401203480c0004010101d94642c0790011001c01d41010481d241c82000380b90007200c412500f03000c020b88042d40e6041c1c01030140100c44400c1116903400858808028a40302c5040c030020511040144d8056a080e5018040045107401d014112880c40010005a03a10b4201501002906d00759070942041e80800007046076420603142c04042e043c1a00003942c00380c22004517003c0940c1c001a0001e191100d0000c0c0d40941d5141c5400b484562001d00c4082c180d01401c100c0440e0f81751103540021a2150305820300c1c0008000d080d01072080391440e410102d010303480028043c0213400f04100d581e00908005000380b04490031b112829130140030181040071811006c4140700312686d070b522442c3d0007a100260a43d49245090030400344d8980c0d0070740b03158180354a0101d80020800104205030460701441c048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 581250107 1250 581248857 581248867
    0x1b06030103060e10092010020d030b130203160909050601050d020a231e0301050d02060f0c150a0c09030b06191203050a02060c07020a03060c0e040e0304060f050f 71
    0x5090140c000b0403d5a000e501072880c4264007050385110b006412801903d4081c94040803082d02d500c03403450040144d10a94400954042650b07001401504460301c6241c00300f12401c081d0040342d14500b03820414441d00b40040104400d0107105043d10303150b19059070700c070381c0407564a104200443d03178161821030002c1c44c10011a842608660001d0030030385540d15000f0b40442c0300010307180c9401d025000d05081c18074006100112800b4910f041d0a00448200140341b95516041c009070120705407c400901509000c6841e07800c44100000b0345440481c2e050583d0704c20f903451100e0581c03460301254008031741c0703103032601d201c01e0b161040c000c100603658000f5100445495503410044104017500300c81c04804a05c0c5804541c080484c0c62106000e03202e610f030651210300c2e0040182c14a40011300381a0010014807068000da0744800343d03c421690481743c0000c141c0c00401003244c08000c41c000302a00130b824000384070030001e000801002241e00c80d50390348948140140d000c485038440c0741842080d0500c1401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 581251357 1250 581250107 581250113
    0x604030f05070b0106080123210a061401060f030c201e101b081612180302070f05010c0209090f0a0c09141e06270103051b06030103 58
    0xc84410030302800d00c94100201540c44515a5800340c100e1000510140010050705080394010410389030750007a0b0307090007401100800c3d4012502e449410040030448101603880a0500203d0740c0503401280c10f20504400c444020404c4800384655000100f0a030203844006100e0310910864480c950b0711000c038401e10300c0346680300f411140c0100b0b5443c040d5060b0a00d544030715102d441c2005000d02c010301100c68200100d102100c03011201e0520301c0c11000440c50383d40d40c0c0310044031b40c001e0210100f0400c0600b00e030000c407400407a421040b00700c6407501081c9581e68906000e0450303402e10a40c00c9549454480100b601e03200b440344141404038105401c0900146882a815503015045100300c90030305c1c1003402141e284c424000004e80c0c040c20a143c00380700c0381603580034000c0b410f09110700d01d5655040549060b01180d019941141801c43e01001040840e91154031040710080c80301c41c01d00700000128150201e0702070a21040311607110f0604160300140740121503921100004000e42d003542e04e151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 581252607 1250 581251357 581251367
    0x7060911010c05061302120304140a170d14040f0b090301060b090f060f0c03030c07060614212d060a0c02030901080a0f110c0f010524031e010b190503060403 69
    0x20304a07031081f40520f180d21000e0042000e000103005440c50b03407046807400c01c01e200780f000f01030700f0400c140000c14014000820700042c0864003a42c480c0b80c010310001c0b0080000c0810b00540d040000d40640d13066002a0960a103401b0340045c14007180200121507648030107144070710890072101e4001c8058042c1c6c040c00c2c6010401b0304402101e0040341c0b441c200c1d4905545055910480d0341c462800008203600060141c248100c001406541e00900c144007807407000a1740070314840d00800700301558455500c0080c1000e00c0202c2c44080385e07c40b04c45045250608007400c0c681e400341211014400c14000030a60800e5010325071400c905a0061740ca0100c0000c011162440d00605001015450360a6001720750214480c4000146080301c4064507005580103007410400642c00d003560680c10322080c07080640d005a40e0f4001c5d034000c1d4090104d428100d50100b410108003801c0a811f80d400189011000036040d00f01d4080e0940441d802c91b1400318150040002c45c2582c05850f0b0143e00050015002038050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 581253857 1250 581252607 581252641
    0xa030b070c080d0f0207051c1d0607060903051902120405060a140403050c010806041a102c031219030f0b031b03060109090807081b0307060911010c0506 67
    0x2c1059502c0d100a022184059500d10f030243c019040c0d002403250140201800f104200c102d014290f5803103403030200d03001004a110314400c4d001c8104000482c054030f80d05c0000302d81260783e00c440213011200443c10054081c1c1c10080841070906141a4020409807020a0110500e00b1001d902402d160038001448042e4010311917100a101c034802003118088102006880194071900c01003140b105960300040981d08081c01302c41c021030400d1480300c101501d20081d101d1503601554080390102038104126025a0540c001e021b20055042918002e1451311422503e81c007416070480c0e04440510780800034034415805154068100e40c080c0c2c10081d4070070741218028024607540842c400c0150307800a400e1810340352106941001c21500c10300e0a04050155030f0044c8450354003007001d14501d448a048610072840c0041600c01d00040e402c1c500d91008110401512484040341c3c0c80d05440e20b0035000800d0201d2099402d1800c0c95606800e541c0701e4a600d10803079a100010b0212600c07000810100014a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 581255107 1250 581253857 581253863
    0x13050a0207170406090b042d0513050405071512020706060e01060c05010506031617030d060e0a0b0303071505070e150405040b0a03080a081005060f0a08060a030b070c 73
    0x1c0104401180709200407500352012074a4003030b6a5841e241014080041d19444640145010320007004414500d0f40b80c42d1074504221000c600c244903801d0f051090001580002e58050b4a045000601c446554021131196100c1d00031a061151106c0d801c0300b20800d00007080c3c00080380c0c444240740c40c1500350090640907210300c10206e50142c68061610030440b098010600103001009008107000c0d0900400d908a502a030103031000024002c1e83c0c41c126007682c0542007401d10422a0b003125040c0400890b2100807844604100207520381e1120b0901d0700046c0d4000710401d0805408418901d030100445015640c0f2001680255a07050880b001504000708000e081c45009100075010307448030380c2059500c15864a5080e6038506100401c03003214407143c0c2a60140c50840301c00d10000d48100200c030203146080c10285030729928103024445c04035540e000240c000d00081503100002ca513010250054040fa51515a0f4950b5604240901040c0301d01c800381c440344a01d00172400031801203244288481c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 581256357 1250 581255107 581255111
    0x614010507060b0904060e061008060c0714010203010909021305011410030921020f0604050a0803061207080a1509020d031b050f0607020d020a0b060f061902070e1513050a 75
    0x800140004c400020468059880b02e880344c00d000443c1c00300740900c03640300820b103000000c2c0038103008007141d031200000c10301c0050305400a0340070140a0303101586039145403460029940c96840e01034081c09001c2d01e0204034082d110000e0174400600350380c01a01d05880d00b032801a0300d5800700408000050000007170800074903554030307140c101003000c44d034858200440c4d0010990a1042f05a0000d140070036208070481d041e0040001e20002810100311803c00c640c0280a0603120b455040c000382142c01181000742e80c0b0f03c102c2400051142c404105800c2e041c0c06500d0000440210b10042c205943c18a0300080d17020f040302c504d2000081c064180714042000c01000c140c4030b580313550360303492400200b200400c4081c5d207c0b1080060041d410030071502240e01d42c2c07016103903411803540d8036034203440007800c00c0d8031482d02c1c0313212031704a0f0b02e03010705860386684848002d841c9058851406521001c0c58001e031007442c0c4500001810b2500c03100f43c2044035079406000081080d107003000700c0d0010400a002d030800c480d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 581257607 1250 581256357 581256371
    0x611040308120103140708030f031e0f1f050609150d0e030316030b01120c21020a08011a040605030c090306240109031e062418061401050706 62
    0x5103800c0058200b10302e100d15500507a50660400f01e44081005401a007103a04c440014000c45a0210030742d2002d4018089454407500d403401d1510131040c40c80d0b400c0286c030b03600c4420481d54550191210340645201100c20609104040710300c1e00041d00d902030031b40c11450402c5408030904142180000c0050700400107418200d051490b01c0607508485141c503060340c804006d00a03040510845403440611604081007243c000c400042c0c01d840380c0411100450b0781d14444040c605016042007524081404052500310668082010094005803203900000700080000700c0e01191003003003041e03035504d00c0320a00e081a00e081400c480d50b910040c000c5040500c03e1140c0781701510100091400b5240da184203100c1e413407105004000e02805291528100120418100049070540001c00c103600064410042c035040d0500b030180160121001550b0b914900019440031102680d80f00c0060f03071060665040982e104012841c02e80d0b405002c0c5c2c500214940c0110a400c0d800381004010052003640d000c1912 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 581258857 1250 581257607 581257613
    0x10c1e1d1e0603090718060515070c090903050a080f0903041e05030a030201061805060a060c051c03050621120901140307080f06060720040b0301050907061103031306110403 76
    0xd81c200f036413090b001d40d2080c0024003203500c40e40c140b8010180c3d036202c1044082e00e00000036003400780c400b03540b1081c038900103082000d10032450100c1c0c010b4280c980c0c09200a152a02d0002d05030390040d0010000502c419020522011201304064002d89400000b58105030400849012024808920b2160300d0f610000c0090b040e02d09100c0d90b04114000d80000443c0d520301403200451090310038600c002d40d4a40400c000959940c880841c0990b00c852810a0700700c0c80c05c0c50f08070724040030400c00042c100c0b0b0b184102d4280550640003503128040a4410130a035401c1209000c216902d284c2281542e908021400b4114204410161a40303c50514125954140e07400c484520340e4415030301d84e4001045e5100700b00c0000c0220f071a01d1742088081d200c4510b024900d44409c101840910f2a502c918080701c040c8074802e541d01d40001580c0503008008000c41d05090504035580c202c40c1c030130000400c22a40a101d201c0001100740e9119104076685003040b000c40f6610f8100415900d508030701d00c20070610000c404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 581260107 1250 581258857 581258869
    0x110604110d0c0e070305100b0703181205010504022418010c0209010f050f0607111011011805060903030105011b05150f0a1103090a02040f0e010c1e1d1e 67
    0x2408400340181ea1420104c0c0010140c801c002e14808907011052000c20040401c03008644400382c0610b000c0b48400841e100e0002d010403a68000e90b00070480103003907000d201c41980720030f010b10f100b1a24441114041082110781c5e40c2c010b41c00306d07030120080c042d4089414002444500e80141450441210b075601d900251384d5400a0704190341d11049010103008604144240703400c2c144080b580176041061564490341001c8215080f180110b02d2004000403080c0905074200244030b0030402442001c1480341c03003844100205000780ca5604c04c0201080c825400482120705851041c1d403105c6100c0c100038403030b10030541e25030002c903494422103c401d03020316485001c00380a4141d64283c0105420030464080039620b0f07043d645425100d0420038401c2c1da420005d074450301154141c07008101161a0503014004016081241005500b00601d1109482e4040c100f60700c000b26015401d207009850390011140e810403070b8201d514903640301540d00f54500c1c140d14505d1600d900d40382c4241d907003030100e008286 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 581261357 1250 581260107 581260109
    0xd090b0904020903060910110717160c060509090f040b0f130203060a06051314150301020409020a0306060809030a0903030e0d0f110a08061909051903050301050f01110604110d0c 78
    0x806c03500420b401105049a80c05001c000c00e01c0d10100a0030b0180b1a12109030444000d2106c0101d1840000c04160b8071200700c555400d600d405c8107a00400300e544000241c003a6014420942c03081440c0c40010300b542c1c0158003114000e13a005014141d01d941d0f08079810702da81001808495540c090f0301c41c1c84005032341c01c1103c1031083c500743d6004200c162401d0140000c99000c0001038900c0c5040030004042001146409584180390758003200c0c06614071808a80242706540107400e10f1b0b0700003da8507407400c0d0141c10600485065a0f903d801c03a0f9205085140c4900446803440002581301e1000c0000c02c1c881d90001c2500d0038000c0044150080039a0b5030a40b6407040c45080b5001a508010844589081c42c40080140590740c0030301460b28146c18a05854a4400042d10310f1030365600244d014417404100410121580c28480c21140d07840741005003440d0000d2003100d208985007888581c00354842e9015518003a10074004045070703111a61801d01d04810207107d15000341626410101081c81400858 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 581262607 1250 581261357 581261371
    0xc080709060602060405060402191a12090f15070311130311012d0c23012003240406060c0506090105090703030807030f0f0c0f020d090b090402090306 66
    0x280251900003440140c400c82c1d4001d1065400000420011841c04a412a8000c0d030485818186003515907002c80d515800e90401115440f5428400100004910003403d810303006c40c0070b40c000c40c0e5a00300c0c4595a2020740d88540d80315040181d00200640d100c109194018400d4240810105c41040c6050450782050340d158401001c840c42c200144003c2c407510784903403c020710b0174460b0ba04170880b40039405c0701d41030030030000d400302000401d4070b1510660303000f20110380c017400301000f4040d9001009100d07505101019600e51170681c8110408190f0107640d0b10001185080354110340c0c0315014403550341c40208612411342140c81d1300c201195201d115401c0500500c0d25580312450007400c0041c98014002c11000c07031a85000140b10072090001004c50890303a043c9860070440c0d0311410100d0142ca45c03803007182c0c079907070903d0044410350000382c200300317135012059072103a40d8100501e000701da90b40b19050788540031404e840f030280002042e84009000284d8042c001501e0111a00c020900d0048126401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 581263857 1250 581262607 581262613
    0x3050406050601110a02011b0803090715020706170a0603061b03110906160303060906030b0916050a06050f0408070e061201020a02030306010e12120a2c0d0f0c08 71
    0x10004503201d0190001403e00e001d0603d010baa0003a903075200392200000c0d0510100046020f66040c0c07801c420034800b0b6004041725140e027400032034250b55403a5030042c52400c4900001d5100200e2000482000700c846a0b6184048514411804181000050300143c40c15880d0312011005c18954000c40c3e1310356160303a1400395001448000181120004401d914010384100708880c1240c4e82d85068805407000180d0900d101e10712131509800030892540300f200d2903414510000180305a0b840840e102d41c103220151604000707030b503010384581c3d0780c94061030794840c218007005e005281c030401c00340c440c5100c10703000189081c2d143c0c2c200506d4a8981d510072580d1076050300802c940340c00e00340080707a1450310482c000c1d410510314040103912800b00404032410080c01005160f030300c2e5604c15180c0c1c005440c1106481901800086ca00059404401c0d043c010515403050110008582e001d810030301a219500b500d40000c16008015118407500f13800da554406010050010546461031800142800401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 581265107 1250 581263857 581263861
    0x3010606050c1612170c060a0b1315031b0f0b0712020f151909030e240405043801090b04030f12050409021323060f09041107030305 58
    0x191071604092031100414003281280400044654909060f1800c5c1d005050f0400511011103a20031030144812000c0a40314032401c0c01240003441e4411403682c9029030700044618560002c0c90203550301c10290a00d82c61003000200042610f0558040c8842080400c642500da81c0c1c03e159070701c1000540141006d07070340000b07030b40003003011154030b003010034060f40040c3c00b250f5142031005440c1d00180c030100d01030040c0c0d00f0002d28440e0006100240030151207801b0801d05500341401450110700521550051180c9850400300c186200d0342204008e0b05261410300d420701749014403021f003503005803100196443c01448498907500c0064000021000c00041e2214959200010500d2030154802072050390108010b102082c490254138600361b070840c060203044030400c0c00c111110310680e84240c0d5401d20216a0447d0341701f00200c0c10302200e40c03111440c0c0004103001d181e4811007505d0a01c1603801070040101021014070280908800100240300050003540102800050742c030941c011000603682d802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 581266357 1250 581265107 581265127
    0xc060c150a0618020c011401060f09050604080307110a1212170c0f090102070801050c04030c080309180a140a05040614070e0418020402070602040602120702030304050d030203090301060605 83
    0x2115501032072140e42404000c1c900310440080300c00042140300095000640010b05880940210700540c2c0221400c6159695504004101c200c920045000003802d00a0010781880c009080e1400c0da10240007440c50485141e5440340b8003285101c07040d40000b07002200040d51101207140da0942030241249460b0200c100c04000c0090744e45205806844030b158060040e500160400c1ea50b103030f4400c0614990b03031100500141c2c5403002c182d1004a00e0741c24401002081040140504201c0348519100314107a600c0e03000b05922070151a41d120303004210307001e40e20b0b0040744c2c21200e82c0d0040c9661a0000c5c41400301c09800340229011101c4c2600d050315032042c0410088140302c1c498842c2d105520b09201c508003804000c0c00e40140c2900244655110064106c01d06012283c440100c0d40c000d02c01c650318200c6180000180d0454030524001d030040d40b561031003601c400c00032281055402070146107403e040c00c0070032641e21002c840035011440144450107854400344101005440d882c2c44a40c1c9070310b6008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 581267607 1250 581266357 581266393
    0xb0a020c060f0114130213170c0d0f06150b03161d0d082b0e0d080c040e04030306030203030706090c050f150a021204030809030d031802040e0c060c 65
    0x41d01c00550b480048004111180301030000900020301100d00b040c41d0012207010b14040d0107429011404d4100d072140c006440c4a40001e01020700700e05a0546030601060070800500711810800544942848014030000800b10b40c0050544903004644d10640c03034075038011062541080764400300041001e01c40d85078054000b8004080e144088417009110000700011403162010b00b44010011240480d440b41c101907014040780704510040c090044541030040180d014060b454070000250190a2007800c00c544a8030b005441010b400103254941481e1174071400d003004000780b081e002c00d030b51044003200580e410320040407a82d001c1c03100452200114101082038003800c0e40f10300c0c03142c00724a140700c040f620382c120700f24000e0030078641507600d0750705404041e82003a084180e00b0041da02c00040100421160703001508075404168100c414402e05500103130101c0d84075200500c100c1700c01d0f0f04607800524150300400b0210714400151400d140142c0301203482600951210f1040f504802c4103814182d81503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 581268857 1250 581267607 581267611
    0xc0b0a0c0b0c04060c0b09010204090c020715020304080a0311150f06041103070e0103050a090507080307060501050105030415050718090905011b081b070209040309050f1212160b0a020c06 82
    0x80042c80d1410385442c10140601c050340500500e03280400707000515143c000c3d81a01c00030f0002d440d05101c1000c4110000351641114003c510508840981d020007161001060701c2c19240702d0401007040586545050790f00380003100c4400c40a11500c44011070510301d4401e1240280000224507401c0c0c2440c01c20003050300c82055010030148424000c02c2003407507002420182c0500282030002c2d4075151103c6600151100c20310140403841403282c0017440c3d2200200501c00743d03018000c10011030340c135a00116510320040c3c3e0050b2035803c486803d02800065a44120b41100840c200b041d12201c0450418561008940c4244c46c07550b69810f00b0f0f001d00000703016a9101b100c41c458000941201e008c0c0103005501c0113400b81c003003500c000c000c071103030104031900300d841c5a030700241051010302e03261800900e80c03991405400c0c007494803400070301014145152070740480c00c804070181c080c144100104013500c0d0003004800c1c4c102940056010041507440c4c4c41c290003181402005650b5aa141301d0340c43c07401c440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 581270107 1250 581268857 581268871
    0x1060305120d1a0319050312160912020f060a020319090810050f040f031407080301031709030604170409060902040501081b030109050a2702270f040c0b0a0c0b 70
    0x9004014220f0f584c01090141c0807400c994404c4000a41d18107005e850750141c060076400c10440345061040c04594000c100c088814590b503240300060311074403a50000c2c0c240c0a002500841d0b8619890094031708500600310322011032044906003000001d01040107406100920041a03050400f0f10440000303001100d174403400383c00184554108801c9407034440070014005092115013401450030544113103106511a6010500d894507002141403000301c983c42844100d0f03484050b100031114107441c0c802981d0900780c0042c0600704c3d640d0f490322a400f000b9480e13024042d41c60310400010448400c64412035025100c04100161560304000c00501410740150036940c5d460300454444040041500499041d035940308004610703030700d40032400c0000d0407801c0400d0300070040300030049070705070120402154824002c4903a111840b28410104040402c5000072400310301902000034a100030792440780f81c00030f2065081c4408540d50b00a01c96080c0c028543d80400036003184030072005d10170360240281e04211 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 581271357 1250 581270107 581270141
    0xc0311030a0509060901020102070803041a01050d020319031b0b1501080108030f09240306100302090102280605010e07020721150e0715021b012001060305120d 70
    0x44101d030090706038099041458402c08000608401c0c9034400e4040c1e03220f00764030042c03035900c070305280c0b500310301d9007100c076101c3d042c80700b040000002d0a16282c405541d030581c001e000f034100d180345940e940883d01140d01c010317810b020000554414039005903040c2441540a5603ca61090902682000300f80b655820385338100f28030b440050100450202c102c41c81c004030b03400d075107a9500c51200410240d005210502615040d0000082c03031224a0030011071090784200d81200403030040d40e8081e0200c0c0942d10345a4016806403c016400031030760024620700300031003030704100401020781e2130505a820907005411b00404481c01d10404a404000c0000540200d00d813202440d410046200100a00810094000100300d03800482ea000e66511002c0c020861034141c0d0ba455854102c9420120800f01034140103204640307501e4443d281c44d510300030506505945066042201c6120300b00f0307000c601805600e4075540c030380700040021010854219080741802a41e0348500ca6250349a04231303008140c50210001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 581272607 1250 581271357 581271367
    0xc060c0b010518190b040603031e02010c050d11040510021606020a1a0c0c0d031e1a040b150d05070e0409031e0207090f0f05060339100c031103 63
    0x2884080d4084e0310030303c9103a646401a003102c40410207410882c030041c0d0443d1920101106159010307010300e4402c8010a450314100f62041030407030880b003142da40040040e03014403901000107500d402c801ea0440414103030b40d0501c0d44500000e00d4165003106038102680c03140007524262000204d81d80014019800503008107503c0c0e0f1564075040b0324854400c0d03c102000300010b050443d03010203450401d4124030031603d0100c3c80e150064010200c001003490540314076064054561028011981d4030121034816103041100300e4140806080c1520009520072505060340080c41650400f0388981c40c0e8075030300403420342425400a041c1c09602030540d030140d42000d0406001ca0341101030659164100b2200c4000b8400444040741080d031160401b4849504055480040510542041344407a5514000300499114001010707901c0008a400d402d84c0c80459411201400c10b10310203488681015451a00400080000604d0202485510b00201c0c0c6244802801d041d0b000d851038030540b110350f00440c904 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 581273857 1250 581272607 581272639
    0x2408060115033201090506030c010e040c0509060d090605150d140f1020120a0c03021204080c010c030203060a0512030d0612051b01081306090c060c0b0105 68
    0x1890440031410906441c0c1d8140300c08161045040e104205410718603d50455401da40e0604840003846019030346414a400300300145408a100c0b81c90140503141d8005a0b840041884040c00080c1c5010080c42418000ba9805403200d070018004a40e0402001a2201d00f40c600002180c01c081c250844004000010029540707441422007941a040514402141d2304403040034600500f181c2e541d0824003404114940c409135640040399903000f11502840742c440c00c668080f0a03401100a03022801c240103004c910f109a00b070b03000c14985101898058604060500e070204000c4064800701c60b401400a0712944070a02071060f0380d41000307286415440c2d0f0034000c00056510050b4003d2900c15400580580504c00042080b01e140901a64003400501e80d2244846501a016003050381d01e40901d07030000c2e4100c41d0384245c90010010503150f0315415200c8415041c0304c5075000c1c100711141e03030360740d2601c1c0d0100300078014010092030b4030b580c0d414114103103280c01c485100040e4041c0f4045c001d645240030784 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 581275107 1250 581273857 581273879
    0x5070219151d0d0e060c06010b030702010e16060f09080c010e12060f0103050d0807050d021606090b330105030702071d04023c010c020424080601 64
    0x200079001001458105512081c4500805240b06458200c40c070681400390140004100c2c5050300f405501d4100011094070103200452146445203559a0411801807000c2504030b07000d0341e000202c500c00019600d9100c0c041a180500000c61840350000041c41045881d40c042017901401c0c41c18034100e0303070451919000640c1c50240308a46070501107401080d441a440300700e0b10259161140040f1591420700300c00c0501100c3c400c6c00b00341d509005030254007031044d010303140140c054062035a65915004070203d180c002508052000b03010948241100c0000c58054060414218001d820ba08500d0501c00c0e4020f0450750320709110110180b9100c403c1c0c0a103440807103000c07031031442030070100e60f41d41c1c42c810100d05041c0366400041680b607000d8040254100c1c04100144150f100361400103c00d07004c51189022660104051990284042407900c001c0800b0f56a0050246040c10a0030020010303034000340598007440003100504030313140c0c0100028000d51108000070030703082c80904070a504200d01261 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 581276357 1250 581275107 581275153
    0x30c0603180602180d0c060f0c0503040e2e06110106120b061503090105161106070c03050f0d020c16030305040e100329060a35060c040603050702 64
    0x34640c0c049400b076410343c854000998050700c005c00c50714110744586003c02d01c5081c070f402401c00286200302d240f0381290007050002e40c0e00f600300700190f08ac80d140424040100000425007a00e909030020b1000065144166055000702c040500420044c04c125008014018003452802960b040810401c04400c00e400600e40a82d0050744030801580c990000c282181180113200c0070281001041000c402010b602460044101d10070f103400920b8414421191000e805028040a070020004905003030b018003c5116081e00c01d017086410b21602c01c1707022240e03030003903643c200001c2e1300000c00903c081828024540c148140d120010782450850320001c040b40035070b0044e4181004410007003854010100400b5000f15400010225128111842411514041d0071100b003e010a0f84c0428041e14101900320140e5400d80300114200705e100082810035580e82c1e14103240801c4101d0012581107061210b1881501c0c0c012000780e171180350a4004040741c9000b0300200854100c100138240c800c203c000001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 581277607 1250 581276357 581276363
    0x60b010203131404183509010c0f0b13030e04060305030a1404030b0c09090a0b1e060d0e0a03081b04050f031504150c170426040906030c060318 63
    0xf400354003000c1c08240104801038605520301d208009400802c910000b4880340d12200f00c04400c0e00b00c450080841360304e40d400c030300007030741d91018001412079510640d210000c3c180103042400c981c00b0241c03651800504242c42000e41003503040c400009058005c00078181041041c0c1c0c00b006400d29640b105c540328080c00c080b01c01001014554090712581c0714043c0c401440d0030041c2e101c40741c10071007000381c840e500c100c290794018994840000c503603002a200340b18284802400b540340d1020350526100101c145904030315403003481032256009a445912510014450500040441034405e0402070004c0743d00610350717494040c03404403007000200b1450030341e000c959040d500d01c5d4003c02e50400280c205120305503500326034403c4100f0801807151a1861000440e0040070030000e4200c00001205c120300e09501e030f12004904240071800150405a1085800f141d240d0140046880e40f0344481407544954080d440300c03074a409084c410b00c0000d014800007419182010441410349a01080050018034409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 581278857 1250 581277607 581277629
    0x1a04110c0d210f020a0e010c0b0a33050405060d050c19150e0a090c0206041e17030a061203080a050403021c030204090e0c06030103121e0507060b01020313 68
    0x700c0041500b02162510005560061000011070f010140094000d426480001080001103964950054004601c12900b0100c50b6100c0d23502c2c0409070020b002c06501c94815280102c40a250140034400c24103040c051400d4000c2c3c146180c28100029168050441b510501004031900005100012401306030b080030f075000002890000d04032004101c19610601082016170480180a9402a6031400348402160b00c03403007207a190042101110380e411216405a4003480100d004110408911204410400c100401c044150740e03e43c0303489441303e107070030703080400100900c010a01280188005091080598959101580c40061040d24050700c0005408e0f0740b00e001c1014544244011603032964240609000d17803204020080c000c1d44a4403990190700e19240d0700c1865030f94007040c00c040b02c030700c010f210f5403d50b403e540f103580002c2038889504003030040c18101000d19050300c54610b524503010740c0311f0f181c60360050f0800300c00743c42a9154040c110b4001b00410501a200450810241c4444803c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 581280107 1250 581278857 581278877
    0x509060603070c1505090d020f011e0b0f0a080601030c0905041e02010c0c0b070507090204050109061103090310050906100303020613030320031e0c1b101a04110c0d 72
    0x4030642c03041d030082c508040d41c103000c100905050b0004104c2806100781c1c8c2102d42c008104002c1e642250800040e0455441000000c1e551440761600a445600300040101da030301240d8a0000c3c01c103580d2030303001c6030042e042100104240504d0800f09002080c2d040c000b840286001c0d84d6a24a20b115849010000c0d4034036140309055910980003c3e84c2c43d81e01c032100c22070544d1584801d07840d80d0091801114944115a000b04034081240251000c448068407403d1030341d410000256600030384080d080340284400d00443c8019602003015107002840035000242d1030038103032550f508205c00100003294910604a041001a9000a0fa69404526089006018815860103d0190607002020404040401030108aa1819800441c060511038031070507401c40000d000c50361500c4007107941095074542881220b0100441c83c03203805100c01c8500c151040c098400c640f1808890030811009842c181c492240f4100e07040c903102d90440c940351207160300d0a0402d0b20080503074500c3e218101c0c20800602004d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 581281357 1250 581280107 581280113
    0xe090f0403230d0e0a02090f28020d060803030411060d0209120d0f0f0503190b06070f030306120807020d030215190633050405060d05060a0509060603070c 68
    0x100005000203a41d040c01e001c00b5030700b140c01c0000d030404494486020b242c5030350640d1503400028045241c660183c03040f03c01c0d60380e000c690303004100300408410991060300840b000d062100c88048111182c030a10040c0c589070407000084c201c4405400440311640101309000c0407070b131030314841c000901c002c549280d41d0320049103005003c0d0080085140d000760fa40d10a03810502c80224103060786080994490705a030118840440d05400c184104402080e01000811038030013035107407040c2c03448000a00c0070411806c2c0e040484c8895210030030954545800c803d480e410154907014a80007020051340304155402180c41341c5250340302e8004007d202c1c183c03500c2030728200350090040c5a00540f013100c0401c600d20341140740184260600f45490f0600345010305c042203850181c0e501c0303000800c1101c4016114840c0312129200c4982c600c4050060120901c40011155203141c020408810b400c50701103014241281030103280380786600400d00c0384010364204800d5407502c0b0305495215020b031410400303000082c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 581282607 1250 581281357 581281367
    0x1509040c030e070e0a110406090306020c1c050a3e100203250c080a0e0d1502070b010e01060e061c051014040b0906040903050f0301030506010e070e090f0403 69
    0x6200c01c5450284010004998103e0080c5600c074200c441c5017817084041b0141c503409140715a01410022590222081c4003080196000d041c03603c840e2030480329606600703424056801034111041000480010362150001d030f0006040014080d0441c100400c822030002482000701d401442409814070303802c189c0700c0030100704410685034907031a6045680b030038120440c10041c042c56400703214824101105490320b0f4410416680c205810100050500d07000c07100c00c40d4083e0100710110f80c0080304031003a602241c08003074002c0003180d1801006940c2c80c0710340740c0030703014003416071001c440401d41700c004120341500144c1b10400100210cc60694441001d04404c000c8000d0343e40311581146450f04004100032051090b0098603144001c00a918082004120a403043c6440854104103818081002800c03c3e400640c030a83c0701e424400d00b0040803001188554100340c2c030130b45555010400410000c1000020641c00031030b24078003007014900301000306a41410107407400c20131070304d401d0000303091621803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 581283857 1250 581282607 581282621
    0x30c2304030b1815011211031507021b0109080d0f021203070e09060d0c030b0601030216120305181b060405040e06150a18050405010e0303070309111509040c03 70
    0x80342c105650305201c0468100c401a841040542d481100d460410f40e440121070281290030104140d8195004e9665400c08030801c070303120039058802c03207074440b00c2c8800303c80f010743c41b40b00180e0050200141c4c1800c0c055046801151841c14043c0c8681d00740034001c404580510454642c0c140500d5007444410100e140c40d003270550001d482540070003880711320b17907001510300b2503080110303810b8216440fa80d0400c00e002000c10001802e9591580003080047d50050200750700000504006080c100410982c07503013000d00d401c0c22103501d04480c03030408046801d031041d160040b42002c9081702400b42c0c2d8030096560340d2004600d039a0040038920702c5000b03990f40c2085602a010180052211035588c085242e554003083d80e038600d00070484030404a103402c1c90194a03040761503281a211a101d01a084c21005000c003410a035155500c0f400c04a22026007080154040c031003580e0001021a218209841c03c01c400384c5047e40300d4a883c00075004025074210070750700c010004941c0020004683c01040d002481e903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 581285107 1250 581283857 581283863
    0x201090e07080f100b161b0621050915040f0804080d030b03060907170c0a03080a091a03060405070c0506011409010b07050d053a0c030c230403 63
    0x22040030003000a0b4007098660086501d50014241a15078079413405620505025020741c400051011200d20f0803090000702032540101c00c000003c0104850000120f20140c000700c003ca2059844181041716480808018246406003004182096604a03854008404110f50f078600c480d070206050200c803551705940207622002c52503440e50317220394068480345c5007988500441e141805080140c10042100b0b032081038894003503c252814401c2841c0701c68038400d10903045100d1240e2012050302e9a5200700051070080c0701081d03c40701c0c030358401030140100d80c001e0701c038940001c000d0084900d03070744055a4200c00200e41c04640c80d41c480c00121200c01092402a0092265400000303010710010b02e0150361910650762080b20380e80301c0114050b64454820700030060340c031129030701400c18454009481c0305840c540480b0b5a24001130001c0b880d4600716240c401140070981c032054000e403290720a49a500c0c0d03c5003000c0c0940542c400d405400862031000054420782152054100c0700c0411003128007071a8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 581286357 1250 581285107 581285129
    0xf010e04110604180b0a050f01050703020f0102071109010801060e0a18320309060a0509190e0601091712160503120609011e06030b0f06070f1502070809040504020109 73
    0x354913000703207842c8800c0b2403160411034644000003034242411914007060790b40113000c08007403c1d01000112001c0d44048429030850045d000c0003480c001082c0010903603103004065499941c0c51460800010f042e040c3c0c4840f200360314081702001300a1043d08201d07800f400d17030540060840c42c1c01d5198140b2802520700104452810b21042c1c0c188644c610f035040400d6980b000c0342042e01e007600a0b44eaa2807040103480d80e403241052041140d1940f140c00100120480034101c141d45a03c041c441c40a2801503810a040006000c0308000701541d000000e200201100082003020354043c565141e25034045108050a5800000b0400d003510015090f001c22a40d1000450790f607a00ca0040d801284042690114866040308000080702205106810021403070313041240d499900c3d010055009001e658203440d04052804108040d5654440140824a01808100c00940d4041c41e090b004901642d040070841803041c0900d0000c50240c0040c2c0714000b03815500001c2f561141d00040e510b825003030b440030502c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 581287607 1250 581286357 581286359
    0x14010c0201270e0c091807021921030203040f06050417161101021c080402010c02120c01140f1615091202061023011101050c18090f010e04110604 64
    0x3400b841c600e400b1503101200d40b0a1503290b41030500c166100c0c0718071583e070081400382002c00381844072003a079810010900481e200c3c904043c1200c001e510103400c040d10760800e100c22400856800000003900e246591808503e589000e030380701c0404514010700504610358079000207041250b07986613800100c041114103901c4014400c2c4079603803a0b1914004131102403402c1c40410495000003514040a00500f200c400d07890180f400072a887c10000348140c0c1006492024500542c031154030b042c16159688016040c64064003001402917040308050300914003040080010b925080300c15904e800105200c1600e01c0c050500b04000e03248001802c0310704d81841d2070314a20401c104428442d40e03c81703203a02552215034170100300b080d50080502c6029180c10804017030890391411440d01c030360001c4050510100c10003000c1d0840d42120340407202c130740461000050402000d0b40000ca5013002100882d03100d401480c1444510780d1881040c41410650b001500100b41006134050f0580d002c1d400107402c0545035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 581288857 1250 581287607 581287667
    0x301080c0a0b1213170d02040816050306180a1709011209170a0c0b01030b180f07090213080619050604050f07140d15091514010c0201 59
    0x40400101040c46070360000c4001407424114000d0310444900f405005101d5901e050000182401c2d003a030489502640c2000c10804e0007540010b0041d00801003401031300d550412000d05d242048a50070454466804003003008036a400081030f60740000303c2d51180b44400d081040c0c4a14241b20719030b00030500c80140c0e1038103900b03401400182030700079001d9a43c0407075440324030701003000c84014050162190350100e16000750300f0350480052400d0031192500702900340d09600c641d0b600c100203030021180b1000410611a0717845502541515441414001d0180c11540c02c0d080c130343d0354000348261880e161b00442c40040d2a4019561040240ba084051b11241c0c0341805041805000000c4034038906440d10000c55501d003414402c451141d8036844402c80540c552500684244400381e0040c5d4940e0020040d07005071418900641c0003255981084040090814859009990918403900304030807140004000c2c4e0b040343c1e0100b0f514104207080608030b0418030300040752036405031501800422a601114004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 581290107 1250 581288857 581288863
    0x20c03070b07030806101b0312050901060608090309061e090604081513050a020d1b090504020913020307030f05070b160201030b060c030d020d18050a1101030b010504060315050402030108 82
    0x14404d0f40c9408940d0b81e10400c0281d0100f600581340c0000720750044280380b201407445128040ba00070f05000d04020680c14500054130002c8034000c03104c2e51200801c100c20740e0484007003a040350503040074604080340400403900c9801360b160000000980003990400e8081100300300c407103611001e49980c1d07840c2d403070307050386076480340540344142c5005050340020703489070356506c2c60215840e41300002e03001d01952038081101d4400b1450041d160504050a0f210600041c250000c005000b000030101303503450320f8010041c0340040104100740340320002d940d480040e86c0215001003600d40c04401c07a041d036426424084e1418200703401c00c0c522007070000f8191810000380000c40050ba40300342d0303080c040815804184402c5008003011107407203034801d0054400b5000b0a402508181d81181070015126062030040c98074180f00b100141c45507001581c007a014082403135250403401e1001c0c01c05100c070f004e0041c002051071142d03105040805a0b513103601d2a00750041c8180d4001081c000b4002d41d00c80d6146d42d001c0e92 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 581291357 1250 581290107 581290117
    0x915020c310b2b1a070503070e01021e10110c0309091905070903150e0d0507030e09130c09020901020a0303020a020115080606040606021b1011030a05040e06060325020c03070b 77
    0x4801c51130200e603c10724652480041e104200964482e070031034450300002d56580b00042c110505501031290803200b64030000c3c1d1841c2240070140d00034400c0300c2c415002607048900348010030743c03041c0c410001e819000e4000411100482801d0703551515541d9120090b140c6400d60501e1501e4460924040c0b240040d8000c56032002c0d039000d4031609039906d00d41e815010031500d90442a040a80010f4050515580224042e040b401e000c3e080198200900e0030029102402c02c4403050807035a0200f00700000d010410303078080c0c00303031135005402c510b0444070f100080e50351000c3c9a0000c042540000d04140b0061003900880850204010651000c0741c0340ea0941c1d45411086441501032031808400140c01440002c03018a11001d0540745003050004c41c0034451040c4003254076400344a59044180f0b04034000b0801088542c80c1d82c2d9416071605c0c102529200456000b400031880340100380180701d20040d00d4001542000540c06103503800b400954403e0707050810760501a0340c0b6002d00203000813040c0c99070303000709 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 581292607 1250 581291357 581291363
    0xd02120a1401021b06190c0203070501050c040f051009180b12071806030b04150608060c09011d0102032b090602182e0915020c310b2b 59
    0x4210809078042c020b60f0313107104440b4400c001021034214044c44c1b025030f01c06a002111071041d00e04c0e1180740d898860035a503085e1107500100c40d00040c100281000c0e00d01c40000380c081180c4020001728054801401401c3ca8056001d110010044102504240d41d00191010038058018405900140380703407a00c919061140e0202001d412020300102400c034460401542e48c85501c010850b12151180301007000c0c1c2e05c04880b82d4079555800403403040341c10480c052182d40111122642c81031858001005180e181034091041c0d103004040220603a000710945010000d00f036842031186150400c1c2c59061040396030b10030b1105140c221800b0511400343c005100c80d89001062034100e01c000020301401210718201540ba07e00000d1080c20000f81c0b04075542040d54441c03800c8a503003525000034040d03402403c00d04001690020200015504119a400441c0d2080701d09402400c10380c0c5191002c0e95010385100680903540304040505aa9480c4610548084420b10300b030070754802c94503106003241c5080c0c0a0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 581293857 1250 581292607 581292637
    0x8040213020309030d0906020c01050103140c03160e040f02090c072001050714010e120307080901110a1808010606031d060114010503060d020d1b050604050d02120a140102 75
    0x4040521007802103d01070310340200114900242081481c1c020310349400111101502080b030441c03020004d018550185004103031202109041c2c810b0740c2e00d004400076030580650021a0305a600035001d0ba012022505014050000c507039591030005920302007148025440258402030212085400019003c0b02e0f100710980d92401d14900110b18201c000340c81d40d140091401c00c0b1981c0010241407600c000f04e6071100000c00d0001c20360482e64100080043e841140c000007104114619a20011b80381d0407850010003004070802400401146204c0c1d08041010b0040422406408400c0036841100401d0030748001c1282a0b1101c00040c05000c004030f80032481041d58410080041c0c01086442c100d40c51200000f4a1022403c0151920742004094990201b0903030241c0340540c680c0c0580302104d501c01c10300702c2d0390410048810340e4140080d41180d805107805101c01e21a079129803030356041300e6404031280700200d060030031194500a04460001e260038090240c1e0800b030380054000e850022149415 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 581294964 1107 581293857 581293879
    0x804080109030311090901150c15020a140c06150406170c0301060f03050601050d06110a05130b03190b010327050c0d0f0303020a050d0c080402 63
    0x88194540d4664001e6010580c0c10b10880d0544114203a443e4103000c030761808a2900f0300305015000800c0c44020051102e00d00a04076541125400101190300c1400004520041d403c090088030104080044410f0f52a9044040c3c5000c151607038024505545d42c4201e25040e203010512030358102e6541c0c0070101d0140c07515400c000e14801414002c0010003001c000341802c40da103c0c1c1c030410b0340c100d20500c107200007000800e03618116041111003200409070b83c2041f01c020b1000407210706029200240f01041603800c180682034505101c03903159a400c1e41c400b6954441d10084605810800b401307241c43d4171070541544622180c1c070041c900002d20101100302606003154201c2d085030340030107000c00041007204c208244150840103035405203000701a1360303030800407100e0741c41e004041c1074001c1030220500c0e1003034003070b100b200040000901803010407410190400f0b00944041e4011015409 = true := by decide +kernel

theorem cover : BRFrame.Cov 581115107 581294964 := by
  have h0 := BRFrame.cov_init 581115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 581115107 ≤ n) (h2 : n < 581294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
