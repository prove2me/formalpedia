-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:43:45.87451+00:00
-- url     : https://prove2.me/submissions/7bab76b1-2819-4296-ae91-c36556608227

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 916007194 ≤ n < 916187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 916008444 1250 916007194 916007201
    0x13f0309080c01080618060d060c080a05071b110d0209090d26010e1513090611030403172203050d0c020f2a04060f170d02063903070201 60
    0x440f41801209402c0054955403500b03100c120310001c400881540d2245030114041001454006100034a802c005800160701b18030f0317180c4036405905d014405a56003242c1141d094103a98030905a07445600143c1c0c0000314483c02c507100301c06015041c0345802e640d64000031007070360094518840541044503040f060591100502071a0a540c04d261040000d03250701141b0120030500c0b40952480c01d41c0041190b1404044070480c8080e001040c0c8201084890000f0b0020402100102c0d8401e241c44c4c087c105003240c03102968403403501074444200590588000e00e0060070020103003000703c42c1101d08840305d0071030b4a40760320301d5078040e656041e16102c00c00c144c00100d0b854402c0341820740d4000306d0100103594002501c500e0303d00d0041e0314400800c9001e030800862100016903950720905000000c24941018600c04088511014800c10300f600c0508050740c13540380c40300510300180c010000265000040d0250380c80004207210240c232280ca02c1e41c50124001300c44e40e07100d0407039200000034014115424007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 916009694 1250 916008444 916008463
    0x9090e101b0206070f3005090105060118210c03050a0b040210050c25091107021011060714041706040501061a12091204060c0c0608013f030908 63
    0x24011044420180c0286c1803009042c85003d03e2203200155588080c001c08811458040c0c0040c03d00c00c5007031404002d03018003001c0f038001c0c0c00642d00902d14200000842d0240c02200c007540350030085100c10396803038a4a408080001d85001c00002c90000c00550100000002e90b4010380d90710150381020f104120a0f101c24bc290740c020080d00b80300c011503c50700442d149081490007880e003016106170039840111031150f5480249540e10380325064050000c80c800410100e0300c05c91f10450504c01c9000c05036801c3c010090311301c5c4103034030450010350014000c0b01401d1807030301d44c505e0300c505082e61440d20700318809892040185d5900244140f00411009002d210080c0180b03d00000c8106200b8030342d82824080c0f521845080c011100101d25264000d00009103150781d290201e81d40c070760321148084c114584000e404c903280c50001e040055018460f01e01241a0f40020040a0381500c0300100d5903449211084000302d0340c3d640202030b1600d2142010b2071044180309480c0d1030b0b51285403c450074100140e00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 916010944 1250 916009694 916009697
    0x403120603020303090f03010e0f0a0b060102120307080406021b0a02180105030d080a1d0a05100b011d0a0f0603150806070f05210403031b0306030309090e101b020607 73
    0x10381800103030307008410f565480d1416105031180504090019026120310341c203c0555000d06452001e1030040031443c42c0701c3c0c500a90049501b0b8903007000481e92070b01409000000c010050000c142c54611481055401c28002c901c058145585188549880204490038407090741c0201e0300c0c0c1085041071040030b149019506206007241d0315050100e13465140d4000a0810020801e00150598403164007071440080d00e2041c1d0104005142e082c546c1d1009608019501c52003582414601081c0034059007800758010707910304104403443d00c410a07004030340e40c2e1050740c40081000e0105440316814500c0c3d004280940d40401e60a8003170610403101c040030b0f0002086600054101b00a05401081d08030b1450280d05d07005a5656140001c180c21412080c7c081403681a101c3c140003d041d0301d6080701201c500c00055107040004501800e0741101d200e8440113000ca032103944d0801c02030401da0701030602040c226003590071101c41d810060085420708281e0760350b1b80d1061052030f203001d07504118075075026401c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 916012194 1250 916010944 916010951
    0x90e0f07140607240207020310150b0a21050717060a0e04050f120901030c03051b0d1d07090c0504060909050c04120c140d0f08030711070b03040312 65
    0x100031040252001c00001d440c0585000220300e4204101c80d0024070802101a01c0000d484505000c14400b030740c0201c2042c0d21038230a03074502202903042031244d002800c1c0c0d8240080110b6181c22205110b980054031500c082c410082070f45051105041c440b000c4d880b2031a00001740900d00880040e02c0311000822002000f00003100300320042d00c401005500381c420448100d44961348030325289142058000d039040740b0313000300144443e14912080140418013400d80703090201c3d8910600031412038004965811983c68580c0c1310740c2040c000c10004050540c4059008074600021101fa40c012407401c4d0101000c640c0401801c00c1802c6091060207a6a8036500d0301b0b41c503040c900a001001030b103c9010b0810300715030361030200b4464001501210300030b01e83e500345030700c81600c6820296000d150a104505001c3c10914144c0c9052070526041c1101380c1d40645003428031090794813803e0003500000c1039442444001e0130b628644000030401c95000700040350809540741341915005040302c0054907a10340c502e08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 916013444 1250 916012194 916012199
    0xb060d0507091e1703090312070309051e010e0613080c0301060906150513090c03050f06010302041211030f0601121202070605090139060b0f061b0a0c090e0f07 70
    0x10b100643d08111000411946406030300c9443c02130440c420300c0c030300503810b108802441804035441c0380903080c400d000e230311003020913940c1d0010b0200a10a900e1180c000c10b0300715606150b9503004503103215a08034040c14a40c10301e0080c400036880d03034407103401080e45a40040400c0c4640d15003406071001405025206000307988c548070440c0791200d94108400c086c000042601c01d105d40011000740020511100b00344445644103c01400418081e103481e1410301e903800002d0303510350082c001c1f00c04440d44400c0d865001610f60719030840d0000500039242c3d050282c0e1148460b001010402c0790301030200e08641014040b11454601c080d02085480201550002c01d400c022464005043d100c22040a0900d66040c030085130503e085880c00c0921400080a45d000803014802108001c1302011703c105400c11481d6480c500f00403103503030005003071544082c04010360700544840da480d9101122114044654045c0184e85030200c803801500071007045035641000a0b40a06d04111810a85031400d018140d800d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 916014694 1250 916013444 916013489
    0xe0307020f060706091a27120d0b0a33050909041109090c040c0c1707080f0d09020907050c060103080f0913060501020c011805040902040b060d050709 66
    0x1070090110070712403400850018240881c542140b0300380c0c1e03404110304609603040d41e0b030764840c03a0341070b200f8800c49921403041000c04415803481804258400d0000d0100b0303408082c2c40509a07002c600b00700400350f01c40107070b1141515010451805071090f2803503e45c404c1d043e0440c40e8641e90300b00c0c0f80d01c030303414010703121039581a0b805c0011510502815210355180d6603560401403440b103040501e0030340000d840e1040100c0745801081040841504903003d008102024800b00c41c04042c01102500d11240ca400c441c048400d07520040a02d01d10072000b15050018040881c6c0882c1c11804810303807127a0f00c404042e406c52a203200c10550011103401d1480c18002c050940c26031350301050000500b1b5090010b5000d8810a8030015a80c50040090a41c022000e145c0c01d50409000540704060140c460040400c4c0107600505804402c0100c840c2107401c46850300c410000600369260045e0382180d62282d040e00c1e1516840001c10804522800124050504d181e009000d400982e0000c04c0010101c0065002c4a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 916015944 1250 916014694 916014709
    0x141503010b090a1508160f080112050109080406111e0303130c120507090501090b280b03010e060f0f0d0f0206120108101802010e041a03030a050903010e030702 70
    0x1140d03800d29060b00d07807128501203400d0a581c2d40140502c0300342d8a08181d00107601c40d070554800c0100144d0400341c241d401c4402d44a030f42491a8070404504104014041c0351001003c0b0340314203004074000b01e01d0020342c0e00c842940d5801a041000000ca00019a0501d081c0c208801c420907191100f03046191510400310a4503030101030700d500021058240340d0400d11020103ca1030191121002502c0c2000d150b2a0255071914584a01d034031841c2400b00004642d20607102c2d043c980740e805842050b00b0a070f030a4668030070290303440c190781803c0e42100010941f0900f02014502030030920407100481d040c01030801c810445210b05041c0305081403081008075890750b05220b104c49078050310410503010a84006081c60207007480300d216445450300002018000054592400d0b644600100503e140842d922140c60003e01400ba020412103035261845040c19440100c0688510010000c01d10034071000900355804032029000007400410320391680d203000e200741038220142100851400100c0d07408916036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 916017194 1250 916015944 916015949
    0x618030f1605010b0a270b010c08210709060206060307030c0b2508040e0c030106091503090212010605010e2704081306170718051302040e04080414150301 68
    0x140300304200300802c035094000380325080000301210070302511404c10a00100e100032640390201c01180759561084264841d0524060041e5114160511941c441c0e08103a400550305e5284164640e4002d0940c10002104500908142e600c0140080c85d110009113070140c007924051094000b00320810000300d850b640482141c2866885a84401c2c0e1049a0010680c296801c040782241920f00c6c0010042400000d106031a585081c41c11281c45990040d80b603400700f400f540002c140444428440f41041052580302094103141c08101400c050303000c61200c0d400801600b015a448540500c03141da0007550042440740d06a680240e00442c050000309840807142d586a40344c401c91010900740b008120440c1c002610113490141c00d556030f518010806400020441000580d0b40b0210b01c0325807086c41c082403584491010251114105010820000f4541020100c216400c0000149801c092800d00344150700500341c0d581c98030b10380264a0740e07e0720259400c0d441584100150b00107002d808003600e05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 916018444 1250 916017194 916017217
    0x7060917011505120a08070f020a0f0e0a2c15070203090604140a05091e0f0c070b06120a1b05010207051f0c150218010e100c05010908030106020618030f 67
    0x38082010790b01314180201900b000d44070780c4000032083c0c1070089070365091075100c1c402c2e102e00f80701540d1005a02d00742d05150040350400904800410b0482d4403039045925030400e0211105041222454104a0121080c040e000e041c0c100c1001c0b00c02d80c0811f02d08071980306d445e1340050351500f03c035480055002d2103140104035505e0340c182d03c1da071990344810518001400380503183c207549051030007500000d80c0c007514944c40d41042d5603002800306501030446d64003e9642d0103541d42401c1d056a6400c0c41c030403000f0f002c0ca4010741740982c003079240d12042050510084c0116081c0c081002c051388a45058401074200c04e0544d13005a204000310385400c06c00100c4200c040800075460700080340c1c2250000f4402001501c0788580d0076820f09a104140d000b0000c140c103c1d44020b51140d2040c0c015150f07070014035003c03940b007190640c80e4000301303010781c6551401500c00c01c0001170b80c04030b0b0742d0fa00c1080d4100781c0040006921034401c011040d6450824000201c4a100c02141003101c02c40341c52026104003550b000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 916019694 1250 916018444 916018459
    0x70c0e040f21170a0222080c01020318040e0a06020f0912070e07050a02010e070303170709050310020c0309040e0114090102120106201b0406051512130507060917011505 74
    0x68040c616941a10601c010f000b502c000c0300a00e44186c8900d801181c001c40006009100711503510358000000c40c0c0f02d68541c0350f20035910b90402420840100354205511300c036401207449400010317850384000d21242c042d0313108035501d80c0742e14028400d14546100c1e00a40d0f0b0760180e6030a0101031807130485c581e80702c1100c2c03070310a03034851030403c0407800b4040760300c1001c07458451844080109030b000340c0d0034002040101c8056007150348011044800030164880c6503016046000b07480e64850781c80d001044068116401c403440d180b01d0300085000c8402c1c004041c003c6940d20001030410320440344580b42c010050320020750402d01c1e1341c059032030514018441e400c1440b40d03180080000361801210200100030b003c0a45807040d2484291509c052030200400d40700d61315085012990340790644010f01040d40c0700726038a040c0600ba0150b4840712a028100080c0ca032800e864890000f101009128003a000e650b031079039190b902e040ba520840c40f11030484001d0a904080c4540c55049076600311404490044400740c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 916020944 1250 916019694 916019701
    0xe010609050f04060b190905010612021806031e0103210f0905011d040c02010c030513030c021309021906030b0d030c110103150807171f02070c0e040f2117 68
    0x8407880004940c0e4030103440d01d010000340a607265882239049449640b0750b90008100704a61901b00e20540824802c40d802d0940003038000c0c24040003460b031102c81803a030340d4000403d0b80c8240508050991040300c1c0c4101a0a00203004c0680e45440380c8060300b50705060880701c03403444000c5c00c66034542c00703030504000c2c0400001d04140d0351042101d0001c00061700c01c028507400b10360028080c2c04038203902c10102e0705100100b0404000100c0000d805074255540c0360140d48990300b000b000204200415032520340f102e080c8005079031a507400a80c515280d04049407050b140403405402e40d403a08079030728486d03640100034401094109401c0104642d203e00d00c015000164001038000b00840180c149100b203004002180041001501605851441e00c202c0e9100a803c02c02640d14007540141c044c42410f0304100204501d031a030050a81c10388502500c142c400c3d01e034402401210320807642994650b495110786800e1007010400003d40104400c040b480b5001a0140034000024196248a07070383c0a20001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 916022194 1250 916020944 916020949
    0xe0c120c09190612080d060806060a0b03130210080f010e0c25080c0a1502040311010c1a0720010626012a11010e07060c08070210030e010609050f04060b 67
    0x4a00502001e500c0004980c9217030034000c07125040700020244441c034007040803c18410000b203c51007840020508400c03e401c1c907139450101d0308003034000314407a4155100003005a903030f611781c000d80000301d907a4041e051031301d080b9000380480c042e8014101e00d41c0c51000c0c081c2e00d40c14202165a40d01d102c19041100c601c07101540344035402c1040f0302900c0720307030f0200d032081e120007000c038a801c07216024450112005048070008402ca105610000f005c1c14012f50491241e9402a03400d03800e06801f0320580007031540c4090341e0b041c08070021188140000e60b07900b0840080c010003d08201c4455402008201c0786003840c842440043d40a160f010380b1201485c4150381804094000251203050f00006003410504041e80c54412005c820313104000c40c6241c3d55002e0644e00500c101d0003a042008024202540b4148007a258124080340998440d5801c00c424009030300c1e002d4070f44900305880d550018000ba44903100c40d0031542c0710380110101e181001e080c01241d0803994261a0071640010001a82e54940c500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 916023444 1250 916022194 916022201
    0x2061b13121e050106050f01031503020f0d08040608010905010909171e21060306070903020f01034d04050405060d0b090102030a060f060206180c040e0c120c0919 71
    0x218040b40c030310340400801c00190880000c44009a522802a210020040d0705490403540d07403505c5256950410809450440308200e158000605280d010f41c1040e20bc90105912642001c0013207070b01c1000401100f10740d4483d250040101e000104200342150b031312405050755912a0032512030340400c103424503480901100601510001c18240c5c0c03698042042e83d00e007910102030090510303081000a20034207010070400d06c1407480ea038034012518103641c2080107034600411389904055444040e60a05c60f4483c14000c9841108511201d100b58131000c40d44448005890016a94507800c1414500702c5420301528191102110003181c603594001c00b08401400c220300c00f42040300c010060004001042d030003140180d2000c4014800151994031402010403030303205040060b84014009400b800402520400e4803000a003036604003a051000181900c520340340c040025000340107071410900c0c10030803582803094498040d200c011b043c80d002a4144c10020174501e034400b90404a400320084560 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 916024694 1250 916023444 916023473
    0x70201020d060f0305010b040608031c0b090f1801110d180803010e01170a17090109080609030d1401060206040f030e03030d050109290402090307030507030302061b1312 74
    0x103004100d01a995212803109100a10082d13845502c3c1c1007e418086c1803500460064509100c025854a25402542500320a1818100704c002d40d0760600d250441d65101c2c400341c014104442c8a40f054104082c0524100e14100d008004aa141402c0400300d401301c68161245041134200014041e00c000e25008800c111802004240c900000004a01c2d03410f20b4040b98140c59810445298a0650580306030b0b40d0300c40164040c05699843e949044e0006400d1f0040c00e2a07101850002101991005d40f24500103056403400728070740000c90601c1d40c0d144076220300f00c0151184c81004007954584500a5122040600080c012804103410782043c11b0203603c00d40301c24003000e802c03a41e1b118004880c030001803000f03000f4542d07254200351010700c03030b4504004e4002c90b000280d1100c040d81090703102040001d50084600b65054050710400002042d81070081c0001540640c0141c00503280034403003d040103002081550b110101401141d040c2d000440d5044c0079503144e00c40e6011040316a0070011211007080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 916025944 1250 916024694 916024717
    0xd020d050d02011b050702130b04020c1006080d0c350a02280b070302033c010608040507031502090415060315240c080f0a0e01081e07020102 62
    0x51509150350358154001d040c41c0e1401990304180c000d244a0451700c610a0102c003961041a40d0300e00f04001800b42d0040030700540c0108010701d0324104200c00790801414a10b619500d0b0b50b2104204078192041c0b140700048800d1b842c046d414890141c1c1e03900410b1102c0c0c03501c10604182e81c84421030f1038404040004110030320a03d0344c2e07102c0c0303005603009594803070b600081c04069000b005a07a44051861109d00001359215800410541d101d203c01c4000b5040140710341603505644071085840048041003014280141800b020201d01c4415401105501a844442000641000c000120300f000c00ea110a0303d901c2010800d14805003030407100a80104000c00358442d01d8502d61101c0d84014440d070b00e0498480e92000d120340f140580f40c54ac6076050600c50300f252040d060f0b0540c0c12a2100c803005003402e242604184003146050b13268026540c001d44d030350b004c0c1810700050490507960003581204001d1401d10707002c8010f1a00c0c1440780c08046070040b0b0002442c41070030106980c5030007901a83d650320400f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 916027194 1250 916025944 916025953
    0x9061809140a06150e0c1e091009141c0807060204090c020d030c050a0c0312112b05310b0910051f06050d090b010308030f130b01050d020d05 62
    0x2c1c2c2030440040500b442d80341c050210304c0400061510a0320580c0b031041041c82a07040c1800d41014042ca12441145034451a0380410003515809a0710120600d40d82461607480e4504c1c00d00304540442d00301011494548030322210707007401c0c10f40810100d008079050b0f07208407441d44482d014030340840a40100d8002e12440ea0074442c60351035161b80061000b5404006540900c0121200c07141070310644183c00300080041d40036175840c00800d01440003041030708040c03540051480120015912039820004509450b1444a028075291043c41c481c500001d1513103460802c0b45080588280030f600d444400c01120200c12402180c845203c405d00194900e600a20061400c0ca05250220707203603480102d92128051900c1d000c40c00501e14102240700b507100c80c03030301c2c10740c800e00700107003600c4a420070140f003140240c0700c0c06004000707041da580c510700840c0304900941c1c4a05050318540e45219004001044c0c40003020024008240007152641c11100e0541e00e56080000c2400440d111221009024100d40304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 916028444 1250 916027194 916027213
    0x507060903080a05060f0f0d17030703091a0c0a0c0602070533090703020909070b0703030221042301021e0a02010c020601030308010902090f04090302010c0201060906180914 76
    0x8020344841d100d03d044880400003503599a041104030040c1c00c19464000001c00d40d2041c140c10700c405942c01c9540070301489000150080d46101c629841200e074840081d40341c4030860f04000c1e030480c0e01c0b480c04400040d8241246050302c925030090003010100ba00b00241420b40c02f0500c1b24607411140450340000c00d030f4007000b0840d04840cad039000321000f0046420a0700303581c1c022480c0305140700c0740c09000c004014000072480d5808218010001800031a0140603a82c000145562090010301c0d00911949001d600c03401e040d82c041c904a6100801e900842c0c00c0101004001a840c2d00701650940318030503003601040c884140d0a00a004140707100c0000c0d800c132420b17004920a030304007402030b481d2154000d00000880803002c0307848840c01e200c018042442d10006000c0520150094016840b020b80312280030000c0c000003805803203600d43c0a402507591811822100d0764203009540290203d103505000c160300c0c0842c450140300003da10304280c2a92a010f400801c03031020402c51041c101002214246c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 916029694 1250 916028444 916028447
    0xf0c11030d091707060539160f060203090d03030204051005031812270a062606030c090c0909090d0305070201050433020c011508010b031c0507060903 66
    0x340b10f015015950303d00000c1d41800c914002901810f8034442d40e107560410f10400ca05100b040b88200c0c02c0d02034290200c00c610b031695549420340001d14036040007440982e0100702c5c80d40c00080f417a0840d00000c40c03a90400d010151300001101d41103242030f900d11480f2440e9007811070007070141c0d82100f94081c803803402800305560320401560044002084d03001401000c510f40c95074800c5001a95406810180402d40c101a580015882c2507210700d1143d615013122803000600c4c440780c1c0c1c0c1006011a007c84074000311540c5140f292103881d403c91543d03a00500b0001c001aa480d21031201e0b0134032541c01c08002440c103212040903945d0280f4040c040e6032050a221010742d848500004648000034a030a0008800d64814050759001e143c001c1c07602c0d0a8080740d11400da400714030649a9005041e40c02c3c0301d4014078102ca10040c036a910300c000000912a00300090140b0240845e03200c101146c0c10024001004e5a012030840d114020302c0b0013004004142c070300c040c1c42500840101400d520301c0c1510300700515 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 916030944 1250 916029694 916029707
    0xa0308182104050a1d07111204060305070e010305070203041203090e0109020c0f0604080f070501090f110a141f0207080a060209180f010302090c090607060905060705030103030f0c11030d 82
    0x120030132500341c02c40705d0301c4040f10140c140ca21285444206400000700c0c5419018041a006d0502d561080d10480e40a8100c00000b0f64019480000000e40e01c0e410811b0803a881032000c130300345800746814021410111802503a0b40110301650107594683c118040405008400c070744010140c011241e1250b694800903000250000a0741e00341c64040c24079810301824000c50746e90710072a8050405030034007a4290179125a0703042043e00300d90035035841a06002095100c1081c16007144160701180b4510128000d00048042d80d520040b25000408101081541d620b40c542c183d02c42c0b5a12a5407205941c10003c0b480c184440c1d001d00c08d103001c0c0340b006d502805015002082d00c0441900c4815524110b00040484241c088581540320710038140184011720b000d140c8140c100492a68a6060440103030020744943d0000d0320855005550740140010004140b00407030340020981041d90a56146840c098168281620046c0030096003e03004000c00c45404c0e042440c1c214060201c0780c550102d1030014040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 916032194 1250 916030944 916030949
    0x3080a111207030908030a081504020f070b0412140d0903090e0c04060201060b090618010201060f180b063a14070206060f010c082107080f090a0308182104 68
    0x1380c2c8040c4041102e400020440b45458010380c1c550700195140d509841c0d1078501d201130641d016400b0401010a48803500161032100e0003a43c51011f20b061919012510000e210003c10501c8400301e0309614410001d00cc2d6094503150b0000414001c0c0355207000c0303480c0c00302074000511086040041c0001d19a1403406401561042e4000b0481e0549401120049020309120300ea8000e40800200c8040c10240704009015001800042241074503001803100c0600190404507030a28404012141a8664003d90a034802c1c161200351a142c11940041e8510700d01040c1001840710004c441203011207092032540b0302d511605401c11400c08644100514040181c030f07645c00501c5501c0100705286040346015a42550503181d25007505240e40d2150754a422904e00d8483c180d60072801441131182c1c000c1d40510903681c070ba0300c8030414a084200d00100320805040d11030182c0c030042c00580081d802080383d83d000750f400b20540e00c0001500c18868a030012600010344c000b400c20102071122104903029100f0f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 916033444 1250 916032194 916032197
    0x10e01021c05130222060b1801120501050f0616150506030c01080601051e04180209030d1805060705030c07030b090f031e0306010c051b210703080a11120703 69
    0x10310340f2040300c68494005001c0000e903224965203a003105a20510904c1181c96400000104240341e944030340d172640760442d1083c545203000c1941c1003817503980c2c0a08606880c0842c10313001c2180394100310126a81141580760940624400104400308107038001690154540c03003054440701d02580e00e0102d010b0036054038441e001c0e11076a9000e0445600909141c1e1103158103a445600f4883c02c0d2076500320840c0540c070181d8010760304010205210100c1500707101d00c076221807400350340d941080c0300307152400c004a07580904108000309212a004d6803807940004442c1c02719641503c0e0b04003814483e06501c83c8176602910391052140000401543c0c1080038821030000054800400082e020a41c0b00d118416188640303802c250501c0881c03140c420701460300000e041c03401c1c0364001450342e603451400c5201e00c1038860000d01c10b00208090715140701550305040031010000e025030400ae04003941c58240e030000030aa15000b04203000150301c41e52080940320810000c0f6661a00e0411100420b039019010580 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 916034694 1250 916033444 916033451
    0x41104062a11060c0a061536110c150108070312082211030f032d07050601180f0c17060402130605090907030627021c0c0e010311040905040203010e01021c 68
    0x20764101548d15120364000001381c410280200303140542c11084a00c962855499a07070002c00c2456503000010340003d0704505d009201030f0452071150b80003101c0c1644032494542c091001400014882c40e00c918058180381440c4540b6154140150303540741201040704028003110402e0424410750fa0304800f2124001c1c1d007a126050219034120343c6a00c00d048520782e031a80500300b01324045051b0648000f042c101c0303484c16070602e00e4690301d0380d04060f001e90088550002c60091021038820a1144040b0703000101020044203041c07890241041c902d03e0404002c40140400080d00ca071165011501ca000c20310240d141295184e9001901c550400d1100d07502401c83d410000b4020b60107442100c084d61290001c010390104542c246d03090500c5080080d6070307100c1d020f0180030400d40504501102d84200c1ca80003151618945100130501070350a00305a040504180600d40f5044000c8104d6080d10703c82d92000c101640c4078004680501b24900c00c0740e5a540c4005030400000e0000c1e220803007189030001062 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 916035944 1250 916034694 916034699
    0xe030a110706050f0c28030e010512010306150b0a0903151404020904060e10060e060316090b030a051902120109120f0e041104062a11060c0a0615 64
    0x403950341e00540a076002140c000c10180c82549071401c007070700d0011100c2e03088544860a4003248461880c202c20611225185854a2010140c21140100080c1002e10f8074505040c400718424654010600c17000d02095509c01c46200e61803c030144441c050300880456965440307100d480241401c445120994801d480546080014440da01850410015052070f4448a4580b0b40800907240405402100c8040d9036460200364a001440780c01d084004031300700040c9031450309005c017803404e5001b8039051180c0c00c5a8604d080c0f1480a030500016112041400141401c603100824501030703591034040d00381e02c00e910801c590b003024861480e04040c800d03103103507103107030f62003401c26084c0c030303d2200018003a50418088211940c410580310214401d50701d08070422402210100b0f0480303085000010900703600203001d11280d600700507941c031488094198800b403154564280d0b001180726900090094a84142e03003d281c0d41d03420306451460442100751807200b4036501d442402480300e0300c801100a601c0a100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 916037194 1250 916035944 916035977
    0x51617180102010e03040501030e0a06180210030b01020a0b0712020c01050a150b0403030813060e0a1707030e1507140a020117090607200102040602250305100c0306090e030a 76
    0x210a41c079010240110f00381b9041034019005404101000e14092050a01c81c0c0b000c43e02d5130080c44929481000c0000542000d0b0062107880c9100b012030320281420549509800c0e607000600b41c00880d0441803409050329802801c45085c0141c00108882d1070010440080920041d44940e00404207404100049180c510100300304922502c14544090700a20003000428055101694480d80110070341031000c2c3c040d680d12048031034a0740d25271125400442c04104000842c988182c0454103f201c9500b00105a5801002640d07904003030350040c10768060200000ea880000c2d10822a0301000c3c1c0551007409040c03295540340c0c0840280d0000e00b8603912000e03185504901036000c0c11140014100750382c2c80e00d80039102c040c201100211314400010300b50015040030300c0908007500744e0780c0c040c10301602c03490f1201c110145000c00c04419500a60310030800910001003044280a502c0e80200e24030601100a1340200b01716070004c400e150070b040c1c082d0b0005202000403c00c51995071150026205882c51 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 916038444 1250 916037194 916037201
    0x1050106080649230c060f1b0a0312060e060607030c1401140a020f031b0d051501031b08220204020a080f0c1905161718010201 56
    0x1105500a88007000d843d610804010300801050320030303040d07001c00c80002e4450b03861404000c1540d1200003191265542084540d18020b01220512604001c511070001201a20b6450844840f480344078001030b02c03100d00d41c45a00340c401c120199000d07110b510018040c12612100b00c0030081740010103a007840310036100326215410544000f48050009075881e10306000ba0b607071040700d082d0240201c00907001d001030f8005041078851109000040b66816040d07014004462000d0301030034400340144130054031144c54005a0794004c0c2d801403d0019010300d425400200e21840300413850070743c205400c1201d481000d001c9541428020303078040086400c070b007010480005c903101201002030450350200c2c15020740400e950642403400550b42d00641d09540c0082e049900010756000812041402c010340c020b00030440c1c550040c00064207a142c1103220100d01940c0c0d0042c42e20324140300c0003041030a0b924920200d0889015401000300100610b100308500e0242c07c000750800c40c0010485030703100c49510600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 916039694 1250 916038444 916038451
    0xc030405030d0c0c061a012a0f03051c0203190e0a020f030708060a05010f050303041802161e020306160917030c07060e091302131a030109140105010608 67
    0x10050760034185210580e0019250b40620503041010001c2d200011954034402e4002c000d1006050136600d228003800540340d40c078445041402031920341d0030b00c01425181d1000d6118030383e2001c0000e002001d40d1500303890a0040e440720b26480031204031380300581c510581c01140250030488502e0403010f141d241c0601650000c1c1c1d902405604428108001802d01480c0c56116110040a640e030050300c8442c00c514004085501030031060700e50004008520300100703284060f00042e0065898241050090300282da40d1100308000968006150043c440c42c2d4284121003a40c021205c01c2544901c10042e03403d10b0f12100c0c00d0b4881d004100c080746030f180141d0418648164580c580d40b9015207002070010429440ba12008468042007000c2c24250405019100181503030361201040c0e085508144108942d00800d4402452104c480100250799204140c0b00c803007a0390303000820324404480e160302c021f0f584220029059805c21108000700b0035145040c440000c50800204a181c3c0c0c1c07400308030380c03407403094 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 916040944 1250 916039694 916039703
    0x61c020607030e060d0c020105061c1e020d0c08010218060a090306111614010c02060c03041101090506032706010b03040b0403210504050c010206010803040603090c05060f030402090c0304 82
    0x70440c1d000003902840301c000c0d0742140285072506010690740c00d03005032125085c4440c0140d5544003045064a014498101d18100c0901e00d000e110240c0e6442c007080c108482d500d90341041c1117180000031540c2d002805000d480d8440c8160300816544d0004c40d007c0d40189040344800301001c00f8100c0542041002c1d101076004968a40e00803a1454452400514040301c2d5403080d070008002d0156804036088803d00703224481c801081c82080132003109421921065018811034016030240300040f105c0c10203903500550001c04102007c0d4540300161880b9000e5401250441004820445411032160041441d402c2c41c00b104280e4528810506403612024080d04980140500200700400c1c10404040e9115100e414460b0a580303180e01500f40e4070b1510303003980c80240e86034410001000401c0c0207812800c1001c3c00200869410092038a40f240202d0242e0000c05035242c0c003080a012105007903000030f00014090320750782e110301002e602d00381c1d104480c140d00a404402c0030a108101c0310084074401c9400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 916042194 1250 916040944 916040947
    0x1030c1b0204020702030d08040210050301050f090612150612030301080601030f230a060e0610030b072102070201140301030c1208070516080f071a030a150806061c0206 74
    0x610101a0500e0003050059801550034041c07580141c0701000099580042a1140328041ca0503204007e00b1b00c1100100001300201800104003070746849040150105003203c007030900d60385040c0810403a030a85080d5804130b1142502295000101a096074000d44090342d0200310b0b41b0b405148640d903417000384038040e0706070701030030040003c03070100050000030900c9140313110752401070707008008280c106050214000ea085540340c6c40c100090352084014109005028040078540300300342000c1d1800d1444042c0c80320210500160701580302d071007146050708120b2100980e1000349500807009400401c8201d01089090404800ca0303080345050320304896004118403040d504020245016860864044071444c80c140460800260107104400c506000c40444114036460400b6403481c24441170081d14080d00182003d110100140c0c8a40c01124080c5a0f100e0703032520354108030f5004181c095882e10990380c80c81004104928085500c0d809404200c844400c40c843e9011048221496050001e600490 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 916043444 1250 916042194 916042217
    0x1b0d1110091a04030201020702180106031b20101104030b0a060503030f0f0f0f0c06061f030b0a05090403021606080c090d0201210903030e0102131a040506070c050102010b01030c 78
    0x1c80303002c010761041c8644005810040e6550101c0c3d104400d2003111107600c41040010320110342e06228071041c1107a00301e84000c181000700c00140608660001106c010880c2000b40d102e820800c01200c03506000c2050101300455107080c0410325500076000850b559030810000c601c002c241400f4510903078100401842c68051640c04200c569400900c0d07400034860117004061040941030702400c1581840c4140654a10340d05264034140749008261134402d084021480d49802d076070b6200b44520b144681000910007480350005070284607180e110650115070b4200b08004c041d80450314161512100c0c43c104000c0d621400140c034078103002c5551428003842404068800d01c0c0600700c0843c224018108050303041c100241165030005000a040d8403076480790308007000c059051160300d86411090008500304043ca682d0052440300501c1094401e115190803200e01502c500300315001028010041981c1c0c914502d08900300c0c164034481c41d03003d9440c010825110f075009000b040044a00c56540000080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 916044694 1250 916043444 916043483
    0x10e0601030c1e09140402040b040911010302090a080f0c09070c02180a0209040509160b03010506030a0b01050d390c1b0b0c031305011706061b0d111009 67
    0x141c0e034029621403540d220018160000788100c00d040e030051700603000c051030940184801d803500d10484600030f92410070403002280852a0740003418000f440c015a4500b1540d002401112082c1c0009990340212204540c42110000d08107000340000d9502c12155600d002c029560b03200c1c4020003a4102e0094001c80781c40c441210942a072003d0424030050900840300c4c0442c08442c4112102c2000703620128020301407034080100c41d8001d0440404451030343d03040002240c600c0c08080d141c0900d00f40c036104c0b000066130090055910802c41001c0030805198008200c99144200c14034404407d00040249903e03031210f44080390400e11700c0d40f036092101130075a42c0c144884110b02c551428594207102d011451034003100003070080d91340f02d100942d1038140711096002d0380001540414140702c403000740f190070359081d0124260301402c00c68106481c2c018203000c1643c02900c540230001a03000d844482071040340c024890100804900d0308440c84074140e655076008681285501030603502e44c0c1a42001010b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 916045944 1250 916044694 916044719
    0x1030e070b070803070329090a020c19020402070f060b040c110d082a04030c061107120f020a03060c0908060c0409092604080c1512280905010e0601030c 67
    0x285d83d0310300003411100941c012011802241c22544101900308101c038201e24100406a420a80184c4110300d00807044214994030070040038030789000010a44a60301350b54607541a0780c0d00540001c45240d1103091841c002c4018810502d029228520307190348040060b22420b601601c400c00714000302140006100140c1d120031000b40488191424201159911000760f4403024201c0c101d010380c180c0b1207003103103070030344034a003040c0c1080c020458200039020401900061100c122861054540382c0c2440500307103012408000c60b4040c0d00081c92070340000401a9a40c4048a03e509980e00c0d01446d94803100d02d80d0f02c800b01513a00030b80c0d620080c4401d101c41c02e500d80c4440d1010784681c0720001000c050403407584000e4410000c0000d16036020404102010091000482e292302c00c036006e4802181d0b1000005050040d55601c3c20311a489500244000f5204065107414001000c40c000c02e40c80c414002e007018141c904412599942880e520a02e45940022482d0680e80d01003040000386040c04420440e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 916047194 1250 916045944 916045951
    0x13021c060902090a05090402040f0609020904180b16050f0406050c0f01060303052b1a120f1b130e160902040e010303030504150e01090b07020f0616170a0b01030e070b070803 76
    0x27660310000031028220700d2080034000e100c1907501503180c1c062030082008036801e070410105400b110040070800182050001940000e8518403080c40c00c00b8000110340e1800342c00d041607034a010004000c00c24580000241044211420031900d00b000d000b174004e426122140700c0100824000d000d00c015120004019860345a040d412044815070724400c404191407810741020449501d500f50800300341000b0300661188459903008242001004941720781c1c45180c03c00060791145e0840f506001607940c41c40f1101a0b44188005210365200c9914250701c0381000d4005003905410060300042c0030314640282d40403100c03070098070002c507880c42c0c60640103800c00410448a1001342056003000011a2003031446002444000003150b011030b14107100024400b5141074250340c4000e9090580781400100107601950560484810899100d0f003910110100e50806984099090402084d04210f0780101146202640c0034060381c1c01d00b1807606e44901d990f0264000341d01c3c00b000300402080d0f00d034004540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 916048444 1250 916047194 916047199
    0x12f0c070b090f0d0f020f0d08030601080a090f060608010612110906010309080f0c1b030a02210307080d180c030303020f040f0b0903100509150613021c060902090a05090402 76
    0x4545001c03001035480006541c040700d281d40705104117030a6040144041c0d007080c00586000408040c0d6455051003404001d01c003d041001c220300040c4103901c181c00280c401d992140224080c0e00192410780c01401250007141d00d2176107442d00000b12864401240480716402c4040c040c004030b03000303080c46000c00e001440e05e8185500d9046403400100010010401002c604a5842c1c840074800c1505052812040041c070007003594440c450081d42d40843e03001034082c0d045540316014110f0303904509a0030030303969042e0001c0c000800c050051000700d6005060032040e09008010b408880c41001200c42e600700d8000c0c0c11003150910a0002130701075802401d04910f44a070365400e0580e548800b2407900100d03040f01c075141801040d00c10316828100b00d070680d43c080380c10041c8458540007500541d42c0b072240e1040c1c4802c2480070003040c210703119022403264900d4034032019135960f2040440162005401e102ca90f025034581a4005640c0025100303490704440018a090b024614000c200031040340085d10523603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 916049694 1250 916048444 916048459
    0x10050a060309050102091009090f0b090f0a090b1e160807080a18030302070318030809040c142107020a05100903180602070f05060723030c012f0c070b09 67
    0x10385071f0b41ea15000202240d060798035100c005082080c1e030b00c29038811818041c24607040003983e0029a0310300c254158001c0c8401b071040d4080e0746840981d000703482454000f41c001908481403200401e450901011a03244c804d200d80c3c019192002c800c10603440d0384040100092004020030145440351030740b80d410100003000130038400392180c4503030105001401e0807408079a0000d0301d44205131300040c40c41540d00950440ea81418555201d40c1038034461020800d2165a81d42003100895010300e00500425582c002440d40310320082444075190700c50404148180c2d031925002900551000441144480d4440007820300020700103021809804584011018030411000c140c54916003030b20900010031072a402060518600958042901b0a6030420750007141d041101d0400f041c11034400f0740c00161a03044100501203000030060030350080d0318165085500b050034082e0400b40701182c00d03040c0844d403400c0412546001d07024200c80d10810040c5021604032003410003900185101800354958080d2126 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 916050944 1250 916049694 916049707
    0x6170f06130201110f0a15050403090527010801060302030114041a040305121510030204230f0901080601050906010c241b03020c01110a200703080a0f0810050a060309050102 76
    0xe040180791944036000760700c00d00c041407d00440400d40031180c42291810045400d15890080c40000c10380102d078050000d8010360910710790003820344000f840701c1c17881c2070a40d0f507180c03030f80309002c1c14607484242c0c8a50b0800f130000c40100c3e20106800c0c0a40e6100051002402810181002500b001841034003840014048007502c1d0702c0408400788100301d05036a07101c40309483c0d01003242d12444503040304101841400180007120000300b24124007400d1007071140748100030500290342803d0560030160400740080001500c840c00040e0b06050720421141640c25990740c0c001124118103800c00074040e4500340400381c02c1610440040e21410201800110700303010110441c2c0307031150516443c040060b500181c1c808a0500038451001212040c0c02800d01d4111820b0006150102c001086101a10f0306650007004110404c0310340d0080d0b9014042c0c2e40c030742544020141c14040300351440c1c4042002c00b000075444401d80c134075107000d032a0000d040da400b0728107001e8110000c1407140011076207907500f04000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 916052194 1250 916050944 916050977
    0x5060c010507080f1603150312020616261b03070e091308040501080933090708031803160f051009050a1202010314010906170f06130201 60
    0x4004140444002060500b800d02000b0a03010300140415404107403002400b058400301c0303004045140b4103150100304030400f9040c19150f1100d5600080500390300016124109802148a61240d4400303450b1205101081c0700950f05c40c400424518000c0d00360b605071032466640c124505420480300e6104c51080c070f07102401c41e4125802039071841c0102c5d02440c01d070b088501d407101525610508904104c000003200313a540340642d009500919040c840d550b00054100c2804014201c40c1960414081999140034141404030440103a40012004048400100070703170b10001d139000480312020300451926214a10080014111450070780d89802854030340740210582040180250000c00c2d010381c0300070301e880104400d615031310742202c0612202c2401004641d8400f4994802c035001903c6089142803d480100d004261000c1d0080b1404000000414200d400e6803110095914001c1c10324104901c2003007140d0b8403490010041c64030360010b0005440c90b00c462101c8080c45106050510040494422 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 916053444 1250 916052194 916052197
    0x20a060509160b0c030405270106030212010503010b150921101407080412050712030606020d03020c0304170312040302010506100e010c060e10090f110a0b070b04020105040506 77
    0x22941d01d154454184181c1240508010400401007080064500f60200980948a0185100705803140c20000e10701e40740d14101c20503200320451807840c3c001b01980c40701c9018000b07400500c048030700c000c1214004201414148145032041c038000f422000300d40c2500341103d840b0b5010300a100e400c00a44501100b01c0e00c45c0c1003203450311501c05030103494100000b41600c0b003100c130b4100b6040c800400e440c040c8000b840c0c103c0d20054116411861440c8442d143d1b40301514107100b592030091003000c201520201041e40b50b402030741039400d29070959410100d4440c08606038000c440ca401c034190001c0004100482a010384820304142da41c09890506000301013010700800100d0741640543d441d24204a0280380079800400440c0306810491041c0c442c00000a02c5010a00c00082045031740304070440bd8041e04103c010000703955004c062000308080d02d046481201d4402040710242c03449540d880c4c1600d00300301c089040d074408250003800c05e0000c0c1c2310066204000750040e818804200f1000c2203e449100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 916054694 1250 916053444 916053451
    0x50105030a1d010213081b0d03080a0b13050402010206090d09090b0406030614010f05041407051b1b011409010507150207020a0f140102010527011418060a0203070903030f020a0605 79
    0x668a400341b03041909814010f101c00f1014504140c2000c1320301c41e030745140701c1348440350f0107140c4005240d40714030030308004144698200703501c400900d000d42e42058103500100c0c0f080c0c0c07003a800c1d2602074032920101960782c0f0800d071006000c00c68006c01070214424a6008614440740200301191041d9603884030301c129007501c02054210300c40c0d50f00500c450302c003410341d202c014141a6410807155100d0313812640039030000381c040c01c01c201c400100c0280303161448080314120385007070096a4814445d81e00d42c85400703007804c0c000c0c0d0104002021803204071050714142c41d4101c2068651600e05041d58ad12283c10084200d60916459402c4c441b010140c0ca03120501406444d4445000810750305240320001480406544541160f0628080002884110301950100210206450381c03100042c04001c0c0034000050aa06221034031504029070768408540c3c151140041000f0307034500d070315805284c00c241d101c11101e40020400700d1030300300700281c8140b920540305007051050720303503204d80c03655078909681060303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 916055944 1250 916054694 916054717
    0x615010c0609060c0908150f0402040e0d0e0f0108010311011b120504090e03030712050910110a0f09030b0601050d060819050705010e0d0f020d120201060f0f050105030a1d0102 77
    0x1003100d0614a030300640810090b003400740c014251f2040c0d0450403444840002c0624005034a0000403404648858000700080b85d42d0509403040400649002000f440c0701034101881002c0242400c00350354000e81d0b0550590380c00c10b95500c0031009900044d40c084021603405c00008803c06003403000304107000b0000e6601421669a107a84070f180940c248242c1d440900c0e0882190010014012441e41102c9004e880014503040840c0c40d6803402c0c00f1030b0515040c0c000e06c0c0030071400d0801010b0401c42000041c030314800c05440b201c0006240c01070407a0708400c1030000a10300308401d8082882c2e58059405040d04030481c18020030010b86030488a420101c00b01c000c114500ca0713160303200c000c10400344040d80c09424286800388a100c0800005610b1801200c1d01074400308210840c8429511103140d541c64103600144280702d681c0701884000c0c003d050a1042c03035014109060007040458034000c20f1002c0700e8050f5a41402d544400c0c1c4440004c141d40c03840c006078103855400c03c00382290280017509018404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 916057194 1250 916055944 916055951
    0x20f0313080606011707030921050306130902130207020f1216090c0f11030c03070c1401030504020f010e0301061806170105090d0804050705040504080a0e10020615010c060906 77
    0x1c125000b4900b000c0a0403042c180080c107124168500c040502c800d60012103031402040d545e54500b04130900201c01002801300c104c00064140d120350b000001540555015a07000743d042042c494024100c4610820096200300345035440c100440b2a60060006603000402d1240000380300800038110b00b0071840c12030b20b2604805d0031100c03c0389503904444001c028591003400f03610101100280045900c40c2400c041c4500100c140350141d00800542d0301c0040d0320001c0320355415090800e40407071810351041e0384040c540061800180c0d44203016650041d41c1c0504080e45450b00f51005658012441041035095035a8983c00640e83c0711102420941d2044500c002030f1003402c000c081c8400510000c0c2c008072580c100024008800000075030a45003400900d00303501c060700d45181050820086600140d0f0181c2000d050009010403000100301c07c00541d110030301c2c1d040001007031200740c042c2045500091b0f042007001804000e24260750400d00d65052421290010040e034600003150b50741c10040d00c800d550b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 916058444 1250 916057194 916057199
    0x801030b15030c011103070c080313141c110904060f0f090f080f04080303010915080a020112230c0904050906040506280f05100501030b03070510020f0313 68
    0x20004800c941103410103401032003581440300802c0e40c403c003000c9414108140f4002d81d42d03c40800307100b0340b0182a03206440088159503418825031300d40000d40a003401c3c0d0300900300016074807400e0741524410a4040c03c10030748005007244200481d81e004000f0b403600c41e02042c1d5803007160399078081b46100c0d038803844000801d03139403001c1b016007103456076801d1040740e5141c0301c030000110b207004a4500d4140d03440700c2070698507880303800150000c2c062684074581d04d01c008000800c0407132050300640d80e80b020b10010032080964400800d50b40d0305a1400103400b0407848030340c4809040d80c0390421201e64011081c080b501d0720202c004029030050468240401400211b50301d225450f183c02031581001c4a40001d01c1e0605068460729110350024029108185201c1100c1101d40c050b0a1080e4030b50203503020811001c0e040a06100141c401110701010811172804080307030300e600900c079900a001001e001821310504010500c0038504400541c0010361003040c0001714200f0040009201c1e40008001141d109071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 916059694 1250 916058444 916058453
    0x190305010b180d030314090a0201120c0c0f0c1505120a090b071805090118152105030f04081501270b1518010e0f0108040308070e060406080103 63
    0x100180c01409240340704104516a4050003000c1c804181400c45100c5112015840d042d0010704a80c4030041a800c048410024001c0c00842c0026005000703803034541500c004104030204440b00d8407c5240440c003070500300c03001b15030940c411032402403141e2600d00d01c00d500c0e404a0021401c001c8120b40c001500000c0c0840404401c50400750007294032141400302c0c0100f941c07001c00c80d035002014901007140350b029141c103032040c01905400900012f020904d89507160310059440d40c18405840030541e090062120384402110100001c4038980040c204c81e03d04182e000c8800408045800e8400744800e00038540c2040251005100a00c0400c00820410696811605022005911220340d40c0c06c0542d000c1c000441155000003c1c840ea503000103100d1a141e03000401c2e809180110548000300400e1130004160b4650030210100b0090729a403640440c1c2c54100808084000d15150010300b252000c10000303405060700d9500443c0504100211a0040010840d2900a03510407000504131000420900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 916060944 1250 916059694 916059701
    0x5091818121b0d050a231b060f0c0306010c0305040e09030714030f0403150f1508011a1f0c050d0c060b090f010b1c0212091c090e040c0b1903 62
    0x90280000f0300202c5044540103800790040c204d40c803051200c40702e60460b130000d00d6083c03a401e82102141c0107450341482a040340d045000b0140040482c40762401050080c3c04400d040e0b8031a10b03082e0100d80c9155605c800440b00310726144021018400705120114241007800b89152080e031110b4011500e03103400e0b060611003841b034032091610a070010080c40040f110810300310b0781901d8000c00c00707111189010b5680c900900c1c0c00010003001c9450b1200d2100070300c191084890440b60900b00a02031025900351744e0120014081101da030181b03100000750406070540f00141c295414a091403040751490752681800c00301c0c01c0c0c291400003a00c40001c407007000180e2240e00026501915405854642110303088511001809640f000a6000c128108402c40e414078040c002020150300f90f4a920612201c41c1c9080320540b4900d029000c2c0441008801280317010364180c15800359106000945080c0c451010b880b0301401c280c40550031040d000c20880d070240c009002c140c0101d0306262110850000041c103c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 916062194 1250 916060944 916060987
    0x90506090312180615010e1804171c090303110415020d03020406051204020406331b0b1510020309132d020408070b18010509181812 58
    0x443c0072003d0b8140c140da10000d40c640d480b0f401084403600c0310040000681c0c0c400e80b00d20440e90305c2000040081134514092019500030740c8142e14950420700099000d040a0180100d17200030481103090598801080d60400740802d4080d0a0004d01d500000c000c0c10071691058220b030542000071000d6640561741002602c09040303062030f0860816080c008000d00a2081d00106000c2010003401702d820740d0f54990015008001c4415060700c81050b416051410305500c0004580305041031003010a01c6004204c240a50342651000317108164090f0344065810001400c05100880d201500c52483e4480d0180307243d4046d890b400458864610400b0072040d059800c03800e501c21402e0800000d641446e030f00882ca1500500c09000d0020186209100000c3c0129032048010344130701c0d40c001804203460f40c014502c43d8071484190340d03203400c08401500d0504c038001e52a5042410f48845001821201501540050a0384042d82c0c03004c02e5284000e06c0d0844000035642070100c00031f49104007100c911500b524 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 916063444 1250 916062194 916062211
    0x60619050c0c0a050a0302040207170d0c0e03060708060d0302030f12060f0a060f11030c070e31200a030321050415150e360c060d090506090312 63
    0x10040c0c24540801c017a4500340c0b00007409542c011840004100c40e4600b8140d44202030200d054961015800c4071000d0304044c00d20b9000700d481036403445203034180800ca041c40b510031512180c0880c0c9466050250013090500c05504601081c041c0c207070703590754410041c00104039103206640346052010400202d002700721042d074483c410f0303141c0c1049150b0708640c420000000c00e040c03544926030f1611096045110b5020461000d00410b2808200035804116540c01010154028420215812518004070240c00400740348040808000400036000410055040c1050b001c004503a900b92004541801d0550300100c011415114101e0680559440a0700d00002d8444090040e0704198079a0451155810600d01705580c036402900007a0602e006d0f204001c0c824030352203420b2032400f4580007054030b06000308040800b010150498000c0b8001c2440c2c80c0040b402c1000e40780743c0140e81c0070080c1c0e5620038200320230503c2d107824070354003c1030041c0519032040c80408003030f5a40790042411f11503000e1005000c070b032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 916064694 1250 916063444 916063459
    0x10f0c201002035e05120318270108010c02030f1b0c0907022a03030a03091103010204060e03120a020618011b110714030312060619050c0c 61
    0x3169000080c000c685029090558102e81c04040c0d80940e02d1260030a9403240761040d081360b1680703040c1c00c100304440c02070031441103d805644600c108050521407425103102540240110004503c00550701c9080b03030402001c1c040e0404059141121030744490145403100343c641401000b66110a009100903460284080c51a0212001e001d1942d80114003031004041c01d1a900c3c0c0c1e030a21000c005400c00031000070b084010a1401400080d034621082c09901d80c1040500c5221031070780140412081032440081c00380d410095081412402401c243d034094a1011040f00040d00d01c2d1000e20040010300b901d96a407108540c028411301d0b240040d02d45101403410010040f240a090340440c1300f03038005035048a181c4600b012030381c600e17001d440801515030105054a14890440c0d40041412551442c260b0903500400e0780e4100340140c2151180010303170540c008100d04106203005448242c1c3c0b0a00040642e400c140d4407220510349292881d002e000407503070005400712040000c01103c2c09030902141e404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 916065944 1250 916064694 916064707
    0x31213050c0a0f1404110f04080f0706170a11040810061703030403080702031c0606110a030801053105071101020717030a090b0f0106030608120306010f0c20100203 72
    0x119442961140303240c1035800040f000c85175529500290b050031086010251201c1407460400d006500500c00c03442184142c5c100142160004101101256448e8444030112040e08140e03200c0c00d1401003c109103551f83d0b01200038144000300281c40078095580c014814441000d60500488140b5001005000c410205440c00042c0c004210303940b140e07061078180d003941c450940a920714000e148030302c003000c0042d000c100c095440f2a48400300f1240c60ba954a00000310101d07000740c441726030440140000c1d0700c07000184910f003810721039801110448a0300070406000f81800300d607031030184078080300e00356203070802d002140ba440303500c501404008400031071900c200359403030503201d00c001742105818203800300000c6c0680d451a803141202581200d50620503103020441a0103441090080001203840c0c100c01013000380d400122814680030742c144080c03035a15468019101c0441c51405102003000c0d440b951030010700c1c0105500c500c07002e20350750260300c000600e04010030240312100c42c00c1194400d200c0c1c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 916067194 1250 916065944 916065959
    0x100603050907050409150203041208060409150b0f0405010b0309250510120f0f1b140d060312080115082e05040e2503050607030e031213050c0a 63
    0x74070b007180c108490000f60312115141c000e03001c8808403c0102210300c003004000501400e109400c483d0300c40743c3e40d003842076a1103a08110841c0d03220a80504205031010068581342256449040707404001000c00181481040004007070301d200740c0280d0050321010080c80404141040f40e0603594040703c42020195022031200390503a090346c807035907100709500c2c80b088200300d020b1318140f05a4441c04805005054042c3c0d0071902401206006908583c0303030443e40303c00c54100e20480e42012849648241c0c4218030900361850130f82254070301c500542e07503030280000040c9003e03030100241181a21054070a62518075081000212014594140004082000840141d10480c000d6803020495031031682c119016101800b0303440360700a141c01c00e02d421112035184000117021091480344501e06000340b844403085035030480d050320009107541d1140300851300071806604840e40c0144000d003101c2c200580c8809054820301d003034070107a840c000510440001c1c0070080c0300032100000107403001890903292a00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 916068444 1250 916067194 916067203
    0x200d060e0405031c150303020a03140c030f0705120304051b060703080c070510060b04140a211a1023091501020304030b1e070e0d08071e05061006030509 67
    0x41004d00c2401800c422460f08450351211491200f20072585d03000544a290107542c4000540040d408640a4100c1e507981d44240700c1106c1011100070047c0d403c0c0041a0400d4166821102041f100c82c05500405d04c00044a440074501c2140902c0c000c0c03104200350109241003074032b091203c41c0201010061000442e800a54a0350494154031401c0d60b201418248141889100c2e5104561141001400100540c02a024000380d5940c1011003018620310700030400c0009962184145800c860400701c11f194444042441200b80039803c000413a40e10b0502c0360510040440c1d40d5007044c042a00288070010326480001d0003080c0e2000d014084260380c00029072902d90080410a5502201c014080b00ba48244103943c01036601c8025500b007404d001070751218400242c071140c405500e80000080042d4440d107058042550094401c4030171007200d86036200c0c1640301d140295030580b1040b090704500400d0890100d00540264060303d85420320944d9501c00707040b164000d508050030001400b200b14000306 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 916069694 1250 916068444 916068457
    0xa1e180213060e1303230915091903111005120405070303080906090a02061308030309030c0c06032811031e100602060606070303150306020a030606030207081c200d060e040503 77
    0x100406c03440b081c20101002e1141501143d00900da00c05001d00c40b20045006e00a13040d4110f42c80c519000341c600c080c000d88101444040c2540ca18041d00300c00500707081d09068000340b1580380581c540509980746000301d4800b56002c40389a40450805c00a142c1d0000c07032190400b8a00024091b40e05003807403850355400c1482d1020f40308601c002a00200e0240da421451f00600405d025030741c8a20b402c1c1d046c10b448e0340108440107014016001c1e001c60341c1c40c1c0a022644200d0301100c0e002ca9240022609000b080d4502110f0b00b80070b542d40c9103840c0b080c62440041c41c460540b644c0300d11074003100d07641c40039aa00000307044210f084c07102540034070800e500801d6a070ba1201c410740d5030740d4540100f800c0403400342484640d111203607040d164010080c0f10380c80d0001e100011050300e0911030207940b503c0c101c04038414100b0280c240d03481400302c01212075240044807850f07200d460020500d440700f00380c031a102c080d00e80401100f020300001d072161902460b000343c0006202420010846207055107901ba102d125a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 916070944 1250 916069694 916069727
    0x9060403030c1b06051008030703120902031501030b04020406080f0307020105071b0b0a090b033105060c04030203010f0626010603050d170a1e180213060e1303 70
    0x5040c684015480740261070101d80800f0360714001c0c1d10407410090b00504040e502126219640d243c08911070400100300c422441e410390391b6450460180258000500000004070781c1402014180390041541412250283d0f001d83e0384e440341070605104000865980d40d124840b6604010405100c0729030200980340b0f0140c0a003012903072041c040c600740c0c121203209401a02e070b0940c0c4c00401708100311190040d040300340c00c64945545054030344100000e03a0100b1039150301104010510a448070913001c2c003101031000d14180b640c010481666407071f8101901100d400101d550040780802c1949003d000c0c00d000842030000401000d07007054103480c02101840c200d6170030640c16081091000500354400c000a54109007a00c4a511403031a00500700c41100c2d41e449243d1801001051f000e00507881884504140040e2204000c489a813681010b00307405622440702205203030b5868056103440061190b5504050300000d485030900c2000407032040050103014984580c0c5043d100002d810407e004121140c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 916072194 1250 916070944 916070951
    0x806060402090d0b01080303090f03030f0705071505010b03090d050301080c0402070f0f0807020f0117010315061e06090803070c09152315130e0601050405151306080906040303 77
    0x85401096640840e082c0060400380013500000c1c4000000c00694048c83d064425121000c084202607949d074041500c4028410f548440840c4440d0701460061000d5071241e80700511701c440f154403040c11500242e10a40b0800f100004100e0316000c144042c03425541136007041c0c1d00b50b505050240350f0f00d1088140c0c00340103a80c001100d5043c4081080340a035407545c0900e40c00412841480e000c041c1d90400e05049000700c0c0402200c411075070050703440d9500002041a60b000c00c1e0f1035515066a85101d1407190403644e81e07149000310305031621350344848094004680c3d82c5e0b00e0703900e082c5008109451036031040000e60020700043e0005240c08040c0c0081701d00b8660045403041444101c00b80081080d8083e12002c0d102d81c007001680862008046110072044039405240741c000a855003503882548038064a2441c09001440703141a800501500690180b401504181c0c540e03000c03c038045840e000021050002084482c03001c0080009e88014224a01c2e01c0612400c00a1956030f68000203000282850388 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 916073444 1250 916072194 916072207
    0x20301090516093b0a050a030e040605010f120216080c070803090a1710061e0e060d0807050c061201150302070804060c02010c08370e01110a021e030c01090806060402 73
    0x8551300850242c403203d8040e00c021122070710f00a940c69060a17030071804101d0019210441d0704d000d214200c100c41040e107807046a5000840c00301d0b0707100c0107140710800260707007480315002c0340c0a50b858680100303200707889555648402402441c40c080342907012101d590b1003040100510f8603200005012224018000e081148000050078140b140b10000091070a240001c001105a90f006501c100c0c03543c03042070100510344445100e1503032003044800c280c0005075110603200261149005000c0680510309548000850f035000513030300d078420713644143c61046640051003800c040006090040f001801c0452400c1015a100202805984039180900884140d034206590003104401481a44011220742d20000c1c0300d0748404054026250a12450b40030000040c458446881000c0305d00003621001d0100c540074004503550000c00c0e420200e180105400e840c0141c445660765440140c401c401d424a2020050505151811011072181040794040040002c00008203a083e0000010740c2c015a9610 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 916074694 1250 916073444 916073531
    0x303011202060c0f030307030b040c080601090b0708040302030a030e1002010b0109051318060615230f0421020f0f0a060e060705030408070815013002030109051609 72
    0x1c5580d003844c859001c00410000310a9040e88203040f581c104590411040315002000c88540204076480b50200382810828028403003500c003d0300d020303482070201510b4540c0302c1d4042400c001d84844110085850701208102c5854200510500042d040c07000308503030240100000d0a03415284949401010170100764011126281c002040c0501c0203000707004d500c02d607881d000703004051510500ba43e0042040003941c032130340720380d41050450b0300540d03078003040d51100c054500042d441942c8071343c28034904100c00250300d6460709000c11680500000710502c0c2015005101c00c80383e07503500d41841005086162440d5941d2800780d00301303641142c500501580445808075076248901f560107802484045400661400009102c4096604a10689a142d8028080740c40712860038002d2081c200c1c58a14003030321484080c0503006080d503a44030000305010050b0082030850b00e41c00401d40f210703004101c04070164034580419400402081c0070070002603040c03000348029041818030503030910f00c04e2603004200e907 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 916075944 1250 916074694 916074703
    0xf0c1b05060c210f07030c09080c19080d08010f0905010506030f040c0f1e05010305010b1206040603060921020606010219020a090212010603050a06030308011401090b2a0303011202060c 81
    0x1c680503180002c1810030050a200c07014044840000281c10000b1203500c080c80b0301d40f2802100d21078000ac010064006040180b075409588601803032041d01c40300082c802e401005035201141447d00c4070036055061841c5a000c059107a044030075402c0c280001045036803580c6040300e074040c400c1038200c08103803140d04c0c040003c48001d5020400989600c0740101c1c90100c148045150540c4013008418207958900065017582c0d0248206002c1e16010300c08a018040c000000c55441031b0002c20004c1d0694480d03441d841291124581a9a21107030883e0410040a01954107514020107000804040c9460030000390745003030820000281d600500049070442d15240072810240458803020740d00d0700074083d4999101c50713091180f03000007420600070420000b1300e4403840c4141c982540d00e4251681c284424905902004c1c1c9010703042203034a1030005840b07080000a805034120400e07480038500441181550984040b504413001c2d50002c100410904a551468800840e41501c8950320358030040415400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 916077194 1250 916075944 916075987
    0x1208090f070602010e070509040f08071a071e030b0f040e03070209090114010b1306050a0c0c032001091410020f0106081c08090c01080903070203010f0c1b05060c 71
    0x3544103503900491030741c0d019004a88295401c10403034246540c1d400400688150a81e0050100001d1049080124040781d005040796801741c1112649210700d00000c0a0704c1404503180e000140501032810306452824595134a0208180b40900c2035003a014001254000d005900ca482142d6810b2160060341c000e0090b6500b298004100501343d2800c1c60340d03240a841c5100040518040e414004500c1a0300b071410350b00d541c3c87c02080f882e0350904040081c2c13201d600003540c2000b03000040d04002c0004102c10f010402952152128001a0841c0342400c4c84415600400354103008400c0d600340311a81c0c000d140310640781c0d8100c0b01010080c10101c01a414241203c04501c0c0035400d10700c0104041800203804c2ca00880000c20080e40d09000d014212001401035a84008680019081c885950311804450b43c00226071410f40c2c0c82c155066001a007110b012044070180692076019210301c444d0080c218403407100c1304200850f00e2481544e151501e5400c014800c500040d404a15540302c003213400d000406 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 916078444 1250 916077194 916077223
    0x9020310150903050111070b07050313030c03090b0705070f0504020a1e0c0c08210702060d050603032709061009090504060b1003020d05070e100806121501061103030103120809 77
    0xc2c4039a030341403420a0382c7c040c0d501600d001e1405001b2580c20f500c1501201d10504108640141e10b20f13243d034040f10006e849090503001c0000d001350218526403c04002d0060a02c511300900c00d040c0742c0144201144000e0340010710a601c140012240c661f00b1100242c40f0240d1f003200c0805401d1950803c1d5100d9184036005042c2d55241e00002c9202d41d00059a9081c07106201c1d0200c8101c0c4081c8241401c5d803040c100000d4100750144038898460055801c2242c1000300202a241801c4808081c0b45c80403400280079081c0340011004202035080c4061140d42140b401d0b01d023080d0260b0302c1040a40301d41e0052043c1c8000030307034032400941400202ea0014024100040c5034807502d0044130801030103034229618110b9518900004a24072500560840105400182c07118040d000450010344450400800d415046000ca503010210048240f0001c1301311111030300741c88103650501c50000c6c10583d0003c0c074489190310800c01800420008509140030005515002c081903a4a01905041c42041d903042c45 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 916079694 1250 916078444 916078451
    0x901080d110f0f0d080c04031a06030a060e0307020108090d171008070e012111010c0f0606030c0e0903040b0d050405031b011d0604020d062a02031201090203101509030501 75
    0x4102c3c0429421418074a50355190001c0e01c0348400d03000584218400109032a400c111080301d49960002c110307501c030304010709480d502075060f21140195500c1004041e040e4000042150441d82c01810f001c1d0041025002003a0440d10100302504400d00b00c3c0c6541d81e006107140003c3ca203007104a010401410600c0c2c08e60b1107003540e1b0050344445040078050080d188511a810114406424001c8644ca60b000f03018038411070051001510315032600003040d61a03900d21017582e03000c901140280c00c000e40c0710341e404560442c80c045c401c000000c0f02401410741900200410005120110103440d04a0700440e030004003a00e9a242a40c614413821168022121030340b42805400e800662091142d19000d84c0c880449e03c0602c1c017103648a80040368020350200100d40d0701c0004c03a580d6406060003807a4910100903011818090304e45100c07002400e400140c0c00080d82524040d0b40950050040102060943c21030405843c0795840352418021503080d44c14543c02a0300c098407624682004640110003003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 916080944 1250 916079694 916079713
    0x81b0406030207110d030c14010b12030405091b03071d121c0c0201090306111b0105060f010306030b1b0d0c08240105180303040f080a0606050901080d110f 68
    0x81c019401c540010f541c1c0c2c09210405450300d0030301c1030741e0f030110551642e1101e02e0480156a8048401040c40e5243c91941d1380364503110141d100c20b400e10b0b41b96017801c0c000f1612507103050f0820070034441c0100310440011420203025102419141a240c118002d400c0280840042888001c907001c41e00c1d01460740704c5c00310000c40c00620000304607141414155008580c00040d01a000d49170020705440090010384006401c001103905540243c41075046003039164540316480b60042c0200c0409150500c142c0d5507802480b003e481d05d00100c0030070460030b0070103100c2645140c640101c1400c0040c50300780340312204098881035a24003021280d503a103003180100425290500b000f41a141e00b180c107080780480710702e06030201c45042c190b00049114140d581a240040c07803002c00c490310030009a00341d054442403101140f03036006040c1d0703c1b002c1c18802e4000c0002944c5400c012003504c61560015008000304001402151808581d400e0300c09e6050910024100c02e0ba00311529010001b003078200304d4000d060b0b40c13 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 916082194 1250 916080944 916080947
    0x2040902061b011506090e09210c0c0a03380112020108010914130507080a060b090a05150409110d0b01032d0f111e0a24081b0406 57
    0x1000c1d0362200342c2008002151480820844d6160507014000c0401c0444400b00104180c0d01e074025070000c60002a00c1741a42403207540603085800d000a00080c10000c03e003440060400c1000301d5403203c048842c200c100d0b20703640300c2c0000d51040d0343c00307050036042e08014210944402514240b0209003200c0103112980d40d000320001c03005000c1012400580c1c10000000c2185142c041c4426500074010701e0807150300d0ba500e00052004261b04200d4090184072400140c0b860188010300021313004a2000c5617014200381007040141c0001c06205000e480c01c002c0c800ea03a410b14050220381c2a0550380010950058248030b24401901042150300c41c4e42c100c0200f0800c02000e103601d04a9210b1808481c0c4031580a4403451100b008036240000884040340000c0803603a160354400780640956242d00106c41800c000c61b400c444054400d1400e081c59402c4840780d4105011000014001c400980942c44590291284000074200d544030030007c6103004552962000c0c0496a0010345c0295559680d590702c400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 916083444 1250 916082194 916082227
    0x30f050a0c170d060b03060a090c0210060609170f0a0b0a060b07150c08071e0507120306030201230306270403120b0f0607021011121b03041a070204090206 68
    0x24883c903120f040020004645410405481c0a40801411017000b203081c14040b000404040181004511034004c0b81c0154091611071180544842d03a21140c1850500c140160200c02d000d059512075070284144450f20034000c1080d42072180c1c4010340c1282600c940407007038007519072a0445800c5420005204080116160b0f8094000104060501002d01482001d64a00c0300c21515000400c001c02c02d00300c45008108800d0401700c0a606200e428195a500d4020151392001d9112000c40c0d5290303c01d000399070300121880e8203103007411f80038941c1080ec2e0324040d00301c1c00302820a5028010f010360b0052508000324070f03558035500165041c41d2500e4103050007416a083d8600c01d00d41c5620b021955500f5003080160080380c0340000d0007103460a082a07081c4034501420403400010054401a0703d40400c02c04e0203030380110503051010f161200801504040d156100c1019800c00760b204010030090b1900c19a12034012035000444680c803280b1038004100900030001f03000b0750025001690300b090384110712 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 916084694 1250 916083444 916083457
    0xf0a0306080d2a03031404140609070b04092705071e0e070509010c0209011814010f031719200c01140c01090b09010204060813030f050a0c17 62
    0x7000c54004004004099a4400000700d0300355030450400074003030341405091030b0b510301213109180005810031012a03041c40c2440c01e80702100d0074214800c480f9681c403001c224050700208180c029207107241c81d04a05181a11030351080c02c07a0a5201c000011050105500e060210000d000001c9026429454019240c00079405410b552880c03100d0314400000c80321411805030313221204c032641d40d03031a120419070342600000301e0103041200c49500c1c040141c807180c031954028040350080924030f0305102003203c192100800c00203402c4c041d4100400814440c2000310342225040100090130340404605a0340324803402d000031448400704908912407603801948080c25610804100c1c2042c041003140310703114920307030100d140018a010300c0d40502074074081c01015a80c2848000251191207079407028051042100d85031581e035408a020000303a50007030750350780d8451804108005500310541c2d020300358068001318901000343c0414a00380450084035454603040d000428110400c1d2105c8040c400c0d5071051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 916085944 1250 916084694 916084709
    0x30e0d0e031906140109140402220e030a110109051e0f1c09080303041208131401090219120b070905060d0b03010e0102070803041b1a121012030806060f0a0306 70
    0x800009401d84584070f031944000c0340410200c010786668003041412215024021f040c40d0410ac01504d01c2c1e4514401c000f00c510025000c0c0da00c8010090340038080000700a803400440c2d050204800002d9004120b10040c1c40d5001d501d0031000e0040408680342449030b082c1044140303c1e0b159140380080d409044000403031601d640300b00d140c4d40c9441400ea00d07404152001000c205205507130705c2c0450b00070868035605c90642c0c072076a1308000c420745a04000110400398000b0b26551080c0090550401c5025802e400200c90b030450000e9107080040442048440f8014258249002c04103a00c507100d0150304004000c0180391030348410900722080010081481e8041c404c0d880c080100050504c180280c0d070146400500c070f60705543d20b030384415a0200221300002041c00410b400440d240c600106488003401500c14025100d1810805502000c08050407150314000c1e001c0382000b004a600158020190f0700d8613240c0125200d44021429a000300514501c3c0420041030b42080c1ca90b041e84540700b05d1b40403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 916087194 1250 916085944 916085981
    0xf0708040f080d110d0e0402131d0606030402060301090203060604030f0821091f0e0102040314010b03010207020f0f040b060d090501060e090705010c050c0603180d030e0d0e031906 79
    0x41d0300e0213031100c0c244480a880c4603005261013525107401001c01d81d009540162000d1310b080216221003242c17000c16040107000f5507801840034210608080c189610a0094940c035145081c40d400040d01c9002c144940070071150000f00241603916260180d41c01168010300d0041c0c1c80d201460401c0c455001541d10303e400310b41c00f043c04219400c1110400d4040c100c00c0e00503003101c12080300c0d2a6403403000f0701000c01c1e1040e25001c045140308800d10080c00118018028005511400c6501600b52002217038964401ea0050100d01c2c056940c20340051003190007191004401c07a10000400c01902c000c0104a502481c0803520980f01e0300b80e504014040b40c03007a0f000b0008992a444c00c00241401501c1c0d00c440342e0302081e014003e6500805d44052210302440485000040c800006002544115640754482d4104445002481d03810401c0d5014200baa042c14401c070a070320005030341c3d5840850300000c104004416484d4240d203007440a81004107130100b03004280005400c2c0360000d008264402c03002100d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 916088444 1250 916087194 916087213
    0x403050910031b020c0a1401030e1b011b020907030b0d1a1e011203110f03130306110307080c130e040b0402011e0203030c2512081b0409020f0708040f08 67
    0x4042442c8003410f0300200504415407c00c0e55030035800444001d41c13818180e940d0504022040100040c568960081c2090112050400d0004020b900d20380c20001001e644030b0400f00042e907a07151b506601940f9481c00290107108800050102d86420001824240d00d5403d00500c10013000076882c41103009569045400c07084585500051200b44103414414500b40c0d4504002440781c0c00041060150004841804e0819054030b402c50b03000714400164015103c0b0704108100050040980c042541d0031101d05501e03041c2006410710b4001410402003d8001441d40c244885444000c4044c0580040d4641949820320b8110200740301035030180d01041c41490341d07822050640c2001c2d03501c1a6984d01450558480049492580e0001c4049100246541e2021000541600340003004030307003d8501c4440403e821400a813140002518956054030044104180c404210302280c0480f00c1801d001603560401103912906801031260051190074005400220401859101003d444100060311034180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 916089694 1250 916088444 916088447
    0xb06030d0503190b030609150a0204051f0203130603051f030f060522050102071209080d08040c031e03080105040b10080702070b0a030f0e1b090403050910031b 70
    0x420103040d0800180c1c1080041c124080045100075000c00c07201012a500e609600080e04004040320030200c1e60380108004c00c4040c0d0744c401100d80103005514114941400c185c00314074214120049900045012002c1014240c820011070f500a5428420300380c1560b159003000740505010346201c48020b25801c1c03595a01507515001c0c0302129440700c44000c0070742441d81c404028001c0100110f081000f1801a4841807000d1144c03108034900c00c000042e0784540f03600d05601500c08000c00303807040012003641404500000250380789101c3c3d880c04c01c20344903503c0b0719010f034500c0c0a54000800a5640303144012400040e100491b400501c01d841d200345076a02e6006003c02c031800011100d40c490154540302e14444d02801c0d205410158920558a00640302d41c1044080d034002581200000c1e45c4400307040f1450164400e10b03065812142c0a4021002c2e15141c18094003207980b5000c0c1700322002c0001c02c08140c0100c00319900c1d29000f8003010070351350160902600600c1c0d111541c00b40401c09a1800351101d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 916090944 1250 916089694 916089703
    0x70e0a0b010e10051218010f05180d020303010605070507050301020a02030c0d1701150c0f08040f12050a08160c09020703030c170c0901030207050f0a0c0609030803010501050d270b0603 81
    0x103c56030b43d0641009020f001040c0c000e60041c0070120000400d41c0d00c290407403420300a100080c51200c05c045140e0038512000460202024640d04e815000b14100481c1c495002c41241e046601d2403910984072011420b200c0d081c03004030751180d07034550320001c0e07101c800035004809485c002e2a001c0644260850710303030080d10103010b00321800180c0c40c100e00040c8011410000c0041c580205442c00540c1880340b50f45480c1000340d01c0700242d5a440010808003e0948000264005450300984e4104030740040d9070740315903483d02c02c0402415040085a451000802c24080200710340e003003921900c0f9a955a0741040081d030002c00143d0010342000d0f200104c503405500860600a80c200c613021a0f40d0700c00744003a02a40000203d241019001c00040c004100100aa0700c2280071030f001501d01c00e2400d02d0002601c1e40141d01c21300510048040420100700e1344019241141c4083c2005969411150b04e04c0008104460a9006046007000e621100124110034201c0c840c0c89030b03d0454168940e80b00305543c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 916092194 1250 916090944 916090969
    0xa05150c0c0304030206160204050f0405070b0903031801030e030a120b010e1008191103010807050d0b0106031104030f0503090108071b0f020a050d050d17040b04020111070e0a0b010e 80
    0x20b030b0b10402007000181051b02c01000c080a080168220a200c82e42c0068282d03101903030b04686211b080b405210900c64103108000089c505620403503d00005032000ca92603000303a241c0c4001500ba42040041d003640650448101d80240700162607944404103800b4190041070411199403070300e0520201d29030350050348502c2032a17100508880c0015001c0200301d4240d2002440f00c20849040055007118503050f0107070102001000307a015440390704040204c0d10303000c0030758815885003130306412040104101c0451541920050700d030114403810765030f40c2c1d40041e110317a500007082c40094002510a1000c04005804080001d07640c022468442c1201120704013a404503400c3c10110f80c1e1861800100f500290b40c00740c81c40a0499281da40c2d4031000030340000c14003c8241d400750040103141c04000d50018000c180a98020814007240c10240c131556000400200001e0500c040b42555641590007041804010b09075000081c8052030180030030310142440c0304d007040c00309180a1103600b45242140c100b914 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 916093444 1250 916092194 916092217
    0x50c04061404051933061707170f041101020604021e0f190305060123011d10110706050c030f161403120f060a0915080a05150c 56
    0x80100d02400c0100910000d04040d501034200107569920300a1409031104040e6a0100000c0c825001e440000320686480c0701805d18025070f8100b80000c9422100320350b14076591403244400c60b0745841041d00c2c02e60382d0740e03d0030318218809010005600c0c28032414500c1213110b401c80002c03414071040107980d030301c2c82074900942c017100700c0384410142104c8190721209880c00529a03105942803401080c0d09510618540400c90513520007482800401c000c040d0041641e0b0715641c0c11400d10000c0d44d00d01c04c284c05036481c1000210111500c2110a48000c00140c502c020b0440061500103540503000c2c0141c0d8205074100d02030034000040082c06a402e6030400002070340614074201d4a2006a4141ea111100865035446003640c1440800c8080f652000710341005030040d40d8030187d6540340000c20000501c0032a018500e42c08000054490880680403101100c00c0030481e265015800d140f04081d43d0418480d074442e880c8a501401800074442d403400c0800e084036426074031405100c8034a03204d00095041c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 916094694 1250 916093444 916093469
    0x20f120607111f020a090506070f020f040f0f0525023408010501091104062337080403080c0c0a0b011211101713021c050c0406 56
    0x120814042c00015409541c1c002c25252000900429084010001503003803501a82c00310f04d549045d50400f11003800340c0411a189810700780c2556446441500000d002401084050703030f80d201e1034680d50440e50030310440c210b00b842104025403c1200405040b1051140c0500088041c403140c541001d03884500b004550207030030f0400c456003500702c0d01e40503220540e01000516545a94410f0000f0840001e05a030b44004140395240241e09002c0d20b440c2c89140303c5e0058108030811005400484401161485414441c0500c915000100c00340c00365043e4074940300b07200302c0c0800c4565040320407000c800110380d2640c12000100803085951443c1141d00030040f90310360002c01c01e1a0200c00190510080c1c900441d00030000c1c81c1d880d4078200f042030f800800400da10b01d04d50b40800040c01c1a02c050f146068403402200382e1403200050501404005a01e580c0d0309140c040f0358188220002c00403210b40142240a03c1c014290090780c118000c0750090311503005401d10141d01c0e00d40b50181104403600c001c040da = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 916095944 1250 916094694 916094701
    0x5010903110a080607020d02010606020606010801060810030501020d06090f090218040813030b09060610080a020711040903080601110a03120c18060905180c0a0c03021f050103020f1206 81
    0x75040350303801000150b84080d0120000034248000c01c003007449249241c0c041c101e5030305940d030064251801d641142096400240401c44140da019103080d04480c07880c030700b101c2280c903501050140f855050700041c1195000040e880c820604607000007040385e031a80c20802001d0310280b0100f003110076005000354042c0081a210395401c00e000c61480e04070b4021040f880c44d000c01d0000040350541e4a0b4800c880749141c44040000b0010140070080e4800d200360303074003000c122200c54014000c010042a41680700e80c003190210a000c03d1030060f00b400305000d00100f001003400e050203018510102d03845d41c005011038580070000000480c549240c80d60503100c98184554116190b80a804002001030400503100e8a40c5220100d4072424001405141c407509816030800d0f05000402a010b001848040031050a10445103c407400b1201004036519129250485516049041140661642946851904410441c405940c4c440c1e0b0407240300f140d1042240340380f2006e00c0b520b0282e022a01c2010b81280000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 916097194 1250 916095944 916095953
    0x405011b0c05100903090b03040c170c0906281706090d0e0405191b11070303020a1401060e010806151203070b1b0c010e010f0519090813060203120106080105010903 72
    0x4a111035100f41014130f1411f0f2105480304d0513400468007030f41d256505820400ca6824101d800c41510450302c006415216088c0d0040b071881c500203404e107401000000c00c92051200c0d050780540c0c4954052240340109a901d80c3c0c40c070708161050807540303100c1c012200400c40407540007486030b1122001c3d4076a015050003010400c0300600700108541c2000301c7c100d001d86420b03500c610600c010180500c0180800d6044d001d0001c0000d2a101320100c659030110b20107002281e00082c3c10143c0d140d2100c031078501c00480c0e96009002d8000342d4005500000020004101e10001080c3e092040e01110002210070203034038204034198000b0503c4403e207400400c488004240c1d0a02e0f080d0384544448040d01c1c0b83c0c0e83d00d01070720001d0f5004401460b510b035980c0c0e10703200c03103030000b8040c11007110701803041030006051000c402182c1154001c000c00115650b010490208208503050f15034000e0030789400821955600806912640410100c003510350510700041200c60007104458140c90040e50703010305503421640c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 916098444 1250 916097194 916097201
    0x501020f250306110703080a0e0307110402090d0c14010f0f050a0201060e0108030a0e090103020108060d1a1e1f06030b040b04020d1e0b0609010e0d05060405011b0c0510 74
    0xc050841101c00348007101241e424000d040d40101d901d01d18076034408103401c0050030705a010b818035902c142041c44c440d0007810000107884206400506074101c0045030b8000400030b00c18181d50380d80060f03582c2e59000500c082c0c910207408541000d4a407a8241640000441e445d1041d2100c4401062103060340c0d04e0003502c81c4001d041444194000003542d01e484500010036100260301404881d800083ca41c2000c9034000d011504100703094400058a5046500191685a00038400e03070080307003a040c02500340481c03d01c40700f5186141031102000c80c1410084806d0300c40310044400800103441020554481d52042940c604294100101031014100f08084000e000c10340211607100d919000441113580c0c0d1403008000d00245148005003443d6030381040d40040c3c0c04005005001454495245103580f00d90044588030502480c210440203003d800040f07210a039902c01034254411142044200801503222142079030400a001c010780c0c0340507108035100b61007070380010107035046152401da50690320340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 916099694 1250 916098444 916098493
    0x3180b06010e090903041a040b12071b031d0316051002011e0c030e030406020a060f02043c050109090207030219060b1302160f060b0d06150501020f 65
    0x34222080c501d881000440801d8213450200c81c035000000d00300820703200c052a91251007000040c0c1d03400c00d49807601803091030191100801d0780095950000e08042d2099000401c00e21503c2c4e4048806407a07802d000b0b0103018110304000010328409070240003813a000505031100c010804608810a042c4030030b100030348001400c404155903c43c3c054481d100039a2119030040c6d0f0038000006a1401012401001d48540458500d46600b01700002e02c80258003213203034000740740c00000200c0c9007101055244000e118652008918a402d031003542c41d440c0384205a40c00b40060b410001c0020700720b90301800c0c00e8180610803c0c3c04102c0501c8100410340700f80d005090782c00c3c040d0040d902c6a05694442c91031105002504503410b9949640c80c108034540744404003424070942c00c0031030800000d85c0008140c1441ca52010f0300900038864080100b001c9504840f0542401405c00c00d01d062a5203060340280c41448600b00740313609034504c0814254400079500c1d078819045001094142c1c009401140d08a5904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 916100944 1250 916099694 916099697
    0x1202010b06040806090d09080613110904030203070c09020414120a0f14010510230d1b031103060c16030207050a0b04030b061e151b030304050d03180b0601 68
    0xa0010203000c1d991440900002e00003400a8015844c00c0511142007a07810880c410034011248000d0007408000218a5403006a040100c001c4900780c1c10b0001c0160240408107920480d0b02d000c2104050717001c0041c100d4548201e0345135900c19100c684207010b82c0103501481000940040d002c1515140241400d103001040000350348110351551244181710030800019030b80200c41c0d03900e440105109118295010030f903402181d480c05e0400b1a41d44907091410094044640581409000382d951140541d042d02c1d0b0021075000b49048400c610448071440780b20966a000c4281c280c0702090a02240c02e40c030034080c000000e4a0700d40c0c0d0000821048000b4541a4118400c0f8000860350f504c40c01104009019010b0790b05032074605d03600d801c0080c0700d802021280100c10300a450203048122107030165074104200d03000b2017048518219400301e0b00499040f00c88d1401d0240f0016400b00022004500540c0100141c6070aa44181003e509550142e440d00040d120440f08282c0401c800035081a0000c005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 916102194 1250 916100944 916100951
    0x813120c0f1704031b060f0825030506010e040510050402070c0b2101090e060103170f0415020606090f040f0312020309011506110a08250506060405010603020412120201 74
    0x19110181c0360300b00320211158541c40040c0034001c0c02150015039040e01018a4141c000d03504001c0d00410050840040ca014401150b01083c60245901004501b100c0a9610740324500c042c408004d01800c810346c1d40a0204515440c2c5503114201402400e01c2005241038260740c0c945071400340402544208000d84449040400110f81c55018400400301e0061b0003102030740f21010030180a400000603403000542519040407180340c00c401103071050440c0d8000c62100040c1c4a02c1c00d52040500c81c211001c1050800000c02003401101e1045140301c3d95080e50849905a5442c0180b00310248151500d1004001d03c41c0000c0002d143c3e4001c03d200c3c14801d2510303900c141c2840003184141e800c1139440c40c015944135520920394489082101c8000c1c80246400140c400000741001d072664009040580761103000540e0f03e00c000769207031003a01d048609058180f0506218140b5640b0342c082510b4540c8580d0404000040c2c0500c28001c1c2e030f065624940b200c41d1200000e0b13030351441c81070101403000155500e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 916103444 1250 916102194 916102223
    0x3171609300215130e010f050f0909190c1503020a021f0207120e0411030714030603070b030c030702070b030c0d0e0106090204090207020901080303040b01030b2503020a0813120c 78
    0x5011000d0484050641010300000b8100100e85e450b40300305130048040c403010b6110800417030752480800c06841c442610039203a030780c668403142400c001c40e4202c000e4050340820018410000706440040441c1e070715040584503402d4201c0304400364424000c1c0480140d0204008540c20181e0b10b04904241e920b0510041c604400d65680c240c1100354a103240010445995a0fa00c150030140141e02043c20004c82d401c2c80d503d09110040e00e00503000c0c8880a820130048000391458404022000c043c2030080b00044e16071514407104070256208076403200050166101c000707003400112056034007880e40400117070301b0200b101c40702800a00b102da220358220b649400c40020150382c1ca1006001a00b01e01c840540e4860300d50040c4030701284180d10007003c80d8010010440424640c0101078152944644903155136121911600406203509290494000c0d80c2c079407a4a41c59007550043c00705200589800306030b5074a4001d04440c04150700c0d405001c22000001c0350030b00034452408c0b0030000f44a50a183c42898 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 916104694 1250 916103444 916103479
    0x2010c0314070606150f0201060614130807120203070e1023130c0f0207181d1c140a1706010306030804030803150625031716093002 58
    0x151a03a220341c8103081c05c144502000c81e07106442510050300c900007030003040d28001d40103080305060018920a1180400c0118442000c1608200103140d04000c81d001a901d03407a0a810340c3c071b1190000c0740b01e0301c0b0f451000610300c4005203003a07215045030305014481500c1c2c0655103418148040c01520056092a0103000c0b0f07989104511700d844c0e14010f000501003010314800b90400d4100d410080c00e5504c80082003248803084800d408078a80e0048003c0703061100310980159041e0344e00160034441c01040360301c0700300d45c0c02c2422446240009a0341c2c44188410302038450310f01c0c4038019900c400500383c078008909883e42008490703080300040c900022116a60340340c000c03c1d0342194200700d80d0000c00005120795169203021456400004595251038443d1200b5140c407068210800f211404645452003424580560300307107e0031300580448c5501e2850b18100c0710f02060000400c0c2e2000c0342003194007003119198024080444000142c802508090012558031440250101280e01c40488200c156801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 916105944 1250 916104694 916104701
    0xf10090f0506090a021e221512050d0302040305032205130f0507080601022a060301030b07270e0c070804031b0909020906040510030203010c0c150902010c03140706 72
    0x110142d41c06400894164410011812001c2c4c081103003040705d0050440c45a5920008200caa4145d0587c00c514441d41444000c05001d0210014481500e48140002c59500da070b0402030b0520311590070382d40e464043c0c5100350201d0085001c0600184c2c002e11404800046d100130003a0b244e18400210740040355508001540d981a00b0608169551110400c00d0842c02ca40545034000302d0381c0c2400c01c1c180c900140000d6403150b103d00004140c615404d24424011030303a0521659800c0081c007a695070f581c6901700202e011009652410001d084500080a84020007904058040100d1308103503069142909510000d1405003060403940700030004100000c1c0420002d00c011403155070418684034680100c42444074050784040f400c075003031100035001a40c1d600c08a56000000f241e0009140d111141d1443c02800550002034040d07203400c000407502c0307402c0ba4003101e00a100d019128540d00c241210070040e26405c801c0280420011003965000900502c4031071034122809a0541c1070086948501041c2c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 916107194 1250 916105944 916105951
    0x70f05070914250c060b040c050703020f0729090301020a0306081c05030c0a1107030303050a060b070503070f15090606030c0603150b03070905220e0f10090f0506 71
    0x505a4580b1016070200c01441100d030f004503400741508180911400d0000020714982d000000c110291003101d00b00314041d17000010010300640100009104c5010180142d4082203007500988200340309c80c00e21141c000b03502c2007540c0010b4441d1302440007032030000110f07a800e0407030304150200c244201c0350503440c24406004844116a004111540313403050b01c505000c1140008000d50b02c0404042e0b9015130840308a80d0849a0800017540d10202004101d4011000103401001d50041c0030700007040c0341c1c0c141c219600443d100d04003000101c1d502c0101180394440c1c20390042664200780321040209050b00a81d4985501413103031058070315084001c10003128000340381150310903580d03c024030a005100c0d03c4034018285900303080000040d0012000c0d681f81181c8144802e01e100000003480d5103108054120084c6000360140e10092404440034015180b00010350520516101c5290b00700d480000756411003a140c41302821172641d5840068019204032282a42c00e03001060301040003c808000f00c510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 916108444 1250 916107194 916107209
    0x12060b120105100908030f031e07090e0a06080a020f1c080c07050d02010c0210120608060a0e07050112020a09030f03081605030915040c09110a03060608040b010506070f0507 76
    0x2558144000c1100409500200c20100f003044d000c1030024178000000c40351400c0310300c1c00c0aa1242d031112070994501b07848500c1c0743d10024482041c4401190800c2d0610705880092500c90301c2a540c03030720094200d4945205010003580301003072442c054241000e0340c00700c520b40a0001c8480700345645445149000d0381d001107030782c0f420000c2c044016003c1841a075019020446040d0700340319090300020603415265401920950900100c6c9400074000e1080d80359040208806010490380d680c5140d49550048648106031410040c4002504202281803019500705854161242611007164802500302503082024040d410740040007050454a8001c2a00e01c640d079180c140c4d103800200410344510960b082014440c0510501c192004085405035001c2d42c40b60040115035140d06040c060841c55a10203662145000303016a4100b01800c000c210080391b0343c50501c6000c3c0da80780222051581264060040711a501c0148018034100004004460080302c104000e44001d44900b170400e0100d40c88010f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 916109694 1250 916108444 916108477
    0x60e011b080c0f0f061005011205132a08060403081b0c010204140f0a0b030106031107020a0e090d05072f120709151404150e091e010507020c0112060b 66
    0x3003c00404101035940441b202c110061218901b20000e03142540d2075400129050316407002482c10f400414614115541050103000c00c03203061101c1c101c0e48070080c1d05c085001030300d03220041032081d0b00042c00380c06aa03043d80c811801c0d40d10748225103003c650724485103540003010044140c50040034005000a080e18204040a81c6040707000c100400d401404503900500740e0f440100301410061060341c0c1160454200402d500c07189a22809040c0b0510a0096001408620100e455101c080c140340c482c039504400c0f12240040c00c0d400740e680b40120340009150070100800703484a45030303240b880c01950481c2040e44080c09440400164031480c10740701e0051550040318200032071800390180000c100c0da0105500c9002c0d007405000d980c200a02441940034035101c00c103800a2082c0d04d101d41004100c4103c0540042c24101c40740e41c1c40c0c0110750f003003a00340b0041d00c2060042417010b104240c05100d403500241820720390b0b040191818211110340c280c030140d4031800000c1c0c441086004000103410300380040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 916110944 1250 916109694 916109713
    0x18130503030f0f150a03141609050f060613140a05041a0f06070503040504020304031e0906080a02030702060f0603030f0c0a060f0908031506090a1d01060e011b080c0f 73
    0xb00e141a004103c1c20320142402c0c401502d9481d140a105e044d242c02420350210501e000c0b1a07030346040c180c903000c4060030075070940014501c03016074403640c002c14080721958a0380c0c403510100304080c040c0410010034080084002c10608841400c0124520806040c0c10050340d039402c0090225003842407602e1804900c0340c40c00d4400e290607040c2150780a000c46480342030172025258160303a80541e0082034003855000001c5000c0c5402035289002c1e41c40e0303041604a9000c8804401040441c113031140710042403000000c00c2e00d0200364020703070b4402c540b6580203080a5032041040c0e6600c8601400c425098041040101e24880c0528014452007036250f000303114012061824008a40b142c0341d040f11007614041d9807400041510088a42068228100180070120000051400c1c404c411006501c150307602400181a00c4406000e005034a0840001000d40e0361958140e80406403104030600185d8112240346500c102e4400c0380d0809401000340c9810200c0c14500280740107060100c0344e9840c0c0c00306070117 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 916112194 1250 916110944 916110961
    0x2070c0f1a16082a060c040902030603010905010c0c0c0b0f0909040f0203010c020d200c09180312190515060a0c12021c02030c0705040f09050a080d0e0304030218130503030f 76
    0x4113145019103001002ea034a49285407682500840c014490215000000304000355000d40044d05115080302c002c20501e0781007600681083c242c50301c116800501032000151801504040ea4044030219008915002440c8208000c0038002442118041d14904840d009614240b00e40f01300e06455800410440000303980107041c1c811a815101c824203080721701c5803144000031070320512084082c0c5010b501521144000b4034228804904a484d0740b01c04500c3e0102d80018045c4c250096694401ca440390b02c0c5552095025680119120120840a55000c60f01400d00344010f007808003071ba00c0e0100b04102140e80d00b41d9800058100c60300103911011030540341741c1d0390803604000c0b080c2e035000035450920030380142501c401441c8503003882159a4140b2400315085a000795041301d03845400e035a03080a0380d113800c007000d40000c007800a00e07510300202d403210020000704550550f50000c01c0209159060404c1c2007002500070b00c1d00903005484000f07440000d0042000d075014500c85c0d0280f2000c0e1070200c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 916113444 1250 916112194 916112257
    0x20d09110a051e0d0305190f08070507030206010302061e0301030f0303051f0303140d0e060a0f090317060a0f06020a0b06010f0507021e06070602070c0f1a1608 70
    0x3aa100e43c8400e4040f404084018004081240041e00e0035107000083c1d040076940390003100d0382d01c54540502011044480da10200320303048a10765403181d404a44640703d040395103014190000b40583d01280041c0003521700716003d09482c0c1d040d000000c1a4518000300e50010750003ea0040700d0301552101c41c00d0402d6014001c040e8070001400300b517200594211440e4424158034070014052000000602140350607000c12034841d00c5046a081c840041003014040d03030382104a91200345c840c0717480140e10040020b0b0151582168041e030f075900001a01403040c00d0914009070006a108030f60090010b50070282401c440020300490b00034121301d1030a802e00c41d10070040181a50704014807410383d01c0c0003a410006491465030183d80103814081044490111401006103c40d84084081440020814070380c0003002d41ca4420522219441d95076850b880301f1a0b0b0358080c403044108070f1400e1880700b0b030040000e0450b410004080b075450700069100c00300d103507200014500c8006a01107200d058141c8005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 916114694 1250 916113444 916113449
    0x50607030c050613050a030f0509060412150203070504060e13050907061106040305041202011205091006140901050d03030219050c0606031c05090a0308030901062102150d020d09110a 80
    0x1a0480810029038500d911401c100c06c009043c0300481c940f001c070992040081e1400000c014020036900c503203a604409810011440495001c6158990244211614020b807030144411781c603150304060900005580103604811070f0740e002080700c2208070aa160314003c1038014140d00e000b83c900d4909110005010010300d40e1180510b61254061000080d8810119002c41e407402e040400154207510040310440b810000083e0101e06040900410306008510f401c0781d2651004100000c41d542d84007001010141d0310003c0e4018047d000402a608020340c030004124803d04d40145841600084201d0b02c0440c03040341c40024401040c03040e1202004c0041540040088000305503905181c4000c01e614a100b0303800008025010400b0309041d120301038a50055507002031450381b80d144c0031076241d00810452140c0c4480d1481401c0d1a803d403400840303011407498001d048200303030100950469403d0340c4140c07100714025500308041503100d8540d01c079145c0c4041c8030381c2c001c50b080030307841c3c0411100b0035954 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 916115944 1250 916114694 916114711
    0x6070303051f06020c100c060c0504061119030509010903060e01050103060609090b042d050f060f040c2306070302011a0609091f0503060a05010323060a0510050607030c0506 76
    0x82c0c00900456030002080858840d08a4544802c1900c0e000200c501154048000303104608100344224070725000070241c03080e6601580c83e100304907907130303400c00c2c1d5501500d01c0e4170607105500302454000b081c4118002c00e02d4047c181409881035a0321381c0d6541c102c1e1342061082034503035541d1006204220150180c00020300244c0b109021b205600d48400e0940c42002d00000e00c1c0000300751000010b03190b1206244181401070303180c00d1841a103410015102e030800ca098840700d00541c8002980a0305c03540c440c60285030400a00c1c06a141481d20b00300141c20070141080d030071105c041d40f500459035140018445644281c1c0040341d201d107111050800110140c440c240700d0030701402181c68139180c0c01d002c1688852860280c1050600c0d9136240b2480e1042500081d8140c05170104108110700075811460407284078449081340034003521403140050000c241ca180068202d4008101b401a9980100e030300706969540071a40300381d0b6040014100d90004000b01c000c034411040030403d11400303008440d441040d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 916117194 1250 916115944 916116001
    0x3030804031e020d08040606050d0605061309081c0f050c0a0305072111090d0812060a140904020111030a0c0b06190302060a05040e040605090c0312090d050c0607030305 74
    0x10382e00003a4a03806101c1d0180204104880003600f031001030f80040008203005001c400c4600980c1c1401c00c00b4203402c0f2100c0d40901003080d40704d01c003103c407032041140306c3c0d4100b1412402d00075807104003200c3d83d0b10000e060380c20b01d4071040a1000c1e03030494454030303005241c9044503030b0f9a26028075000d016198010b00380000d100898401100c081200f841199a1000751400000c05104904c3c5692450203800ca14580100f851004003040040b1034000b080e09601d00004c1c801956141410000d40e8103c0340541181c84024182d94031003408d04800d03503500244141000c46031001548030007441c58002401d010000f501d1500b482090101040c10180c0141c03060b2141b003c20a1082e080f01d58441507480000d0041c0000568a1030302446202030b180a0002c04806061505050801c03034042d240640e12007030780380100b884c6110285400a032107200c00460721300490611031900200048400344d8982a150740c00b501d891180c80303903076101c02003c0c064440e8400048604010503404602080800c030f0743c4840d0784 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 916118444 1250 916117194 916117247
    0x6021b030c150c01050106050a09080615130f1a01031d03030106110f0708031905130e09010e060c040e010807030b0420030f010606081f090504020f0603010303080403 73
    0x100031410703150480060303a00c490902c003400c2d0024014442c0c640b40c400c2035440c00b400814507992240c002e107240303034090360b80c3c0e2411501d5004c515126003080c2c41050040000b444441d00c1414001e030308900e24660014002651800244401d040c0c0d9164000f100e411900d4a400c0034041d80c152040c3c2c0a007008a02221881401021105550784410300a0750288040c0e1381408411410401c512000140d89009440b2107540d600092a625000010007110112031405501012842402a11003912440301c0c0c0300740c291b2400201020501e4060941e5000b5504d450546071641410007406000c0c003114644c1c1030350340e803400150b00e52002040e0054091a042403c0c200041000300f000380e038205402032441d01c81c540050b8030341c1d111034540c9001036406015401003400488019449401103401031744817000e09580742403c0c1103065600e801c0d42141c0c0009402c1c103020315070003940a00d50003440900320a4840e01c55400280040d0800d9004800140481d0104030400d07510054440203140e544060401490 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 916119694 1250 916118444 916118449
    0x10b090103020904210203030106030f020906030411060f180901090501081203071b05030d0f0510090e0c0411030a0c050702010915140c030c061003020102030301031b0e0c030106021b 80
    0x10410700c40a071103400c0d03003404030303080c48440320400b41040c0688000c0d0b42c0000e034480c40a51650424803884022074078028007035000030b80034000c40b0456040142078601c2c0d130b619541c42c800050f6110281941001c4180010403481c140c1e20700030202d0442119184002c15881800c01a880405030084510302d4106401000450340024040d0811650a0b00300c40d203a40d1100801c450940b20810001d0340005901031013028020040300401c14031543e000240010308d0300148103000c3e28410b862280348989101810800c0d0000da0303020548000d005419210802d9662000805954004101e003580305800400d20001500c0d03442604203c5019040903824135104c0d400107081c6a150740b1450b00403030703a5440c031291198480d0f003008511007500755990380c4420036196401d5403074000e005001010710901c00400d001e03035000d090440480f50705a0046145a00b076076a1020082d0380b07000c00403014801c601000c140407800041d200c0c8903508520f919a1a0741c5030040081c42e064155aa02c00810010241d50f5001d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 916120944 1250 916119694 916119709
    0x60e010b0702121203043e030613150f06150f02070905011410021c030608070b130620070608070e0409020a1511030c0706180803160309030f030917010b 67
    0x5400c500880c1c500c10302c01680d0a4041c54002c1030034407030210040005886e100c7d495002c00b1401c0207408540b03055a401c840c150740b000341d0b0341001c2c20800c0b40c24105030100d101074104001041c0c0071103000c220165030390001507502c01880c40c40b50125810005000342030303034100075081c0200002e20081c0941c0d4941080050803200c15038a00d4068149000400e90090003040500441714440104600c503600001000f0010301060050100c1c1d40200030000813041c0161003610406e04000090b003040c24a03142058860301c594500c3c40c504002e1081120395407040501140009051a0310303400d24034500403e00910340c07030a030700a9070300c41c034a0056010096110403003007030295964141050000352103800300381e6807501d43d801e07402c01511000030a0074030040040703119800c464031a12034032020a40c40d0700d071070b02c845200e0040c006d0700da0081c070844c02050381d00221240014064140135116071780341c0e10f586508044184060300400c0144400f0002e10080640b0008103003c00c0c00208042c88101d0000fa070032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 916122194 1250 916120944 916120951
    0x601060c26070b04020f031212090703020d141606051b01020f0f04030c090c0203070611040e010b1201060e012309040e070612060f0b03040501060e010b0702121203 72
    0x8070000114282070016049a8050003a041d05a4041d11015507203000c0c4140041200c1c200c1c01007041d40b60410031401d0004040c414046a005074500348221400a07598000d0002c1c003180d02c5204d03003040000542c840202240006000d0181d08e203400d1041c41d02c26117031071041500d05820f0509a032080104a9115080e84e41044400f0100301d050000b105030315019004020524003d1800024034034a4603101c40020000c40b8420a82c4001541d40e421068080345d0203000040050381041200d5000500f2070f40c410070200004442150425454010340d12290809800103550f100c80040d401c00d40109840070540141110b20b00002c1032003a04000820341c0b4a200c00c00031030118030741c0301c140010b50580c1c00c0d00d010460180041000183d0b11428542c0ca100d94881c00c0040f0751403800100c44082c1034000d4006070713900c1c401d01100342854002c11005540c070042060340d50395030741d10000c2102440d220b0314031b0007403048100385900d83c0c0490041161851981c1025111030b80076641902c030700c10105044c0c0e40e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 916123444 1250 916122194 916122203
    0x20160606050a120807260a030f0204061407061107030314251107090f02040f12020901030b0601020c09012306031012021507060507111908030a0b0307080a05010e0601060c 75
    0x11030b000d4074505184d03464107400c4070b24603006c4540c00520800306040d0140180c45035a540520000800556102c01c038812170081c00b0006500728107035000c40f02500300405280388548800211001350302000c5400307820000003180041e4807910114641d805010f4085d030051183c155084080000d90903595403c00d06564140030b01c039100900c0c4004d40401d2014000401810a00f0700c02c42e4000c038600c40c002d43c800d02070307182148003110011400c645c0312089080e52035805855401d559085458117004000b0003040e050440c8119003040d0b5481e1262320145008001da09984010300000e20074044082c0c014010082c00f8042c148104403d11101404070400c40e602c4103103066540c41c0c20b00220f081031031280c4a10900080c0000da4408201d1264003ea1103140b4569520902c0105822820380b1a428011629084854040c011000c50100402942c104d14208000990000d684000c170f41002c490b60300040c1e00380c010b07401c2401480400e018155070568400c020340100d41c1005000362010090310000360 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 916124694 1250 916123444 916123447
    0xb07030b0d030e041e06030303052d040807150f0e1212070c1b060e060c0c09070e04060905040b0c070314071a270c0d0620160606050a1208 61
    0x100b00392a141d0000c0301484a07441c1032007001001c503c0d4600030304447e10088000a00d0440006d03130707038503032504403041c00c130024074840d00400703103840c00700401140181c404e58080c8410002c038000650840ca1807044407000101c0440d003103039252541001c9039411000c083c26500806011000004500121422060b0071251032403207445581085504a050400080240b204203a024061550206400c1e0441c0d00568030100150110b03800c1c05a20702490a4070403107035121103230341d091a1414032451640014030f854405444050f8a0000e0140d80b099448010781d1907448017031006105d80041980d03402201420030b90700e0401c05581c020400400744480b001840400b0400400b0403501040c0c01040b100758500c10f0180d410308610ba84142c45007010040040c42000340320062150703000c91500407a02000340b0713551001038141ca45201074074041450032046528001c10100c0410040041c20384020000c000503c1d110b0f0030f02e4044101c42580e04981e220f0110700000b000000311503500d40c01d04950000609 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 916125944 1250 916124694 916124717
    0x50109180905060403170108030909010e2a09031e0d1b0605070f020c0d031d040207060f050403080c0403020f040f02070209010e2d13141203040b07030b0d03 69
    0xe00140312045000300305016030710a10040c0755000c1c2040d9814022001c2900c170350b990b0f078040036070b8031300c035914002d0f811a201c80010400400034006003070b070042c0c0020001803081c103500e15030140e4940e010800c80e820100402d81c400a03040c10800400304001030042600600c40e0801910f64402d00c1c00e00e843c04010007540c10500444070a04400c281c182c0c03100c401d00090400200113800d8812010f01c5000500c0788080300303000c2d442c04580b503505680d0551075120230a10460b5a0300f840000d51040c2503003064081184c4030005e4403a110b021001c1d2040000040c81d03003020310b801400301d080901180c0c03406205000610140e5202c0e12450b8900504403400101082c1020900010b40a034120283d07000700c4805c000941c41026040481c807460b05c0c480407a41c008060000740144540040c0c040c29200582c400003170052260400c00c501c028021003c3c40c201d42e91190300945050740a0340c000c200500d0200c24402040070201d800ca80200b42401c1c24800982000003040f4032171b441d40703070240800c600840c80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 916127194 1250 916125944 916125989
    0x70f05030c0f04020c0a1725030c20030604140105090f0d08060a15030f050645010902070c0e040b0a2d1509110301120c0f090c09080304050109 63
    0xb01c034009510884400d00f41d0307402c000319082070301704400f0740b1074205c0c00d0401404510362001d540b42c0ca1590503144cae0745500c6803a44800a00c28165a03800d0040b00c0f000103012030b40e550400090340710318131814074582d1804d8a5900309082d1a0042d060007055404000e6801c00640301091f4034008007000d14041c059540d44800080c2c0048003a03103c900030044c400103407104294140c01c60300d0103c440c0d000502403901c40380c040c865503043c510942084110543c4645118004100c1e028080c81400c070441003c3d440b0a160703c403003c000a070302400c0c0281c0d002520384100008101c210000300190220341d0a1840c01e62113036208000c00405e0074654941d9801c07002421aa1005030713810882e0751003c1030078581c135801c0e5804010001e5451840e0815440403000401c038400c2e000d800340100b520150682146d2809103002000a40c10408075500c04441e800466064803034180f000040c2020341010842259030740c000303004207015030040041034208100c184107507600709828bc41210704d44c084404464040841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 916128444 1250 916127194 916127203
    0xf0807080919060203040b0105090c07060b130c0f0f020106061d120f15060f010f0f030209030105100501031409030f0d110d14071e0f0c050708070f05030c0f04020c 72
    0x90070310b115001c0010060034002c681d8003840c0b10701e05c1904042e183d40d8039041000a00f410464555441040070001100000d06e82e030041c283c001400340034a001d0824241d1031006440c20003202800060544100071000c540c05405010701c08030500003000f80340d041c40001440030108a960a0f03840d010402d014541e40c4600034400c0c5180361040c1036400d120001c102094550101d44035400150701b003400802c035a40b9207485201c00100d0b0503180c0421210b40900107844c85440030f6218010306a0030b001c120800d8a080c0640c510600520f080505002e0401c400542201c0e2a816040d036000207450402400810000807151500c40e000c0c00c15803280484170020001c0c11002403026001e007000f09420030549070a41048504440c082200c80c10380d60f03a507404031035210b8410310700e080c04090710b040803213010b000b000282100c40a502e055210b5001d0703a15018500500760344100031940c0900f03000c0000d10040c0c10307200c010740800c40140801d25140e1000071911000a45018403d903400500c03120075400030030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 916129694 1250 916128444 916128463
    0x12150c08180a150c090602120406080613020304060b010f0c03021f0f0f020d0c050a021f022a0c0d050a020402030a020c1605040f060303120b030c1503090d0f08070809 73
    0x240242ca40d044507043e220003802040245002144102e20701140303a03400401e203800c1c07403007000c2815400e1614021040b249544041d019503007103841c4000701c41c10341d111400107602c124040c1130007282c2608500001050500040400010041070003003460020350f01051801d070440390704200c000700105a4030004010182400d002caa910f25000100000303a8141c0c02030491100000e1042102562808081c0c800e485a04080c1005070851140080b8820031a0202000c114501c40010308011181c1d40c5241c240004092000d03040c0c0c10680c21008880b401c01c809041c109054401c11894078460703032140d54403010f011009100d250007000040070b080c40390303040e9502000d0880890380760540d0181e441a943c0070724000c2c10f02a41c2000c40080c07281c0000c0c00343c8001c40ba4141d8910409600954110004220b40d50b80e496141c0181250000c480d038850045504924568103090307a40d0400020071840c041c00c0203118400e00c940034508001d1aa000f1354051750240c06802e00302200c0c0d031203207000780c01c00c0f8100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 916130944 1250 916129694 916129703
    0xe070c03030b1e1302040b0a0c0f020a0612050603030c340e070807020d08060f240c1006080604230304091d07030c1202030c0a12150c08180a 62
    0x6a00c0035400d81c01d1401101100c40540307006034540413965858059114030b00032052494020044141402c0c40f800e00c0003c02070003558103c01c1d4400c5540058a140440c4d030080700003a040a0400e00144850304c94180c10203c03c0f402540f42c40c0c00a8a40c075192008004220700e68555610020b044d0010100071030000115040380c200c2e0305455242443c3e1140d02034400500007000c071800070700b03920300014203034200740e0054864100740d5946404200d1607102c40a209a08041943c1c4019012110304518401201e0700d001d8054454031103100b030324034100448050484044c2420020411008040b03011a04960821010a40d0002060030301401e0401e88103500c40d2440300041c0081e41100035403001c500c2d01501481007408811401c905a034810042c0005000c1c03c40c0f12804004a540c110340d4042e000c1d1002e81950000b001d00c20014403951603a0340071107602e01403882e138801000201842c41250803000b1904224143c01e484000b08000d10080101080400702c10001074100810000d14591a0b4071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 916132194 1250 916130944 916130959
    0x30c052e03020f0d06260703051b03150f152403061f0c02040f3305030307061b0813080304031b0c03060e03040302030a060c05130e0702060606040e070c03030b 70
    0xc41030300c16101c007800d520300c1c1030304d606d082103c1d400c06001140100c102c980007030042c002916070040b1480e2003000c2058140d0306106118800f47e4078440c0030310b242e20a1041d554214500d1804038118a4090300d4207a00c0c612a440540030301c04100702d405002c01103240558805904c90f9540e202240070501016801c40204034107040700f2140e83c1c0d00001c03110b40c5070f10a850030302061511030110002d80310840000b8041210f07800302000100a0ba8808044189446450444c00c59507480424110b600c50f21007a54100e0719080c5281c04542104c006005001ea10f1410040501d031500c6824503494900800802601001012509261040180c46202c51401c602c05070740f68014a80206840f0f12031000b243c0d41380c10722140c0c0410880210680e000c603078001d40506002c1e40590740d8078004102e610480320074090140300720074440c064a080c00303001d08240d09080c222030a00041c041e140442c01480d031880b628040000b404040780303520b01650441703864105600f045c1c019140c158081c000c0346194a411406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 916133444 1250 916132194 916132199
    0x90804090f0e1b130501320d0b1e0f04080c150f04050d0201020f1819080a150c14160209090c0a09020a020c010c050a0c030c052e03020f0d06 62
    0x1c007015140c501c00802c4851043c07001c110503404090b50004d10500c140b124101307001e041c11248140c216854030b413101d846001c7d00c015080000e8403034001204140c40703600400040014210303408042c1103802800c2c0050882070b26140a071000301d0070700200f000b001001d02041d440c01f8541d00b0050610740c900001d52a507560703d0505544210340d0400c54064801348036034003401036103d0042c401c0311081007840e44114600040141050841e5960040c0039401c49183c440070000d81d03402c00c042801410388035000e42003040241c01c0417004c000e540107849088a01c2c4c2500031141c203401c40f0040702e0300070081c070130701d6201d1a40c040c0302e0701421082d0101035007003403800381004000c070700118440700c818408481c40c000c5030351240d04070000c9001e040c401d5000b6a101c40100000c039070142c101c25826510a03001c5940c0380d4039540d94003000e8001d6500807500c01c40741716003c2c002890420503000844070f00a406140140c08613140102ca000410603c1c41816800244500b0b003401b16001c48207482002c4c10140310b0107030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 916134694 1250 916133444 916133473
    0x30807171209010b09060907030e030f0304050a140606180403030e0d02010b0102070e0f18100f020301240917072103090b1c0b01030212040f02030f01090804090f0e 72
    0x7141159181540d5291600c1c11140c0e28120307210a024a502401015240c0c1d14900c0586c01040c02c80440c1c44140310900c0b00560f00700e6140021407040303110307801611403a9030928045100780c2c00a22250099008201000300caa240d242c8101034080004100242c244c82e142070540040400580d440f82c580280003c1140c09501500240071012081c3d0841d00d455644039000382084c0e905076002064000704c0070104140e002e0044811130f03961200c20988411801000c009001c448034000d458040c1600800108044c0d91000e29104212031302805810584030b0102006025010340e000359002c0c19082101c0400300c2c401000a840688040b1480c1d10a45120425401100c076001c0c0c000c80c0040c0e55400e02203803094a41e41940c8510184200c01d0105042410400c4050601d040c0001e040560922441407001b0078000224013983c00380c03c0303800b18000c00d801850306200005032600b42c43d07814084e645000904280480b03040b1020305000192031483c1140241c0a00702c628000b401c0384c1b00303c408800108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 916135944 1250 916134694 916134727
    0x4050301090b040309272a081906060c060905010b060a0513090917030606073002030306060d09020a031406090f1f05100b0307111b0a03080717 63
    0x101c0c000c0c2c0b107a02c5150340d120100d01c6c2d000e506220341d86c018000e01c4510258038141790080191000020781a01d0380340050040e042e4581500302c56440051940020310020080f8450360204500209000384151030030203c000e02718822040b40201560b81d00d00c15402403042c00c1d881940703540e00040c10360b590b41c2601c1d10000c110b45c0003055007602446500c1f1002403030032094840e00a2490f805003c4050168680b001da1056403c014003d6803c61820802c0f980003c0140c1040080c00b240f6030500701300180c400d00034100b074144007144074040d58410230905c0b4803550760b13405545084103421b5021880e0007480c808680e40e07007480d5100408148848551444003440803505603c0f48581d0703001c072900d03203003c80d81242c2d80c1c1c00000803040d007200c2c107545981203541d01904403e5006606803000d05400759078121000f403070750003141c40600007070307001c1d4171880180001d200e02c1102c000c4031114000241c1c103200c009035a1900600c4020020040000c4035001c00011402440d4a4130200c0049500d8202121265815 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 916137194 1250 916135944 916135951
    0x90613141f1202030607050f090d060906201801200706110a0b31060209100302040803040b160503071b05270a0906021306080606180f0604050301090b 66
    0x401c00d409801081c4912009102030503181c00030000d16030f94541801c00c0d0b5003640300d5210020740c1d01d0108040803681c0c40c0c000c401052180304510000c0c002c0302030b00b096021103513441001001c00c41c40169081e00c40d0491400d0f10781c4500c8074030034404a14491001642e401c80180369080d15904c45020b4911f00000c0071419104070350031500d90b1500c40d010181d40c80e80327071140350000800002214001c5504190719925810221100300e4007500008060001e03049111001c1400319981d58001415600c581084890241d2041301c6050650030941072030245500e901aa026141c5410404169045008600c0d0740b1011390540020940303a44045d00e060100c00710302d000034454034800301107500042d00d0400413000240001f43c4c03a80c074041403491550713040f110703040a00000320700782c0c64521040106449100800c0750325000000c5100051420350041c1c600d40c4001e02c40c41c03180d0024060f031400030350000f544044228085a00c0055504028009403590155800080c2c266190440074400c2040001d1003500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 916138444 1250 916137194 916137241
    0x60406060f0f0309110d0b090f0a03020a1205091306050102011a01121d010c020606040f0c0f05030403090306060303020a03120c09060825020703140c09061314 70
    0x4168995406440751100011000d001500020350200990310a41c44501403d1007132880c0d070a1401040000390300540c1480c001c0e144410b6200502114101c10441102e0b8514001c02505440106450103074403840300c8400580f0f8004540e401d01d1405206904444003030000400c420001136082c0400c10082c0307694040eaa0242d80307055600814652078114503a02110140c0d11450b01d00d02e4040240003900164800ca10400105c20034034a104500b1300807414007a00e158000c3c40140307050810842a82c0f0240002c4c5111442c2032016081140d00112600b45801c407810150780d42d854a1900310364041c0c80b41d101030180c52601002104140c1d010070502640c5000f0780d144032000a03042510070031654001510310115240182c1004144d0060442540c0a90b40a10281c0826003c811501815114404010041e04080400d004010f849a007010000b030300d4400400700c3e5890300c00403884510010b01000e1092a400000480008850700018055090201c0d00d1900741000700c03810201d040c10070400341 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 916139694 1250 916138444 916138451
    0xc050a0905062802011d0a02010305060a0302030d201905061803180103021b070e010b03091b12070f0513143d0501030608060603100e010f090b0604 65
    0x1401d45004415240402000d04002c0000003656051148a100703082c0840d00399500c0b0030300f8020800041c000300002c010020050120803580d0301c00101280d00043c0094803c0324421800e002603180080d2105500285042c440090052800409280c00b84003145070314510a8001010990f85070b003902c250107512550403510940c4484045003140c000390b00400e503041c0e1060010018110390640102c00008040c1001440c04555955500c0d5600200038945110382c01108200004100c415140e40144403010200c1e05509080707541c0e5481d41103495510844c1032911040651641d601d0102c0e0940c0320240c000c451005581d41c0c00c001c0b03041034600c1040e01c1601d981d009007076148018010012030002c4034482801540d1a0b02c0e45c00000320315101513030000319103100110703602421141c055001c035030104103e0945c50719101c001026241c46400000301c40d08104148050340d100011040c8030070b011401c0c080740b18100040300c680140901c4500c501820f050540c408107204008012a000314001c0d203050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 916140944 1250 916139694 916139699
    0x512070c03061a030a020910090509031b2a180a05010806010515092b2109051f02010f18050c0109030305072405010e0a0e120d0e0309040c050a09 64
    0x228020f00c2120076050381140100e41d00624007003e11540c01b080c000041140075403690041022258200c0e15101c2c507038400036100a0940e15000c000351420001001003a81801c4444d001c01c048081a41800800d0740c44816044155904081c0d401c030486000d82c50007080c40c1c10790400029107801e1103560a42d00030000040307460304085042c0524500c1c0709c1241031810701070506104c916500d0160080c10744020390a0940c0040840483c0440c46001b11980005d052084d840102800d8411401505001d14a1810000764980100c1d54042ca07040f502c48148203001558280d000d000082d0756000380702d140113400c05407034000030140a44580284204e807403000b540c03001980c14905600018002c10002e110900c005040a0094516410b00d000501d02103031a40d9070a200742c8401380c000b0140550740004000c0030403054840d111252500d280181b00d0321100101280d03d512600c0c00c4d00100b40e85030300e0106883c070403c0084420008020f00100289a80da00c001400c94010080002c002131010000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 916142194 1250 916140944 916140971
    0x60f0518030418020f071506060c020a050105070204141e100f180209060403061a10090506161217090f0304060c021807050d0b01050c0c010503040512070c0306 70
    0xa5100300e89009005614050501c1c060202c1e041c400180d01409580801c59801a03610a401401d4201c1c4101036040c4401071b080004c105640b80380d044031003007088221102000d82d640d001c40c0d50807274400b070034840ea035640d650022801916204070035000300c44290701801000003c001d2240c40da14070000c08d114880d11003c40689105010344110302d035030040b1103424003000b001d6011904101011050040c503128040c408203c3c150400c0d40140c1f040b596402071880301c0c109440345030525003000c45d20250812224030b0068030043ea28000c1030701a01000c00c42e1340c409180d0b5410380c039003550000580106001c443c28020103881e21a0030103006c500310390340403034108100044c00e98a8100c00002a60900b0704005045070405441c40050380d02004a0109426950180d106035006045507900e4a80c1d8120b01d4034004140e54031030190300c2c1041010041250b003650b000c1410644203c00746412075690b102c40c20040e20b4101c400b00c0c1240c1c8900700095080c10001c9030294801100c2c8115010f004216000380b5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 916143444 1250 916142194 916142221
    0xf0118080d0b04140907170705010f02070806090d030501050d0f080d06030203010608100c1805011209061e0b010903022b0812100e0103081c020c03041409060919050709050904060f05 80
    0x20904c207d82e026040038003d40d03000e1f69079000030301d28501c12a10700540d01c022651a01c4d1060702c8010f076a810a42488445503414010280034203416514900c1d0707524255074940c0600c10b8070101401d8010049484d040d50000717600250000c40d0020001e01405480e01074540d21003c11a5a0080461802582840b214080d0940885400783c58003513442c214034050065902c01800740d851148035035a04520400104948500400001c285d01d0384c4040180e00c0c3c0c04281114a5000c845040c001e001c1c1c8100016510708804100e011070318402c8010740c1b50401c0208940c000c1000c4002e00071040420356012044401003880c0c400d03401c0f0a0b541d411256141c0118204120030300000e00420380800c9400c4800c44000401000c90115240052030411380c1800c0c982150403a0b00100351114010304c0d00070840c5402d81c040c0744c0104c2c003280c5410791803c02540b58030300c7c7e00794000309005454030f890002e14001e00a5080200900000e03000303c44a284c180740440050084c03070b94402545181c074001c2075800c0801070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 916144694 1250 916143444 916143479
    0x50103020310020313060c0804030f033b0105070c0c0915060e0f03420711010b03030f04090c08010e180703020a0806090f0118080d0b04140907 63
    0x401038240700c082c001034040a940010714540e0007001c0c007650b0000081c080c0c07060400705101587ca9005508017480c1c008d00419900b036503401094203041c161400b00405072043e08800d940061460b01d10700701681c405001002c0c8600d02d082c0f9502e04010400569000341c101310720140b00d00c844d80a040d4a43c0307a0001190351080200c00d81918440086c01024021454602d061000503d45501c41d0700e0280002d292001c00c6028943e540c170040600b080008040403441c004000c03422990a07410340230804c05001c4400100540d04005020805001da0003003035119880c00c01c000b4080d6a91100c00c2d1202502c1075100e446200c540b00d1a1440c0c0c122181c0c40b4901581c1070340e90544500742c07030352684030500b44840b564200145090091000c0000142e0300c006008001740007240141c8031605d8000625401d04103003140c180400e07410701c41302d000e0004400807030146055214410503203e200c08089000182401901c15811624081c0030703014152900d034910344101c0401c001c03600301c241c07150001d071401c0880c40c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 916145944 1250 916144694 916144699
    0xf0415020d020d0804031806021c051602190f12022b0605091f0b040b01110604020d03030b030a0f15020a09090504080c030a0f0f09080318030c03121c05010302 70
    0x3e000d01c9010310312400e003090304640207242110f40718656468004140d40142e2214001d64403031000714030b08018007040d40d10b0f0100b107410b010b030038089034441e140c61220004000034441e840201640b450501c601400740007a1100d8418540c0040e140c030107541d01056250000c0c1e1044800383d240b200800c18400da00c9041e01c40d070000c041803040c1d9070303500c41000d410060002e010a001c2d012000d02105207c288203201307030101d00800314108110506200446030708000b140c2c100040801440d1101c4800203c60750400c1d419616030a80001c5400c04500400048080f00d50502980c221a0280700e08040703040c03012400307011202c00703250408120b03404a10409040901040e644041001003000a9001c4c9030321074090110986804c8007005d10509540c000101100441c4150342c3e040350540e40301030501c1e24078401341413015601d424a04116600d00442903160000480e554414496480501400300541800380840e0109544d013145c031a1a03400004891080429440440d80c08400b14041c8a0480360007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 916147194 1250 916145944 916145953
    0x100b0403030e0d030e060a08061302030f0718050d030f11010e0d03021b031c060509070c0f1407090f0f0504081c091a060306071d0d110301020f0415020d02 68
    0x264240000e414400c0c0068007840002c001790501511614020b20604c1c02a41d82c1c9051440c04004109030300089450302c3c4060b91040c070400020140c040f050542142c500d080c03070704030107481108000c11220203802c9146c01c580741810b07080416030010251902d4a00350b8403050485210b425916003201e0484e181c510855005000c038240380780c0030313a0052100f50100040c0d59841c002d0210140e29592211034034003103004800941c40c0c1420b14074402d02c1c0203040c08a07600304440c1024000245013040c1410b010b004940711903189030401c404551400300c0444903500b030304d00d059034540c21030000703104490b40303031502c58104103142e0500c0703405118552003560f02030320403070034002c41064545440c0e012712600d190280d680c0d80000b000c034200f58034000d0f413070300142d00d00b039400e01c0c0c4034040c5030601c0c2020f0450f9040c0b000349910341d5802c0c0d0f10b5440190300326006032a0305060340141d00304100c800413800c143c0c17034141d4400980004504044002070090703038501c0500076018544228201ea45146a4036440010b811 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 916148444 1250 916147194 916147217
    0x1109071d061c0e0328020d0e0f040606021c0c020a0e07050f13030c050f010e090a0f0f02040510050f2502040c09180209030601030f02010323100b040303 67
    0xa0280180152015542c0e4034100d42c0d8212074404203c80c030001901c1d1003503101044160f0300d0081144524414020014150b4804503600c9010f036550406504500511040714134181c01c41c1c94604c60a150040014000d12006580e2817010703464a20411503a04012480e458030844280601c60111445502400400c4c003240307400008407049401038152002c000003000110007648101c009442050382c1258a540060f02e540740900b0050500e03400386004003001d4040c40081d03031300903104d00071565007507031404e02c20b980388a82500204140070201254620700010030700844101c0d4041c0054031401d0b10031501c042401d120540d40d60052030b90b229000801004002001050071000040c069402000012188041d034000b45c1039515415500e030001c1c0000030104440c3c440491300545207000400c046240180c0c400100343c68140500007d000103429801e03031030071a4441d910150214000350214a488c0c582031404015581e02520201446d00c0d1000e40858048007410481d0202e95064456010130035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 916149694 1250 916148444 916148449
    0x110a06050a0b0d0c17070317040e071b030c060b21070608040203030a110c06285c01050603062418010b0a12061a0f13031109071d 57
    0x190400040c0c0c6c0203c10000001034689480a500700801c034101c6915203003003d1240d960400d008080d4810803682080c0c0340b100303807240840d42030619058034015000d00c6940c10900701400c0000906a040380240448494201d000c421130f0300c1001000c4196560700340c3d82c2608403824a01510f0181d891340041014410241c00b030340c83ca0a02c0440c1d00243d03451001c00c2ea0001d4215044210000c940114000c82000108441d48018261801608002001a000d10b590602500703c1050070707200d00a00041e030382c07165121442c84070040d5144c0010054480382441d04800398030080e10b84e0816542c05c4c80042600352601284852048600c20812410900b80c14212442c840b007180165401c038140030512750280801034603140c0a48500c80a96642e10b450300c000421800811217140f801c180b038120180700b510000c11403842003103060700f130a80c0c4891150030030011030f00c906004034414240b0980000100203104404a42034502210313101e484e95142c40e810350704e07030340011561903079032617424026003252 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 916150944 1250 916149694 916149719
    0x3070b18030303130201031409060a110408010501090b011803020f061b010923030306060703050a05161518050616030e03030f0114060703050415110a06050a0b0d0c 72
    0x1145280803440854403a0303408681558000d0b10400d0556050b07140d0803065507018000c05a050040072040e0601e07140000e40c031b58881c1c81c0602803108036a05c503041c0b900001d49480c1641e000d003000000810055039180e140e400105401268280400d80000400703001c0161031101e02d0403690040c1804858009150400c01594048202040070b000e044a10f000c02082c00d1207405481072040d2405072241c52106004982c0c410b80540c4036400c2d500c2041040b189440300d4099400e0583c0c542800c0c0d0700c51211840640e542e000c1c0c0070380d200410302141c0900d0f0a0052884942018210b0071508000315203203400c407000684820140038ac8240c0c400340100341c00c00880d95001d50545030f14076001560310b02d404c422a0a50b8000d940700d05080480a005200884c504c0309040b2103088100c1d4410702c0c1c143e199a000d80329000300e2007644c4c92110030100c0340d110381d8090780d00c01c40f8401403001543d048115900c0d0040003800d0a90320020b145261205940c25420003000c409840390b0410b01d4590410729103141c44241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 916152194 1250 916150944 916150957
    0x3120c151315060b0d06170307170a021903032910080a11040b03190209010804030f2d020c010e0105070602030c160308011805100308030a1b03060503070902030603070b 74
    0x82c0d507104030005881e820900a0403e9803c00000400d0075403418080b1030440e0b20709040c10880d078004020754000200040103000740c00302c0c1240f0f425264032050005a090024496296420b40141c078100c078205641940250038018092400d02214440b0030101030b002d00f440c1d44034075041821546c0c620f01c01ca00581c84642d12294a54012940698a41285441d034016a100815010020040c000401004803c3c544401400e01c0214208811800003d16080d409000a01441800c0d04a1561588143d002011546001d10744005507450009880ea018000e4070383d182c01070140030030300e9001e988504422248194140d40d11420300803030b41c0306c14009500c00351422030300c031800b005929840d1065081c2e500c1000c1c00b9071116210356151003807245070141004082406140f500d1308114882101d070011406490300706c02010f49035542c1c030980000070f04058810b194400800802c8003a0709606401c414285c4105400340d0340e91075629501c54069000036501d140c0d040d00311650074420100c001016018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 916153444 1250 916152194 916152233
    0x801090e0c03011806050604050f220203010912170712020f04050a060c0b01091503150b030106230d051c02100e0d091d0414010b03120c1513 62
    0x20240781c0600081c00c65003028022154444182d8107542400312522a00c0c0e0701075170990782403203140b0700001c60350744000703006048078540c00c2c05100344840710007144c5184200c16805002001141c0840c1007043d00110045241d100042e0044e07030b605484812049154000c01d0f4903282c502004148844480103508041c401400c50b9005100008540d66508039000081485858030700810030a400c16091140e8140c100d0010b45082c03442c1d50b03030000e0810b00c40740100ca8110902481350b80403c04104064003005040f16450341c01d040000c20380710004907442c076200c801022502118282c8500303002c64944d5000003c1c0ca1504820045000400000304403691002d0340c0c410b50301c4280124020b88100d85001190808035800b82c201e2140943d000800c041c003130044002000d01103080b400c6101c0958000610080c0071918840028118a50941080c40e00e50030080903240e4511003640001842e81000c0007140710b6100e28407000f1501806402007a01070012107a07154201241600e80c9081821003895500c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 916154694 1250 916153444 916153453
    0x111c06020c21030912130b07030e06030a140a0b0607020915061306031a1309230312062b020604031a07090503030a050a030b0f0901060525030801090e 66
    0x480202c000240104400c6154480c00c000700754618000d5440060340c82c14000b00f201061054117803405808036030000e0001c030350341d014504c0d04480203900d41d000d240d023110000c02801100304040d000700701d9028003030000b242c89503140076100702070710540c01126070080c00030040e01d000b60402c2c0021030780c40241d0303501e0140c201d02503002140716644601d1342005115400c030402c0c081254580607820210041d841a070048460307030700006c1c9034411048480c01034969500c08900420050b100160707010300410000c280000d802404281c1c4070360004500c4410089004005401d42c602159003402e01c90024100000c4494002c034107403000403404c00c0c1603900507000e110000010f0590403148510341403d41103503c803810b00080103406542e064105520a400c2800580d081603440001d584a61109140106104d0441c03000b00d0400800c01e94945d4000001a0020800c280c000c401030841c000c8106090b030510004142d0149241c15580d002400241c1c241c0040190b68101d801034814480380c1c0d41900c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 916155944 1250 916154694 916154713
    0xa06090314120307090608010f03170903010b060c030c101a0909150709060f08040b1909171209030a0e09091c02060613140109090302030c1207111c06020c 68
    0x522164104840107000500c032000f042c07017000e0f4080860341c010704c00f270303100b0010181c1566140301c0d01900420492142c804003042080c1c45070f038250850700101201030880b41d0798250122a1a890754042c090080440c0b0448042030011104d910440b008450180448081c00b15113800700300daa2600540004a1482000c0260000180d03820506004140781e40b05c910700c0c1d500c1c21501514908a0b000110701380600c0b03204110204010255099000074100358185101207148550070003000d003100007510f403800c288102405041c0c1040100b144000c15a4200705543c0c4118501d95070788211070030701000500200f59106181400a00d00c0d81140408050b24900380c03001350000352400d05000b4500050313006905019242c203103480072502d0307512420700a2010a010304030800c240c10b81803040c2e004d45581c0ba0b140b2002d0500c24825103014003810001d4900e8030091046052050b00541c0090f641e016510610b0034183c900244102c4103100240c0200c003100c49130351aa04003e410580320100d05000e01d0904 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 916157194 1250 916155944 916155973
    0x15060f0b2d030f0a0506010216030204112701022e051003120e040f0605090c070305040b0409050702150702191b0914070e0102100f02040b0c0a02040b0a06090314 71
    0x107940310f01e8120324101c00514110804e1000e5034000750010703066400c0b030780d4081515440700f5503d00580380c066a0104103410191150645403040c1440000c041c0c81039040340d11000a0342c004140016030036421142c4811204807080d1002d42d403a582c00001a5034045400c00681107a000941d024481d80e43e40c03a00665a511001c0703d24076840c080d400020000349422465180900c6030540910000d01c040061a0030309000c140034000c098000302c045200800c0420401d0b1248040314050140c07a440191920b5407608064003034041070710f0301030241c010202c12104419843c1103061081800e0b50081030302c105410203410039841064001c2e100b61003055014011105200c2c540e000500301450300080b0084900405200314201030980020050030b1009207070945ea000613940550381036484c0022f010400c00300f07010024400c070b901c2141e419a0200300c1c003100c410b02041000002e8003c3c0c5092000040c000c042140c500310f940185404a03411040a2002c01d03001c9031780318102e4990408952003450380180c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 916158444 1250 916157194 916157197
    0x20a02280306150f0e060907081909080d022a0604030503060d06060b04080a020111010c09051005130e090f0706080703020d0905030301030b090d110a06020304050c09010315060f0b2d 80
    0xf100501003680b105004c1c09047c20541160f11074003910b00003180d8144082a240b007810100c14640b00315454060f0401449442821a841c103144500119078400e00011144101035007100b0200b82c05445160f180f00c107020218216100e15895504c25166566071020400c0f0380c3c103401c0080d540f42d552034002003080103401009101a05200c0c0051080c02c40c0e030300c001040c030b84504d41e0070200c9904042544007181c0c0c0103803c070002e82d18219141d20405240c820102c540c3d0007400c40c105c2141c12008000074409091030358250180c01e10320706455512500001056440001d4882c90000070201c40000701c01900c6039000d89281c501c400300c08a1038040c0b5031181d520755002a00107640003800d210034040010020890040321212034100b05060100c0e070640591110803101018000607000000242040710521400c00c1c1800024800001942c6a0400341242103c1088800c0c0840c6001d4000c54030050b010744040884142d800d0481c41c05281c41e00780d0400c504090741d502d0840ca6401d80180243d0007420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 916159694 1250 916158444 916158449
    0x60415021e03090a05031626031912090b01050105030606070501060f09140c0322050d0f120905072907061b14030f190c020a02280306150f 61
    0x10011070320f558080b0f0400c0000d56042c0d0010784a0350046412004041d914580350080f200860541d1008201e00819421655410200c40003503000008d0454610894100035044510240e41c41c1c0704140c2406401004540d20f00d5030280c00d030340c900001008558802c1008580c0300002400082c1440b0071903440500707407442ca800032107034000b100500f408041d03100e00c00c0040710051a00f1000040c1403100e088070440c40081c068cc42100e142e4110100c0482009001038000c1d0b5204003141c4540320001c00c0200020140060400020764008001c950128103026403541c041d00b100140c91014034000f40c3c0e070100c050350b240010510104190b1000c00d09131100207440c000d80580008a620b140640040d40c07031182036640a414410441541d500724210802540e9000210455811a0340c9031040c0e0520b010032041826540f0a04000400305459804148206014425144040d20f9036039800028280201402000140a45100c040000c01e2240d00328802e8110007140646005407941c8540c43c841d02c2d50b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 916160944 1250 916159694 916159753
    0x140403060603110d0c1703040b03090d09050f0f0108060a090e030316050414060a0c0507090605120f030708160206030709060f0e060423060706061703030606041502 72
    0x22482001408500d03031454071540011540740390700c04d0050342c410191890a000301c03010010302804403000044100115805055040e134410b03143d2404003411540c4080d44840b03400083c8a086001400782401e604490700450020112803640c0700030801141c03800d800401f0a07174090580c03080007039000c0310f038170501c190a41c0140c040d590324900700c011388450059440d24101044010001084845c2040e590951110b4045494035035610500204581c40d407010074002c2c000b0b018100000801c403260340d10840031501c00382c90044a540a454885485d00f59099214955400403c03085001842d403030010004100c1c800c04110450096401281c45608215a0303e03000c643c62a0062242d42d4000d80721002c146580d10b0a1400c1c017001401148483c010351003041d41401c0349400c00340c16241107000c103502c4208050700326500e032010b9087c21000f41ca000d00c1110145000c4112000300c202c401b10469100c1c00005d040189041d240010b2508003d6401c40740a04502a0703020815020703801c15460075410080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 916162194 1250 916160944 916160951
    0x60e01030204030b13050d0207030203070302120a30050708030c090a090905010c090e1005190801090602070308010f03031b060b040c0e01020f1623100206040309231014040306 77
    0x1780c50f1403840e00b1300c901401015940041020001039400140c1d20041d00d0b4160f500d2007500703811285482c545070403100d0080c40c409010005600c11a00b40440c40781561801804108210850718159941d200b04000900601c9080000504000601d00101207074007028020340001551503181104640c0a0380045a403079450314080380000c1da005010001400881e1584905403c00d02005c400702d5125104650007411302480ca07440762105400d4420060031050700900c658401c91030994029400200200d000c12074003000451400001e2034081c0549905869448160800c5401000c80303944428003120240c1d1640c49410880c0c5841c000c0401c402010780384c071a1441114030001e403d041100f00402c0f2180d014480000900118800c142d00300c404010b440044624020034465402c2500207189404c046072000e0b0402c1d0a90010b140d0384142d001e940d407000d02d82d032a03a001030080d400302e29494843d010b04220f006079515000c800a07203042c02c0c0e03080020b42e0304800c20f0100301580240e40300b541c181740d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 916163444 1250 916162194 916162231
    0x50603091f0b190b070b06031e0c0301050f07020604170702130e0609031603050c0705031f0f1b0f0c1502040806060d030206041b0e0a020309010c020c03030301060e01030204030b 78
    0x1080d00c0791800c0c400f003d1088080b0641801d0007606540605140501341c040405c010130001d460501c0442c0140441041c114804180d0b040e00b00d81e50840c421060b4065131070100018144040d1030b0100d40070b602c01d603000e84607688450b00c64120320411000300c2d42802100700407007230059817540311641e1810680e40003c1500304036403090ba0b00385000180760b16500d8204102e940510003034070703032442046503040c1010750b01d5030783d4500160703c0c01c1050307003103e60140b09e200594032600b04040340202c0440940003003449915416100c64040c1d03084843d411102c10b03004220025018002c0124910100306441e010f2a10507454482681d003a001407402d607804c0743d0014090280800c01d01c0081d52100f4203a80701d0746800f4090381d0003580d8040080c0b000c1c3c541119001c0701c0701640081035903400100202004c0001c40c2c14030243e04402544140d07410752041d071030f22001814060000c21030103116074009000e181180e28205042d01c00d944140e000d541091750810010001882620455006461103034000751040c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 916164694 1250 916163444 916163449
    0x807090819061b1209060b06071b080115050607060f0629030c0702091e04120813020310050709050a0f0f0509090703080a11060412020c060c07050603091f0b 69
    0x5a030b050f031018484503103090410308107030081c40104034600400303000500080c860400c04020f040c40c0905990040c80080e401051240325400e0130b2550f0040c0b101004100c0d5602091342c05c070f581205600b408401002020401e17803801101415025028441c007048481d41101d207841203c1c1c4941014010303807030300801845001240000c05220401d012142032450501c1000d8801a00840748000d2103609810000b81217010501c8000c499245007154800342c508003403405040d0310f460842e081e400502d581001030710440840b6900803c1d1500a00a800041545030000000d808000d107541c050100b03101f4009065107803288000e00030320081000e54030079410156680c41d204040d9000a104000310003e20800c0301c0041089401c480e4090742080c7d441c402c41340b040d14241826485038065004007010407090141171740b1410340d4000c5507403c2c0c80c0d48490349410401540114031030700b00d450b44040750a02290034030500440d00010540201c440c420440c4010031004a03081c012070701031039224121007044d030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 916165944 1250 916164694 916164701
    0x605090f0405161115010506161e0210031802010f020f0f15070905030d03050405010f061509150c2003122502090c1605070906080c030c030c01080709081906 69
    0x2c01100c1c2c00703000418094205c0400000d0103004942c07007288000b4041e5502d03500b40036001075559002a8904401a581d05001440004954203a000e002d4041c02d0b408400c1c400e102d101c4100d550040c0110505e840c5400440d49007440c210703500c0c190b10170402900300305501008240344c844404001800841e031510340690b102c03500035111205015888905011665002c2010382050003145000641a41c0382c0c1440707070140c01004071144030305160607400b00705846200c0c0001e400340b01c60b407a400b4070307150f0b141c281d40301c001c0030600c001e00001d2020301000001503014400481946548412042c0103c0310b10001c0d007007541c4a000c0c2500c02d50b0019441e80c61240c2038942c105265030940140e00303c0f05076900811917440f0000c0c5054a140310020710120080c540403004003800d07410504440c8865101c2c400c4600a103a01d025044091080c0c4100100c0f07403070001081d03442e401000d80505455001c40b401520300800140044050003152000840d106c1c10811002e01a4208084007800442c0e0314103018046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 916167194 1250 916165944 916165967
    0x3022116120c0816020c0a06030e0105150a1206020f0a0314010e010810050712090b0105180c0403030f140a021b040c080106440f010303090605090f040516 68
    0x3014102580e4540c2d85800c02929644211004030700c0c0032403a800e5200300d00f01104030f003107194498481080420400e5040c1d0000d0b0075450f14800801c15a141d55010000c0340007403241241d07022428010600c6800342c541c40006985210f801c0c0541020070055440007150084815000002e076555040103841203130403c20750040c50312400079855541000d06243d00da03c1e16402c80c109181d01c41001ca070082d4482c0703c110003001e00c1c02c0c0302041220311b9407408801c41030f8284101c0d446030300741b4102c3e40c1e51040820041d9000b01d4005076003901d024074640e415203c460f030400703081040c000c801201d000781d09001001007a1084c0c9644c054503000454456900100c1341c030350410340c00b0310310f0604d1403045a600a5a010306480c0507040c00e0820002105020b26444840c4103802c240c103404940300e80d060600702e030b10f4405441881e80a9041965245050f0b940d8100034800600003c0c4040c2040190030300840082c20343c06005040c00789040c59008c0841c055480503030b4603000c030b02e04245215410f203074011402a10b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 916168444 1250 916167194 916167227
    0x9041401110c0c0607031b0309030606170318030312090a03030515060912030f040b19021615030f0c0c03022b05031e13030306090b1003022116 63
    0x40c0b04140d0341035990744140700c0030b450048400041800c1490302500d071005c0f528900d401070281400492078020042c0d5114441114602c0c100b0401045420609802080d07e0004000035814141c0c8515541c010030044100103030140001c11048022411002c3c2030b9205005940c001d100307500c0c05240003021280006e200c2d4030324804840c2820301c1d940c3c2d141e080724032106c001c6450304800d404030a840d90543c0304040c03a006014600003000100900404054440044568000880103400f09026a00d170800c421050700360700780021050202d40011104010f060b009441c000543c0714808000700d044441d0020000040390070450010105541089030480482d1050390714880c00c521200e20b040c03050790150500f41401408800124a0780011900d03403110680c040f951581804c10607500e208454030244144c00180c10142c0108035034a55005030f40340b402e00600080c50700c0f140300304d00304c0094000009109d40707140b104e04151230480840c018036020300100b031003121004a0010000d0904d1161204001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 916169694 1250 916168444 916168447
    0x51c0606021b06030f04020402131e050a1d010b1b030a0302040e0703140114190609030210091404090305091504050a0e01030506070e0a091112092113050904140111 72
    0xc0051078482c4061b042070341550b0140c2c648031805a101e0005a80d0340000f1191200c1342103130700d01e24408107040c1007183d20544580d1040350b2615580c074100c104141c205414280032100400c40c803041c0a00400e8011100d5807132443e505007070707941503085620510900d000250082802e0100802c0072451640101180c2010080080780c03c10450008005201d00c0a651812590306c0c0925110f000c2400a42c990b025074a20f031083e150900507200034003d00059000b0642c0b0306c900c14000d030003040803100741c8102c0c0704001810301a00082202400c0004c000301c04210b428000e40205444190f10400c441ca00d01850b69162402c0c982403000e41d10080c1e00003017059800f200108003184010810a421814910b0000768184001d000325044034074641c0481e144500d02183c0d00c40320342d1900050720161503001001c8419454280109556541d0041865120005007030041407542c01e80c001000d00510030120090300a9484000440d4284112400d69400c01d4403a40025080c3c400c0c800c0c502403001001015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 916170944 1250 916169694 916169701
    0xf06050307120e0102070b010e040507060809062a0a08061f0c020f0a0f030b0a18120c03031112040c09060b18060f0c03070203060907080c01051c0606021b0603 70
    0xd19072500d1095441c1d0b45551141c0030b400c00300080d011111480e0700040d8041055941d150030003100d03082100c00b500c0c18060400b000c211a4803441c52940144c0d85500180a070740c641c3d054130014083d0f450030031003030501140e950300c4c090079680c4058801075071a51114038081c6000c1c410700802c2a0b1003180c4151038200c440c0a510f8007500800c1d111400c68050300c08504040407500030420b411030395040307510034140e607810020801010360003c43c4900d071100424800ca03200403210340021220381d8001801c1d801c00e0b005200740607105249800f0700b14080c3c50045100c5c00740c080409415132000c1400c00281d4803d07010071082c0071084d00020001d1690450401c0368924101a01e180e80c00740d40c0d4003c0401d8001203407246107907501000d48090700034031207903a0740d41d80700c16850036a280d00580c0100e000780140c000282c1c0001010803440126811500544241d1801c40011151a07100c600007803090700da08800f030040c0c185103100e450040d05c19a0020440f82c0030b2504a0814000d5401c201d910880c810000c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 916172194 1250 916170944 916170947
    0xe010503030f090a0b040806090111041505030910020307021506060c0d1107031a01062d1b050d0819020f0901030902120109031e020c0d2a0801060f06050307 69
    0x1100c601d00412410700e9243e211040001c0c2070400c0e19407003114811404500410301c5c0101095180c06030040720000c0098604000001d451406503105881c1001c500c00c035625600c41c0200011540440f0200580d41c4111003c40400103e07081500da00303005902c0b24490004051003004182d4020008541c03e9040c850401035490340c4e40c002e510120100300340c203504104000002c00404000d903070f02c484d452242021100d040138207030200b44a504005085418001121080c0200d003003041000d2403422880c0c161040c40c141d581500005034441c81c1282540141c012503c14400c2151182c03a944c5ca51601c3d017024040e451805900d01e0084039068810080d030050007181004640d8000301c03e01300032409207154000281003c1c0c000a0f40800340d400c100880081581c4900c80300300c4101e009500680c1105400d504036500d141d1008040e4100f02e42d00361510105a0300302c940307010302001c2e000c1030000d518000e00d1110404250b500a40c4030740c0d160f1714244810300300d202c0110003a03c104d181480c114a840701c2d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 916173444 1250 916172194 916172197
    0x15020315030f060a0b03160605090f060c0c0f130906020702010e0102071d181b121605060d2007020f1230040f0509010801050408040e090a020d0f06060e01050303 71
    0xc0c1c01c003000d170b592214403541d80f01800704000c003040790b2201c2d0b41440d1341d91101402a50002e0840d40c4a10341d0000400a14a800e20a50300e020806000900c5034100b40d1b024040c40120b804c130480d034003540d41c41c02124030920350300487e00050300c00c5001584984592001410a4686000c0d007030640d0403078141448070035417640146104020b00e00009140340c8542d030a0040211901c40c1e0503000340254024011706071049110400003078419103a01101d8070000784600c0e2220400c0c9119482011010b0b02045240703442c80140001d04601080058080e00013203000750040608200240000000301c0c0900c15481e01021100c5140ca003170340d2005400402c5001240c842400c0d805031141a00d69044401d10100c192401006910012090590302c546818942810070131a210301441400301c60008114510103005076809580e01c107078010b003010300304120b0004817800242501c810784079204410300540e0b5003c034180c101601512140c104440c45c6e0601a0689000350402d18001c0c00c40e00040205850000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 916174694 1250 916173444 916173451
    0x90b06070b0606190f020f01020a0912110910030c0b2104030c02030d1112040f2304020310081e1f0b0a081e0601060f03020307050715020315030f06 65
    0x54615290b66880c00090150041e6407000d14401d1444100020890f082600d00c0060390640d000c039034151109403ca90b090b8443c00001030000380b080c1c0000c0051800c10304034141071034862000c4081c0c0c01c00410118a0040c030494060b1001c0300c0048041080c4036001411101500601640c60326204260180c807801d0400c41d041007051240410026041c148500b920310520341c0e00a050f2481d16090803002004074007800d01c2c507642400f484d030700081115001c0c0c0446048a506004072540d00e0300e401c243e200c500c0400c40313480c44050244640407555a949100540c402c0e210303c110a6601410081298a486620705400382c5c0303407075071400407540700c40700040a8541400b803401c6522607421108442009c0c0c84c07a2440d02c0d81200000c0000308a031304c070100e88054155418102e00c20030001824a1980d101070a201e50404202c0d45ca11109c1380c80e2203074009660042c0c0f0350815034a803081c6071340e4203081c100041a80503560f50303000c8244417540510401c40d50b60303103504a0041070301c49030781280980c84000c0034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 916175944 1250 916174694 916174703
    0x20a030503060103090b071d0109050f09040305040902030a02070c054212060102061303080a020307110316060b03010b0603010b0c0a150203070e0a031a0736090b0607 73
    0x101c00074003540c2c0300c0d0700060750a83d8081786400140c1041d40700a4203c05403209500103106c103a003101d070100e501c1210b0000c101c1c4e2006040781082c0e1501010701c04043c001610036070420008000109410003540000e5015140e0070500590301c242c3d13410000344004081e009903100714248500340302804c20408511000c50222082e01070b40e00042c11030340180310900c1e09190543e44010449964000356107a1003445064283c0030b88005584085813040070140c03030324008005c01c8009003c2010003800d64080c0d54894100d080459610200051141c41d6400c0300d0449444041070581e1081000020f000d2400d2088050b002400035483d040c000a0b0324ac041401034504c00c2ca00801e004c0c1481c1e20400c880c00605d5080071145440c200703851440310103075008546c22000305034820380010f0607050500072172084941040c041d06000441e40c5007050b5500c000341c01c03401002582846506201010f08080e603504c0484045000c91841e01903c0d2f800c0d140140d8008117655241c848600c1c160340310a0125503050707512 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 916177194 1250 916175944 916175947
    0x331505030a0c030b030706020c090f0421260403120e03040315060302210c0d030e0103050a201c050106050405100516060b040506041b1b0f0c0e1006020a0305 69
    0x10034003c60081c82d01200059040c801c0c0340c0005542c9030007141c0900702c28029212202280e075403400b0141c0c1b201044d140140700c0e1418011445601032440c0c0d0700c2c400d048803498485040340c00b10070200b0303090044d400d0301010141b118051108064100b42c085021658000003401000706910146803680914403001c0c2c2809100b42ca11f461241c070781c0d030052024607801003816500040000031201082d0b038403c0c2c03025103032060f00b1088190b840c20b14580d80c03c1d25416500c030072000b0755180044001c0c0001030035035078031030b5101c801460559100c01c14100c8101c00202d8055250502d000c05158104200e40d100c9104500d042c00600245034480115000d80b20300365688c442e46c11110004071858030809100e01034051030304200c40d0400615802030840058125000e00031a2140c10070002210070010701c4260107807108501c012458011407031500d0100c0740b14014051904c1c2c2e41c5524001c6484100d08480070040048203002d00d20300148a1904004450340b0020310130304081019545003140800a82030080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 916178444 1250 916177194 916177211
    0x150f0301060b031005010f02030c060105011413060f02100e070e2e0f150918020405090f040203062203080a0f0912140c10020904331505030a 62
    0x40035085000140144080b8680d41d244c0341880c0d0380440040d004490018112907c0310003140c3c03002080d5210341024034081c0805910b03003801911820500c05804035031220074013265500d00c211416400040c1000d44840b8541740172510001d0520404180000c1640d00d010a6401d0b84100081c032401134039032030319070140c198685510001a003a90f142040800d20305030b4a0300151001c0c040c0d07100b42252200300354004a25110009120400110090240001d900780301c1004014287c0f680d50480301062107006242c1a00d46c03010400011045600303007801201d82c02400708604040003203c0d44403043c0074040e401c17502844084c600c1c000340860048d040103440004a40201b5032540414501019003a04211310140381c42e00082c1034905284150210f201800004048080c41c8100c0d043c051041d800f40406280b84880ba0380250000a0300d107400507544d030343e01c1c1c1074849030140940d20481c0003005000c8204081810f60341810064115041a101b0001070307141080e08441565041070004c0c00101d480c07803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 916179694 1250 916178444 916178449
    0x3210504031403070c030503091003062301110a03050306031b0303070f02011b030f0e0f012016080303012408040303090f0204050c04050f06040b07120e03010f140a05150f 75
    0x50744130240000002000001c10004000700070f0600136030941c1c00300a001c1d4a186d0507001c40e0380511038006503c0d00480b401020580842428503680c0d41418141e1040d85ca94200c00c0c500001d425080300480c800106010711032034204030814003003c0401004001c2012000441d890f0b004440c0d000302940c08c400300d00811607018400044444124102c40d8140202900b00209029410700e200c0d4041407004484441c54207001c20001846031040c0c4030f00c0c62a000c100d24411000c54140b9614110703001e10100d221312540107081e14401046880300442d1654142401d0362551501d45001c001048030f01200071007040e401c03095603039000d5054180001c205049007800c1c6400c0070041c00082d4000d180c2810030400d5101c000103402a1282562400000030414003403103142d100383e0141e02203500d0f09200041c0061158011006501c0443c944050b000c10a000400d082d40c0c0c40741c018800513503c449511074100000300d032650740f001000c01d00388854206840d1992504600124060140c1c00c0030f00b000d011074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 916180944 1250 916179694 916179697
    0xf03150c1e09010c080d4d190210060605041e060c0803090a0209090708010b0a0b032a0a030b04180f1103010908030a060501020606190510090b030405010603210504031403 75
    0x40b07400400225602020801c051f080310b0503441f0304917500d00186107100d886850444075103c1c21203491503291500e04100a0014846103203500c1760114800c0d802005103c150070301503038004001c82c2c0c41c5e4940300c50400401080c0300b40002022409d464080e80c042203069032003400390b82c4443e040950103680313889640d0183d0030030001210180d0041c00b80c10038048039840c0016010121171050707008029400c02c078400c005008046101e00100b128042c4041003413070b850341250040522101e140e4031b00b184081015035400b070b00306103002c1340401d94894400c2c419040074081c4190010010303042140e0007130706644000c070040800d1030181044002e030741c040c60f8a0303c0035808003100e41d4200803044d4491600410b41c1d805414a8000e03035005004040c0811003030b04081540c21000306d00c0525941807542800c1c03d019074444442c0851003003140d1080001840c002540003076006a00500000c95894118105400c88244181402d50103100040e50340200907441402c0c1d42c01d80b548111101507400400c44264910b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 916182194 1250 916180944 916180961
    0x6090a02040b062505010c0e03030d0b041d070801060f05100c060f060801020d0c03110a0c05070302090106180b0a0e01030b060702101d060702010e0f03150c1e09010c080d 75
    0x5803002813410105085515602160b018400d00c0244415046c40c0e100b102c01e01c4503468002d4040e40107100c2d022400c49160401c4809103c05040090301c011104d414480440c60b0440106544e0018001842201020300500f00944410010702d0300346071400d000302d81c0b61b030210100302d000c00000ca413001040085980081c2d080800d455070920545444841c1103000307501c4207684103019840c1c0800c1d070810b070b8024040c0100b82510000024180001c035041658819550303041180c550103400f40200c0169250307000e25020780510b650756001e02a0100c4001302c444002d1b004004005420301c841c10040d039008200302d090304030a180200d60000c4000201e903041c0901200203502542c0302180001180d44640c449a4242c20148012610a80b510600026108100010b07000440800744c50000b4100712800800103100581140d00d1004600c824041c0e280d000c0c2d50a0000324000aa03c05059488200b50711015450705c904524000c0703402d00203440358041c00f100402298011500f800c0c1e881850340f00c5480d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 916183444 1250 916182194 916182217
    0x100e010b070605190f061e06090509071413091a06030c0a0201180501021c05130b0606070f0b01050a0602060c1608040306050103080306130203190209060c19060c0206090a02040b06 79
    0x2d1550901e06002a0540c2e003d0781c11f080d00c0172400c12400300440d03400d00c401c407012902c1c0d29009034180010302c04014002401c02c41401008030303280700c00800d454010540c04010706480d984040c200010320042e22460a1420580f02100a81d100665218801c894105031484640350b62000a40c41c280d0240c81c400101d8100d02040746903450034880190014081440c40c0300010041340d644000c81d104890040d5841312422400090000029001d1b03460720750829001822641089a0345d0389083c41220f60000458003504c0c580d004000a0070030700588c102070810f0340060102c1e0300c0d10401818a6000d1500008500408401d01400f4003110f401220061034100c0000d01c103960312030a00b14542d03802910380c20302950814181c10060442442520b01038041c06240c001107800c00c030204406500400f403500e500c10070401142e8a03101041100c4001a80140d551601910075802d01d1021610403006540139500702c50200011424040f50300107030b146e0f04032000289800c0b10000310b40e1900a4038207109 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 916184694 1250 916183444 916183451
    0xa0b0a080601031e050c04020a200a0b0105030a08030439050a05120c0f010e10122714011e0e0f07141201020f040608100e010b07060519 60
    0x140010001c19101c2c1a280900100c0d1282540c040d8442c00c501100303000074140c1c0d00030a0020b1680d182c00e4004014146c0b407440c2030044e00c004c105003240706028007440c0c2966a80300d9550081040b81d408401d50043c5000c8001d030000e80042d4440070700e41c0c400200300820503c040200305c0014140d411200c03091480b9400a111000c009102002050305039008aa1040c007003c2d800242a28180d020394100222510141186c003001d0007c1c080c1c0c007120541154148076214400f1400381e295003440081541c001e0351408209551401040b01f19050115107030410303585c0089a144400d00c6442041c11680d11a003c00724101641a006004003c02008030a03040144c03146142285081d4101010442c2c10605030b80c1e1412041030415500c030141d00c1000d88665000c682004ca0349040c4c410401d4002c4020b0015141402580c0f407401994019040307500842c103c11b00b48034045240d44240b0014155044d030b90710301941010b14007100c5014410700108416101c2002030400405400c154108a00040b800d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 916185944 1250 916184694 916184699
    0x90a050303102103090b09030f120d05062e02150a0506120105090705150c0d05070b0a0c090e04030c0b07120e1207140a150b0f030309180a0b0a 63
    0x142803010b034601c245485040b102c0f44036182e0011444040c41c225500d521076580c3d05150100410b043c1d007000c01401e170b05001c1c0390710028100809215440842c0c0d00b14502690381e1110910140884502138041313802515170f6558464003503c031585590100200740d55940c3c22401446c022480c1804100e0605124500c000034007201e0340b200e41040740182d2007102c543c00a44000c1d03000500301c4000f100d00780c01540c8800c10821040c140074a00845880d01e29141c00d1922a2030300724985482d0181907041e001a40c0000e41d401403018016507036801942e0031a06100c9082003050007030608000703004800b8140304c060040303800c16000b40782440c0c403958800d082c89041d10b84118060450f100d400a000c0d0309034100744030000c02030f401150052503900304c07090250400c2c41c2038458100101001c0b1320b80090744503161030f0b4004901800702d03168844008200115010a0481c1400314604c2c2d0b550001380680d0091210c5045a0b85010303417005110011903076514140c0d101c141010242601060040d00304c2c0038803902 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 916187050 1106 916185944 916185961
    0x209010e070504030c0806010816060207140103090203010c030c110721140312090c0a0b03060d02060405060406020105090106151407060605270a05060f040203090a050303 75
    0x82c81c24a83c59039950980040c040e04a0882a8404801040444c504006111412815406050b0741e40c0c6000406559030710f550241e020707000b0070241d0040310350344a548142c4500350010000c2c404040d10312405002031210044880000703074218010130b640b4100044180c00c035102601980d22044114800700f44841130040c0445c2c0d80d4004081030000444200060100b02086c51104031072070400030020380ca450740401920340141c820302c8040103405201410f1301e41c060416501c031a0810814030000342607201d2a00000e41c4600e001c170740031a01560540c00a0322030740e6400000c0100700c0d16100a090141e0101c42071000141404440400c01c005d00c401500380c86114076004140c558586000032005e00640690702c0b42c0b80320340049844148210002190040050701081140f0709040010981b03440c01100c040d401a500040030a00c1143d0401c0190800b80c1c0040650340c680c01d24008 = true := by decide +kernel

theorem cover : BRFrame.Cov 916007194 916187050 := by
  have h0 := BRFrame.cov_init 916007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 916007194 ≤ n) (h2 : n < 916187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
