-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2612
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:13:27.842494+00:00
-- url     : https://prove2.me/submissions/f77ffc4f-4e66-43ae-a738-c26dbc9460d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 469604316 ≤ n < 469784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 469605566 1250 469604316 469604341
    0xb030603010e010203040c1202150705010f0e030f12061203070b01140102160b0a120c030f1404030504030f080c0303040b070f0305072c0907050a020f0604021807120507030203 77
    0x20b10080c41644103005000008501d00070650850b1180d1650f914924403c1c0000b9000b4070340000030310b001c0e180016450f020400c042d08801d20049000900b002032090b202c034a50b07120b00c5010004034a040080103490b02041c841020f46403c44006814a5144100e0b80d003c0d03451540071303c6085d110328036090010468503860000b01c038526417080c07010303184200d840c5c0884c0700302030024042e00c061550f021842115072403240d80380d008a040445400e0080d40040d10000c1c4c0100441000d40d8040c078201000b10701c0c940204010903004e140e06079109460301c4d1030360b194100300c203010301001c41d40c40c0d1007000710301e5089004001850056004210301046402e0030000908840c5411803103c05042c10039040008840e08908011200c07481d8090706e10110410f00b0390302070710200ea4005c4c0d59111308902c090014040c0e0200180c95440010b0b0205c5004807030ba030700c80507074480701150000e5201e0b407043d09110342105200740183c0c004245040c00c415003011b548048045d00d10880c0d2660010382d001c01000318464800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 469606816 1250 469605566 469605581
    0x1060f050f2d040b07080c0a0b040308070219110603060307031b0e060909071502010605031203010503070b190c11040203070e09100614090307051017060603012904050a0b03060301 79
    0x940303103800e24200b44018517006009020303000c05000f04c1c0707103445a9005d100310100b00394400d031510725500d01460090401c81c0103a070048014070601c480813002c0405c200083d03c0b4070341c10003840da800d40c003003004000c4550300040800340c2502854400000141104003105003040380403001d5186181080300307020060000402c0e1510820b5a1001d01515150109099098031880070206c04402010303c0164090441580103035098461400c600000d0941d29018605036002103080e50025640c50000c8080f40c0545460302d112a100c441020b00640d0240b000d5207a110f00c03505240c00404408030001d41280c0084640e82d0100d507184280040d6403a0404406600500e410b50040e482414403500174038010404480001d0309078001401482650100841d4006110041ca2040745082c4124000d00416a1084484013409030602007540ca02c1c000301503074142c070400d111081c055549154220714280c0684079400746c1420800000c00c8980302c1c04008809892554103c076641d00b0324a05050868029 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 469608066 1250 469606816 469606897
    0xc0303030a0533040b0a080d0e030c01020604050d080403120606020a0528081b0a0f0b0112030c020103020d0b090a0603050f0307210908100e160e01060f050f 69
    0x183c100404500402080e14054140a42e400203078a1280c42c0070414901c0d45400c0381c216407040c0c0020000c520750154481c40344003015130580d00700e114100010799540b141034030024640e8200d10403082d5020701c13440d02917910078004c1c5018075140c440440240100c1c0c170180c00030f07401a04800754003c1844010002070701d036001078520103035003968400c101012913414800024444000003404020440700d0301c502d914807518100039207d5030344580c80e00321401108884102c60b04941d01c1c000059203120311050450660f0551a00c12202c1c10f00e42c01100258443c440c01003009a0350402d0b40403c1e101c01007464810702c40000c00041060860030800e00c1c180101e2845021030b0304c00c001c02c0d80080c2d0183c41d15941008026140070590080c120150760094090700a0000c0d4131a104000100f48840d070408160003110b58252140d10504070340c1c0c16000c1006009042c4642818001042001e115142d0828000c0844c0380c40c5042204904003014203500040000840c9614100161076441d055090400d0a024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 469609316 1250 469608066 469608121
    0x91011190312090311010f0c080c130902030c131523041a0d0f05010e06011704080c0a081605060c0319051e1f080d08180c0303030a05 59
    0x605541c02030210580458000c500b645400b00482014064001c1600c02c0e61220000c5c000c21100a1041700103143c90b40300480000d184002007011041c0090498404060290000400324104508135010354005007052141c050208040c81c40300103070481c2080039103031402d84c0b1510581c01c0070008049102100440200c030400803034400c1403001d0324048a040b0340c1c087c54095030100c141c80090b00030740525054140001e0070141d401d9810320496110768160b80c1c002050030b61644405c001110302412003485903d8582424020401040030540580960900e030300c100c60f2900015a111240c6401c81d180450001100c80d803e4001c2180600c591a40b01041000141c1545060000034050403150300c4c05c001c0d45d941e141c01151b910901440411010010103c0d0022982007200c0c0b2412800b02c000078200740e1040b460340100d070f0f5502c003041e4111000d81d60f695003082929100030402065a04c030b03070703e0441ca03c030791034691040362001e00181d4420004a400040c481c45c1c0000c00b140d01201c6c403075540001c3c0c0d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 469610566 1250 469609316 469609363
    0xa03020a02010311040e19110408240c07110a1502010509150f010e0405011104060f021b010518060d05090d1812080c0c040e0304061d0f090408091011 66
    0x448103481c1c268000340d0030030117071f40801c4010707403030703402081c00100c880c140010014020494600c0024946036000412051144002c00c1c1c41624a01038000d807042c0d4510f49040001c80b0101d600704042d0049880020044c40445e5658404d10003640391500400000d40d440d48100008504240203003001e500203800c60001d1481c00c8002003504003014091030b107030004c540000c00c0c148034095018080703401c034003186203984544545015100300042d031500d0b00144aa8100d003001d0395020040c80c00304d07810684a060400c54810001c840b85103100b201c0c00e4011400380720515207080309015860084a084015010341d030200035004142e4812406034074400e4440d00810440c0308810036690140c2e80d0030541c55a1120580e0200c10b045c20f2001d505e40750b00a080c544600ba0201c0c000c00100201c1c0ca9549801d4000301081c0d02c00c0b65480c4081c03208a500c0741e460092a441d505164a5a680c09403044909601e0000c9000001c1c004007112206000092880f20403803c0e42c040c100000030b555850458440307001e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 469611816 1250 469610566 469610579
    0x3041d0a1a09070c0c060c120f0206010506070807060f0605120601060509042c060a0c020c03031204051e0105240d060c050c1203070311040807091a030a03020a0201031104 75
    0x1695000c558040c80c00c2c90300141c03038240b00e49000c8452640c0300700109600c50351038400a1401d4000342c010382d642c860348a80480740d01d000e080c0702401c1e00c00a4020b40641d0707182c0b40800c0450703007010b0350070384085004010710710000d402841a540c0c1c145641e1000212281064144204101404000c103000d9114400603c11140c00005503180181d084a020840068043c44030480c0040581d0250b201c2042c14212180c2080c0855810b200300308140b0208071215070711200700d035100c0c0006031003a055041007055180d020000e400c0e5551140c010012503003d00305540300303802e10a0700041403140c240d6441c0709100941c1a9000a8140b0b8400e00706010990000000064820301c91460000d00f40c541c0c80c0000c4605601840683d20b911014a041d80c0d41202c041c800c1c0d0082d903000f11407800000e4500304a02c03480704180000d407810b075901c2c103009042c2281481100c0700100340c1e0448501e0030106142406a02d56020402241040c5c0b0030b038050056110740b4030000d4143c0b00d0a00c00004207900501092220 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 469613066 1250 469611816 469611851
    0x120903160b0a1124040606050d0302010506040b03010603031b0519030903030f300f09060e06010605040305101808190e0a151b0803071d06120105041d03041d0a 70
    0x82020308807480c03540d40c035a4a03003800100990380c0125027010152130311109041c0c040d8080c0380706d9030b0240c0d000e10489029400305401c9503c00c0c007000300480c0c15540b20303c40640c514078149a240c0c2c40350040b10303d07022405421001c85140b1440403400203690a00a2040660003224411581c060741040028045084402852107082014180c0801c1c040204135983e17860f02c0c2c01c0214260701c0035204120090f071a0034048064400100c00ba81203118403000000c40d184240d00f15030071260032401a10301001c190240c0c0d4060b0011691242c0c1c08a5005103507400b203180c52005007200300500c66005010804014090328810f01e4110051003007080c804204540b423003149402042007500d28040385608a6940940004141c00c040a0b2401c90003008204100381c01403125001c10221807000100c4070100d1040041d1442005145142044c100f0010000d81c107158201a001d0714144d540010204090a003035443c5400c9075004805a50955184406000030310003a80d4202c0c1704800b0901001c1c0305034040e81c58 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 469614316 1250 469613066 469613113
    0x60b071a0105061b010b27060a12080c15070f081006021207080f03090705010908030702012c030604060f0c030213030215040e0703050a110a02120903160b0a11 70
    0x2190040c3c05500d0104c00003035100c03010142d80108040380402070000d00030b00040e540110444440483c00c003140441c50140c101c00108d416110300301c0c1d031540e01d83d9900d40380d6070060462100d6511401228510001401488a118a41e42e54501041081c0c590008040071006030a121b00c0c03a1510b00107222040d4082a00e01c072940300d12117000d0303440c02d080c80c1000c0305102d0f602071414500340100c2404907101c4c001c959a0300b162001d9a95249180d242c000300364692045400080c00b042c43c0c1150715511103101c03062602d15820004812040e0300d10400480d051080071901103035640e6a40034484d00d50103551140000b00700c1c61349000c604291429000c100d0707141c203900000e4490780140481e0b900c044690000c88028003a05d035000030701424858006009000b06031407400341d9a051660004402032060181c488104840d402040d0810717400480f140700754807040d1265010f0040000415001c50814401401854107044841d5115a262402829845115503c64580d00015070110030407042c01c11003d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 469615566 1250 469614316 469614337
    0xb01050409030c140312010f05122b03060801020304420506120a0602040609140303030a0c0e1905030c0102120a11010b040e1614010f051309060b071a010506 69
    0x541c41311502000e203146000d0f01502c0b41c0603c02100000c0341d107220402e451411100141c8945c0d0740b40884000443d00c1e1f1006000075880100348106409142c0445540c40710030104506000400da40c80c3c9180030300703a9008440039554030180c9001540c0c3d00540c0c624100c0b42e49501140748440038a10081e0540c0400b02c5503205007950381340c5002c24102e6507049030481700c100c05041100d10980e5203260810203900b0078401c04c00402c48058000a80d01c2a09150110b0004024040d51070755076000a44001031141c4907180d0f00300315040301409240e8680344800c520500a000b50344480314a06000c0610b040780d84441e140c11500045040100907003844203681c10715641d428000e400300d4413001200c1c010101e082c442907010342002c44041c4805404505698841000306104100580318800d115180d4010078200c2d002440c01224040018130a0740075080e285000c200c207558003079481500c0c809480442c0c0100301c580c0c1700050303d00d0800c5080061010024541800600113615000000720720780285200781 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 469616816 1250 469615566 469615583
    0x503030319021b03030f040b0105040c0504121b080c1c03050304030f1e050a03051005010e0618060f09031603120e04150e090d03090209040303021309020a03090b01050409030c 77
    0x7412151542c1c3c5510302c48181d84001c9030788a180c00314144040013803e445c20380e6040080e02c002304013400d01d4011000c5940c1c068a559141600e01200d5144800340700c401907070b01c41e102d103064040601200d0000d03401842170300c0c0101481c0402108001050801e01201a030b012414072483c40060b8000c020340b03902c51b401d805c4c100102d14080d1415204084411480404074910182903880507411601070400030443d507030100080d0351003050b011558407180c02150302041565030806900d20707100c001031030818050103004210002d10000302d45140c00c61041003042c0c0101045183c05801d0030800e81b0040112985101a03642c82d50b1162000c18840080c48e100300104d8010250305500d454210201c201003c00740d1140851707440050065400c41070f139a00c18540642c20701d0144980c42402800d045640003090801240c6a039502a0000d501424003100090305400001401c40604d02c0238120480c1e0710380300420700410700c3c6004c45840c40c05820440c8101d1070804940c0110354000c5402c041d260740300804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 469618066 1250 469616816 469616827
    0x30204020705031e03010e070c0213051909080904140f16032703140a14090d0c151407080a0f2c04150501021b04060e010308090a050303031902 63
    0x8604620800c1942d13031101103441c0300c0c0f02090700d0030b400641c1241d241c04c500315556100d0b02c0040f20381200d04000a5403000240b4200164994107038490b039000300648100c0300440300308000d4482500c1072000240c402c2400450440c1407401c190285a8644801000b512064038008010450450000d803103171b00b800f0101d0401c0c1001d140a07600c890711000d0003001007a825060125441e02105000100702c002a12894910b85020422800d41d8070348111a120a420020042040c0c4210b80120704c400364000e000f1b0601501044120a101020340444d04001036400000320000c0c0503000d4170303904055000b0b0b0410a84001c91011419280c0003861031800b2800044522022258100c0e445841120102900066054071036002c1e0300c11100345083d6814003005003d21000604480d4904c28240541c200c40841c0061401c03041402080840040000580075160f08160302e000742c1c03d810031980101c0c001429001803814284a03802088114011840c5103041103c9040800740d8410300982540c000c00c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 469619316 1250 469618066 469618073
    0x903060c0201110c06060315071d0a0b0f0a0f0f0503041506080601120314030106020a0209040f06020d0608100605060904021b0102070f21021e101a0411130302040207 73
    0xd00864050b503c100c603200d402d41409144c4401e000d4410324800d01c80c059040f28010034841f1124402d2030350342c803000d03005200c41c5140b04c00d0840c4441219403104020502258000c0d01001900c0c0c1040d603400c44070b0300c40568000241001190305891f4051180700000c010403958404d08880e800b680c44408514500002c01d04000606419084400c0d540103081c000f02e0043c4943c08000c10b0345000c0e50711950456094940000c1c0e510003800b5681c0141c100384d03505000b504081003541e03003061007000c018031003200301d8942d18120f802c408800303074046845050400101c2c03400c010001e00c0e0200c404040012901e0320380040d03414492404010b00031500860b401c403c0b400f621720241c03a4058054005d540d65811464007a0b94064241000c454006420b44c000c4c0061100110004004085c3e4006015820015203440c2061000700c0b0504014800c1c40c91aa01030b1056018854002070151801144244000d0030001070b42c40c565100144440103003c046001c1035405078150840390140c80040c4d5075401ca05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 469620566 1250 469619316 469619321
    0xc0512040308070638010201060f080a0623150a3c0302030f010606080f0903030402011b021e01110d0507020607022403010807060c05032218051806070903060c0201 72
    0x141001c2c0109101c0249a40303c1600f81c403001d0001704240e000b0415291110301c8101307080400e000d0316985501c00d664030000648281c0c800c6c154410350050750100303001e4402c2c4000703401c1005c862030803055001d00c141c960309040c08600603000e011500c40ca401c10140c00101500b0b220400000581100105281601c0c4007074101001000b8680180949071050240e888250181490340329620000d07100000080d50039000d0039140d802800d001002d10b1a41d2a142c00442d0342c18071032581010b44011074403840c801680c60310504289000d0007214042c0f40c040940c0050258101c041101c44031340c110b80e0005807482e910a08440c038032541260402c2d1109141d0011882c20038074903060890150043d60340001f141c5007080030358100c404490403200c45580340e001c12185808440340042280d407003400b100003800003446211885c20556000306815541d41c006200c0b000590820076005280e83d4801e01074050307a840f00300712100341840c004114034101440010540001840060900c640c0c0b504022401807007074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 469621816 1250 469620566 469620611
    0x5070f030f0b0133120e062202130b01120212091c09060c0f0b1003120306030c0e0a140a0e0105101a0c0304050a1403010c0f0801090c05040302030d0c05120403080706 73
    0x20801001b903d20017408140d07462109440605200904a0079502c0b5010f50003000c0e10300d00c1c0d028101c2c1410010001c400000341103c0307080715040c862a12002c2c041421148054007402d1841207100841c0d050415101d8248100303101c0701034884010680e00c3c107000e03810110030380c11507445207810711708003545041004e401c2c091000300400b400680700038491101c0115034400140e0f1300400e072480c510400c1e101c054084070403900c00241004060380003007044603a0780c450b640d03101c600e20b540410300700002c00011180c00c0089603407520280d031303d00010510b41001d2041c5076224040b921010001818002c0c004128519051074250142e00001d2042d00251700748181c2e001090041c101986caa6150030809030350320401000308d0f00030742c600042c1c1c96406200300b001908601054aa555242c0d0a04050070081c03c100b84884060101c108000001a1410080014404156510402000201d140003420207200e90300388840c0c19000c0c8424400301d003540e01102e04070360b0f03c80e5000801c910f201c019204c0c4000b40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 469623066 1250 469621816 469621847
    0x10b0c0118050a0326010515070203010903120b0603090c120a0b0412120203060a51020d14030601300b0103020c1905070f030f0b0133 59
    0x1c00c44420100800000c0c0d45491520a46035000d1503410f14001042084c2d100159840f181d000800400940c1041c01040103900e848002080c41d1020706c3e00030900707440e00d48600301d0004201d60352002c8159511b120340c3d1464002200c880d03180d4280100600c0d0303140c0c0c910800074807482100c0300d18000401d00700312020105a02480d0a000c500d018203010319003a00401071000403410540510315542054800c481c407440c00100441d0f41503091101001150f580110700403c022203540001c00306034118101c8110361411320540b000d800c024042510003101c60030b49800c007954400e201440741c194001d13138000003903441c000b10b803a1207981d0200102e03000d640034440500da0307001c0b10740c0e40622040160507900b840024200e091042400d0500114100d1242806420302034101d0f82e42e5000640180700f038421500d0060044956164559112080d410210340c0121242040807181c082004441d0301854010000014031000c1000c2d0110149004104010b0407a42141100c0c42964160302811500544540 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 469624316 1250 469623066 469623101
    0xf0c070b071d10020d0f0201110c030405040b0109030507140d020402041e0f060c080d0219050706050108010501060c0206090d060c030207060e03210a090f0c060305060409020603010b0c01 82
    0x24044006040100c0001d0b841c40700e00000781200307407941881c0c80420002c003041d42c000c102c581d09500080312503000c2c215412013195224a0a180326200d401c01030308480380d01801030741d540c07071500341000219410041d07d1070500c030403c00100041500440d00c54211445191b0525042c0400c000050a0000070b04009501a01c00f05021810000c1c4401242003251a0400b6054403a11002400e011000718868540040c42e0310550030001403410700504107000c0514400350911803482d5101c8900e03080e01d0a278100207040480d80703070140401da01645006010403c001c00c11941020001055421010401390040700001480080c83d202c1802d00806581c205004025500700484024040c1d4408001625120308005003140003600100442d00c1021885600010f414038540008003218002884041090750350b2102c1e0011a0346000e00480762445101c2c412011800c1000140c112140030b045503020790328107008100107840b20002c59056804d0391000d15110410340d03482901400004079003e44055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 469625566 1250 469624316 469624321
    0x506190f020a050d0b03121804060f08030a120e120703050d0f060f06090b12180a120f05031003080919090209030607020312040f0c032004050109140f0c070b 69
    0x250b2050150000c4d2403059030500c49441c2d400c04060707a0700d00c0311040c08110341e01001801344100e075440d040200880050310101e80666626020000f00c0c9640c0d20400450300002a20080d840d0701c0f044104881c40783d00350800100b000c001c0020307514150604402001c02001500c5001c0c0b40c0180c00b0b4503620b4181c1003043c8032181c8080e2901c40640300c1c510400300c5000c1206008105240100c4400054030f202408043c1014025681e1100c1210003070f00e840000c50080324034094200c81800051101806075404200c52103402ca0000c00f0006003c170180108007042c002c3c44074811600041d442225000805141c80d0651840080e08400074a4070400ca00070180c0c10001d420303000354002d000c6043c8101c0c191000c680c1e03a101d00b039072248503650004038441040c00001b000101c11042c0b22951500612245441039126603582c1341480c0704040e20f4142124107184040306241030b000382d0740508540c04080c03214504c4c162410740c20030b801402c07002003644540f000515001001040c0c401c5c480d00600c4c04035450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 469626816 1250 469625566 469625587
    0x4060609021c0c0f171003050a1a100e070c051218190f0b0a09051002010b0907050405150d1b11070509040b1321020708070905040506190f02 62
    0x84001d1041d0b0800c050800650f08000d42c068110980c101e481034a0b804510200540c018a407100014100300007070035420300100203d241007000180b0b2602c180040d01841880440301d0200d42e10040101d80d03141003101e8103000819003560f10a4201400b4281000e0000740307403600750304054400c99101903000020030612075403006003040400e0392005440724008030f408076840003000e150500a44820100c1108100809034103940100300c00342d51450075041d04d9440707800084070110040030030f8005139180da10760744040c90503a03025504010582481782c078082c40c2402040202c0c42103a8050400750f401710b41806c1480d4590855030402c1a001400c49050038072500c05054003e4800380e60304144528140071815040c2400494080da03005008103104d640c49290b000421501d05004581c06260380101c0c4013441401d0f1011001003041e40c02a0401a08110626151940560024141c0e0b0f00346000d00001c20000700d0f601e41c004020b0301100c0031607a0140209809002c2404600190307274400100d60106 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 469628066 1250 469626816 469626847
    0xc1109190903022e24060f030204050901090906051015030b1804080a020609032b1e0204080c0d211809060509090114060f011206030506070e030a12080406060902 71
    0xc001daa401001125484103030540c085e010007220200c0406400000d01a150180c003803d04842024a0058a030a80b510003182d5070010a82c00034182540f91f01030841004413070b0145d075078022842c3c50700420544c41c020101010201c0c02c51442c0030325075219040440c41e11130041c00b410035010840344801d9810146040340c003a41c881041c4000600603003000c500e42420200899809445402c02c00411440903203140c03001042012a0008080e5a484060b480d400d0f5094a4030303020f0381ca40360051b03e803480c01444500740340c00c156040f031060201c40c0a11000501440004244082440c0c4650311b809001340d0603a0200e403e8001c0070140080c540000605001d2500f040c1c095450542e1040441d0725810486401d07a401110001c0b07090001034001403850521140315010b000051402c5180946601d4400c81128026002528660422410000381d03513040440d8412280054009040c60760a030740f580342c40750b89402940c0c403c1112402c0440c0030b01c805a00008054195103000b10360f02c41c806031541c0c98 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 469629316 1250 469628066 469628143
    0x3230d050c0921030a120e06040f170708030a0e030714010b0f012d050f0c010e0c060c0601180212150108010503010615120f09030c110919090302 64
    0x300c0d1100311407060f01403110512481001512200543c20410b0184050310083e01d03004d10b110300a03a550302860850001040858001da00130001d040701c1500c10b00f4022144500d030070300c0360607001c8100070440018180500300ca9009402c460002414154407410500b58442c0d4100075194803001c1c1204140e08a0640c0018404501180c0e400810112400152009110b00c80500b80c04805107a018154004540402c00171802e245826803030f00341c2120320010a038000203140c2e207080c0c0d0349112810007050200160142e5202c101c5966040003034034a900789d03503a50140a508095020a403804564010035010b0303810009440100c10440c1c40e0481100c9035440220302c0d0140000c48403000003525003010720410060344e40d00319030b80c030841030201070079101010070303c00342c0c80140c4e607422a0f401241801d22510f05d5640c400d0781e80380300111482c200340d0400824178514074030800300c0d5002d0107103000c2c2c2c0506000350b10001c140003055428050406034140600720100200102d000190718600c1c440d14040106e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 469630566 1250 469629316 469629319
    0x10c1a040b0a1a0d060906090b1603060503030c0a02060a03060f0b31140d020306040305190905010203120403050720131802010c02031e0606180403230d050c09 70
    0x1c90b82c0b181800140c1c42510f0000c10741080f040312407800403a01c96004510303802d0280c00d02165440d015919486200d104645120390701038407034a030b03440c500da140c0070301001450120001c50500d9140d18209803540520a0028481c0750b0000300c1c1062140a60014001840005804503d031030340c811201078240d200d0300c015030800840200c941741c128110061815000d2a4401c94200b8900308110800c95080340d540e202e03400a84840da9500596003041914825807003541c0f07240d1640083d0f5000c42c00d444030a9420018810310500034801a640003003941e45074500c1070f40b0a10b040d00c40b403d0a440910a400b809440c407002903d1054143c44442000c0d03031120300030795030748880080011004084941c0300104007002010200d03100c02661060500600301c0740002c0903544a058181a403405640349a80b403c0c2c2c0d82d401074801c12407645044081c0342d5005d41101060b0a00d49000c0d03400426208609200850648042c4041d120042001081e107005c20b000c210108031071704110704075103400e800414425 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 469631816 1250 469630566 469630571
    0x109050103051e0a020405120a021503040f080310090f0b0a051c02040203060102190302071a040819060e0d17010b0f040b0901180e042609010c1a040b0a 67
    0x18a5486482614072501c03504441ca085541035141c0c81d0705804019200a80f003640038071000c2450342d5031600c2c4045104d002c030700a100b2040c03140b0610860340301e4031030748020f152821f208005c0820140c400b0234071580e42c0301c05115540d5480424070060300e85550000c0082a1070500294003070b01c2c882d44042d04803001215850741c0c0560b20401c10408420000c401d0380c0148581c90b501c001804c154015540102341401600d01e000c0500205945440c0507410039001070707000580420044100058110004501110f440e02c2c0c00d00f002a000d0351008000603910469448001540038815140c0c800361194804100ba1f40d401110000010280c5032004041d403d002204000000c1d40200c030411185900a120500d9080c98544400011240c01c061140c034140a10700e0345050880340d4251181002e041080c59000e503900f0542048070004a0840c1000b424014220340c15205500a0003500c0c201e14003440c00c040c041c0a00c0c5020180205e40001d0382140201c40d0302440300300800720304400c0c8283c1c2c61401c05c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 469633066 1250 469631816 469631819
    0x1020114011805010f060212030c07170a110d080f09100c0905010924080406060302220b0a080615011103190f051c0509150702010b010314090303060402031009060b090109 75
    0x5c1ea0b14001c0348640c40240c0d00150f2210b001196180181d5804002487c3d02400c2140f030ba01c50100700c0d0015041c4505002000404111441c0c1002c641c2d080d040346072008125035111080c002e40304207800742c000c0284071003050001d60459410000003c240700040424042d1001107103003e05030340c6580c081e0754040b030303041400480c02000e1640016010001041c804201e0a441c942c2551902c201030010f83e003075620340344040013584071807004501c0301c1a5134441203034915a40b40c0a0741106c103131800c11881030918000401c5280c070001003042d040490220741ca100c014210006a5800b407121038101414080801c9800ca150303d08150032011440d83e48603410000c400a404507034074400c4e944401c01d04100308038040d0204215074002540201d0704030444a16094494070082016400c80d5000010f13911358085485070b581c1402054501080d165400c515030400445081d00e9000080c800c0d80501d42c04400959460006a05c0c14010b00001c2d804015a40c0c03505021520342d4881e003030103030108049550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 469634316 1250 469633066 469633079
    0x140a050f01110f07230109030206220b04110609180f0c04060503070e010c0503030a05040c090b0105040306110405090414060f07121d071e090504030203030c03060102011401180501 79
    0x403101200700310154207152100503a18540d5a031702c41444001c0c81c03c410b2440002240c024410500baa42c001c3d00148490300c2d0880508820320740f4888020049006944010300007181c10300365035086540840d188501386103680c00f0034214000c170001c840d4001c0d510112784c404001612a03803405851130682c189042ea650745403082807845148100f01c00248108009241a407041104442c0800140342603464141c0540b181132440d0402e8450000303281e07913141400100078401c0c003040700801d0810401c1c044141514000307020746c002c1e4840600f07100d40310005410040d460408036406840300800d81000d60804c1d0030515030b1030010300d00c0804c1c14490440032442d02e40410680500c2000b2039a42c0e011040c20011682c030103800341c0d44920404505a1008501c113540c140034071790103015800008001280d501e500e0030b8102c4015448001110300c1d250034003010a80c08070440340e01070301041070300e1b0781e944030380340102c1c0104961650b0707000c0325181c48004a0046803100188110322000d20301032041e41d03240c0c007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 469635566 1250 469634316 469634351
    0x40203010518070e040c0302120309030f0106050d0303050c091801032d1e1e03031109031504110a182405010f0201140a020c1b0d06020304140a050f01 66
    0x10000b64960b00c1840c0c01c21016038108400c41c0c2c018031a1080b50b0050b607507540401d007a40541011500c0301e0b000400c0c042d8a40c00d040050312281d048901c002d000c1d0610b003a000c07500040c20120301404254a8000081760b2004420449016920180480e00341c60415031081d01101000e02003110750542a0024040c81c204220900d64400e9090390592400500ca070307a007561107001c03050043d00340d4030b10002c15170116022008a406014910010705183d80d072a1078010704072154094010780d181c406002614064600003000340c000c0c00100034600d413549490400f4440004c0d8002ca06078011103850f00841d0314032a444040403210071014092141e4451021000d044003c0b148000c050140e000700200701d02d40c41504c2001c8600780b40d00001808002a000d80d0306070b80300448112400b5500080c1000407004104502d4a890301c044c044902201a014002020b55003c2d11002d0074287c0c010000c10140700061101d13805600c0c2c220111440d48241c0d181058a40c84040319403c800c1d460f040e0035290f44008031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 469636816 1250 469635566 469635601
    0x60b0a0f030803010510170702061801061d0423030a0e0301020a0f120e070f060f170604110c030d240503190609050303010e011e05100f0e0d0b0402030105 68
    0x110b0840c1180c0c00c00090050b4103501205500400c03928098800f58010039004441c00740b4007590103000c89113810305640862140c000030703225190b890a0130412402d52820f030424800d581a00038025992140d007808040380c80520000d0138080440c229001511000200600000419444004410b08401e04141c00c0380941c50f0948041a440f545c04120248a8408100560036502e8002508100c0f409214a010203a0704081000134859034180403141d00b0140a40d02c048141c41e00542600b40346079070b40780380310000e4071007800390303888045031001c0141c41e03410f441042202c3c3d0100ca844984902c1140c2c064241da40c002c1d000e01c4169055070101c0307108080c00b003090307890180c0145200c041d90b1491401c03490f000441a58000e40d146000c00000b1824030013540286180021034503070394141a40042000982c2103811740c09140004200015100c41f070140b1109852410006c849000604055400755000c5000c1071380580c28000316010850140c50040c040d80c005c1e0002c12169848608208070080d05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 469638066 1250 469636816 469636823
    0x506040e13060e070b0706050a020c0703080708122d09031803010f020408030315030c10180b03070f090f0e0105090403050c0102030a0b0f300316060b0a0f03 69
    0x1400146031612000c0c203a01520b0300c125000501e0744802e65901d410300660340c11404080d076000403030809004241c06401d4121210b15400c41c03601c0d1185940e655603c90b5480000c00920740030500d0000c4c45a054199510010700d0001c24840e445e1a64a0707900c0b8044041c09502c10085009001061200b0500010321800c540704c02180b4155103040030788440040b10004551540d01c5100da81020f012078000f4200814413440250b88905007401122115100c5000c00d901075070004000e82c40b546e9940c1d00c00301c0d0a01d000e082c10314041a2110f140a0710601d03a80054103016000410b01009640c091340c0800b144503a55664103030b13140c80742d4040c1c0000780b80703101320903c0c00e40501c014012850300b003405640003482806c1c111300e8442e01e0310b1004d081e81c208070b4010f41100e0b5a1200d070315450411485d5502c01407001c40e1038983c200c200340c220000021300189040b0a003048001c02d949000000c104030b524140168900640c40a414a42040585400795800d4003401c80f06000240b0340c213022a10f14180c035071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 469639316 1250 469638066 469638089
    0x3081b27061225211b02011d0f030306010309020d05010c0f090e01080307060e070e0a050411010503090d050310180e0c090705070602311a13051c050706030b0307050604 74
    0x1030030f20000c1e04e40c8203003681c0c84142035035519a01001990745004048031961070300081015000d110301c0310303500b41d107642d0304000f03640107a11980c00090001c030441354840024200014449581d0020503542002d1180c010141e41c0f80054401e543c6402058460f0748072580d5440c021000c0e103c0307407080f0f120075080c400c10060740d00500817640050803035008209034076075020481c0d48090707582001b1070400d80140c0341002800d03611014041806012050b15011206c00e007003c0303280d1300b0700342c050356a079000f00c1000e03104002012002c84d00740061040104000e01e0403020700f0100300140c40e110001031500046c0c2140078860380402c004d5074100480d42d248151101d031519400c224503619040003943c80b440500b00e903070590781042c400c03110380c0d007901c10111410400c0c030002c221700700303203000842483d00401e1050500050000d000f062008440c068195401900d01c64a900c00b6800c4104082c600804002c103507010f02d580c04110030b0340c598040b0054000440881c6e106c3c90385c134402c0c000248524003c040c000c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 469640566 1250 469639316 469639337
    0x402100314180a0b010b09150a02030a0c060e0304180b0103180611120403020a020a0503060c09040f110c1c08010303080f15061603081b27061225 64
    0x20314124015a0460408141c42e403d1409540703241e00a1001d03004a0b07a00c11012075920b14a0030310701400711840b4000d1030014a403620600f4040e5072401180c0890b0100311603400024108119600501da0360791010089a440360340340c24000e205250290010040766140200f0501c0661280c058ac00d04c140e00c01904190600442d01d03000d002c0d0144d00820040c2c0103080000045000c111a05580704038069405401007120718410410341c1803036a80031600c0703540441c040c4078080c10000304039010304008480014980b07290714400c0000d8284103100400c81000820380b0104c5540224103686040442c89024801c1d10000b1400d68400c0000e010240005003004001454000d440c43c0081d0010f05000500203401444800070301e0a03170044030000640014131842c0c50805403c1400c2580006000c00506209800040400ca95000720b581140240501b141100100b24013407070559805038010f00a550b50380c0e0040d108601c00481641c4401c2c01d08000402c8a1201500c0c2543c040c090445903903101500c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 469641816 1250 469640566 469640581
    0x1b06070807050313020901060503040201030516050f0a0909020a030608190b06100c1209091d0c04020313061104050a081c0e0105040e0103140c0328031103070501050402100314 77
    0x80e00010f04004c1c04c3c078582c11403513000d42d0b120300e4001c0c002d1605581c1c0e03540e60f01c0c2610004051340c1c0c0250444090084501001007030079000b80540d066403603910031443e114801010200c642510b1540301d0303449144001940c0742c50315450b030002010703503542204440071100c1004840303811074202c0c040609100104004140d203450700011036204810f0f5480c00700d1844405482d40540080d417002543c0108150b400c08002d80d010502640301d0704a8591401c100d40290202c01585402c8100300283c400c070781c008000707080d00c075003551469001500028200150b01d4141a20002603010740201c5202e001042030008851a0002e601500340c5414030172403050309541041a42d80c00c0744224540c1c141306040c007000c641050350f03107102c1d4020340c042c051548502d04000c0c0742908000c1c1800348240290402c2040302400d4008402104421040c0c1d24120401000350504a500c0d107042c2992400c00e010000b4480140001500f240e400765008a804208a8600b01d0064088803480040c1a4a0110100c0040c80c0d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 469643066 1250 469641816 469641827
    0xf0604020607020a090509060f0601020c0307050409170706090303110f071b09110d2a05030606270108010e090a060e030f1215041a0d0212121b06070807 67
    0x2901c041c191410f90b58840301005c081c0c0c2c208440341403855115504119889039042c00740341e0090030070300180040440742000b10392030307142034003c50340981e8684500604002d103111030803601d140c2c1a01e0107034480d1300034136001010b85075a1a00b80c000030300b0303e400e000e02140c40c41c0860780150592503207d46402c58a40e21880401c10407041c0030001841750000040700b6080d40264451109400c0780307181c0e1800200c1160007201e0009044185203401c0c03020a9007a0003034000c04c100d0400075420701e03a84a68414001408034800c103103580b042c4141205015001003469143e942c82e0074801d80780c0042d80d81c2c8955250b03811441c129000c03d266813041c4012000709400764046802c01d56020243e03407600d0882d80c6202410340c0034a20f04a61144080d04011039040c0004c0740e052404c1e0121414401d010b290078402c10f6544083c0c541c94401c0c0ba11120a204540e00c1c030000301d8005021900380c4003245068459030070f10344c018990040d000c40c9031014100180b100411081d01c2060b843d143c5c10300d15102d0803003c682 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 469644316 1250 469643066 469643077
    0x1b0105240102100513021302070201050a0809071a04150e060405060a0e090c13080604051018020d0501020d0b12030f36100e100806030a08031005040e0f06040206 71
    0x190f0140a6582c0c1c1c1000c1c990090b18403445905101e9980076190b4418048611105041d11895903c10320040006070390001c1224150303103182c90706a91030344541064030b00302035a81e40082440c40780f40307480090030100343d40030700308441040c40c401101158014099400041c69442151700c0308040101384403618003003025007103245607480c0c180142c2ca03400c1d0100d034824406441c1c0f03100c554808a802149031542068042c060140040a012541482d540e400d5464a903090107030012910381d10545048480400340504051b0002c01e000000c0030b982c18180c1c003d50010640c0f180daa410912440894203003a4050492040304400452400e40951640200b41c2c1000f920001c40b1340c001c40c000c501100d000070010f01d4090549881c1241c008180342003280806005182c1c100340311080c46194003c0c0d444001d981080200c40c10101c0269641c2d00c0080e00b4242803010082600e88048280441c422059000e00f090b9202502c0c100445030038000700360b030740d03440c420f007184280d9000c14006401070405101424 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 469645566 1250 469644316 469644319
    0x1109190218040203040606030501180c090c030b040504030314010f0b070b06040e030d050a150311040e100606230f3001060e19060e060903030706111b010524 69
    0x68040c407590300090b060740e0050358241c0701d581d15000c05006101003813240d42402c07440315842d00310042069581080c800340f03500c03a401000380c0d20b0100321141c038004d4024081010300140100101e160a19000e402400c05058041021103440004110500310a00d40010ba400c40070106003040150f68480007005401072407550040c1e00c9051140071148108040d00c0803034410280483c0620306810243d00b00e500320050785c0e00006094100304003240e03030910691a0a44191404109201c08034001460003e1900c8404a4a80303070100000e00d1607888040f00c40a070f0003146035201c542240d440c480505005003042c2100400301000a109100c480582e8803030740c840154180002c000040300c0700340c50f450090740718002044084a4031042c520b440303102002403c9640001e0301040d8100300c001003c41c0074401da411702540700000c1c580031990b410010b58803500e51101090102c181d40d2041500c640d002441c11b885d480c0301c080d450804502d418081d0905c15a48588800a900760360214001e2650f1b4000165 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 469646816 1250 469645566 469645597
    0x6150127030b04051b030d0c060c0207032102100b0604170f030a0504090c09030809100e030a110108090607020a0305070f051e1e060703150b0d050411091902 69
    0x81da20749001c41c0704038002c13000b0b80303104543d58a08180b014030700e12200d44a13401030500c1850994010380d058000365003048001545944600099190080c213030006400007001802180e401608040c9002660381c0f15420f941d44880c3d024418800c0d41d0041d0440d50344801c0920040c840c180a143d5a00c1d9a660344100312040c4c0c0242c895164116800506510001003001070184022415809882ca9410b003502c0d0141c0b100746141c44220441c011003d00a1040503106140c0326824410003240c0b0403400e000b01503c0c92481d29190084100180f00080b03400b003038564001562007030b00030441a12400480e000740c40005c00d151382c1240c0d903500101e41144e1140855400c6000700324200320441200020046002c90300f00da0841880c07415104020115004004000e018070404002c10310399000700d040e040100c1c68a0302000c040e0360322141034100011071040030809200619458104c0c0d030103580140d02c5142940c81c600e060001c0041d0072542c1c0d503620050078a0850111303120340d00410b16071180c410700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 469648066 1250 469646816 469646819
    0xb09100203160309050906010e030d12020c1e0c0909100f111b07120302030f03150d050c1306081b1c0b2401021c020115061106150127 59
    0x4801007079584a064000500690092004c0c6c1000e00b002501b056090a098401c0e03680380001035500e291543d10101040151010030411484c2d64050302d407051009425242c40c910b500b00070141c4614440840c094030320850a40e03500900704100310500030b64241d0040d19803a1040311500000d40301d042c250003032455680300321480c01c01c800310140051b00848980c0c800095011030300c0c1880e01c00940c1161380005501c0d1a032400186e0000221404078011240b5551250f8408402c8104419032200841d001612a0380300410040042510582d80d03104480a030206a1004a03c2c003c071406e80c0a44412640000707148010032082034584040b001000300b03541e05040f0b1039031401034880051401210800915814002820799921034140c05c850081c48405091020f000000d66564100c200e080820007a0001550749920039045284178850442c40c0812003a59420000d2403c244080051114090342021400b4200c91001d4252041e4059451103981045071015aa007101c1d000c1c007071410203285400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 469649316 1250 469648066 469648087
    0x3020d080606040918030906050f070209191b110a0b012123190f080f07170307020c010212030114032802090708040b0a0905030d05010920040b09100203 67
    0x3400c1c03400c06620a003904030108906d00540080004c0e0002c000748a81402124800f0400710141c50304990101c1d0f01441c02e456460800b034649080c2c401c3c0001c51410178200300c24030814940016942c1100399a01e10a800d460003004c1c3d2280000b00c4018240100700004000d2400c01d140d1a95651402150481541c89581d0f01c541c02c41402c0b2450880e511440e4941282c6040c3c00d101c80720400c07035800640c15401c4500d50720742c004440071070401403440b500450003c100000120036200c000703500c0b060620b000b0888010f00101d50f001100c28400601c03807418440c0036540701041182000c6d444d009060305507424440380c644c021001c07440b500d4240c460040c607107408201105600107a80c00d03115031700400d40100c0c0140510f52600600000c01d000001c800e100002e40031005040c1e006071492000628004140740150940c800c641c030054003241441e00101d05440705a00c02c00700780364198103550355151318100c00c0186005521504040c0d1005010700b0601b8108a40041c025100b18411b0324542445442c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 469650566 1250 469649316 469649321
    0x6050307080a2c011508030f03130c030c03020901052e05070213271203050604090605041406010819110a05060301031118091c030b06070308150d03020d0806060409 72
    0xc800a03e200314984403d54200c003071081442c0840484164040c0d00d0508000f140d69214031341c485114100000001688084c1c91440c80e02c2084d48048070a003031a940c1c1c203007050f4000f02400306a01c40c8204100024640c9401d550111181c1416030a40600003010b1041d089411061040d450074080200103000060b511045042528020300c400001c0306845170481804020a84420340301c814250060900840c84602074400104403600e4046503d03034407a00072030060014940010009820724050100b086007030180b00140e00b5501c0d0485520743c0c2d0b2080910340e0b54801308070341c0003500d028010f030300003054030300010030303229000a802c14148942d2040412800e0380241e10664401802507445a1113107001003034056031000143c05007405003400d900c0303076494144074a00c0550310008003410140f4580250051408040300401c03181e124030040c10007626a030300882d0411400e03114000555a5894400c0343d40045541550041c808418219425501c004018084aa20500a0000040c03030b18850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 469651816 1250 469650566 469650611
    0x115110a02153001060207030b040809060d0504111305010f030f2d060c030204151d0a080f1903020303070f110303010303110d020607140d060305120c070e0106050307080a 75
    0x1030303900d0000606039002c01d43c54444103803c080c0c02c64001c18030410200703c010303e00b141c026401104599075000c210002035000d224850340300d0140360406d01000b0910031110b443c9401441c0549914200042080b0441d0441708c00740501035107403401c0310080c0b0114604155040a0b80d1040504030240d00c4201b000240740c0a4800d411001c141c0c1040d103500070001a8054000200b100742403e508003410301502d5014083c03180414000c100600c1410501d54200c10008010703100c015040c00507240e150340b4060b4441e850600121001e101d00368803180c119110220a00010f50194040c5017103894a030406c844621910026504120307040030020103407001072000750700a42c4130341c40703681000300c00064881c10080d108920000395004801004883e07038118003211020700c00c0703941c07280e902c120380940310006100503040940719115006182903000c01c02d130020039501000804841d140c3e035075a48402c400001c24024100000c8003172012070001030107581110b03040f5034843c0340464603440c07401c004540784500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 469653066 1250 469651816 469651867
    0x8190c020c030a1410110324090c09040b060421020a150c03141e0d0207060204031505130809010813080c010510060f1709150f0115110a0215 62
    0x4604045018208000640c00c41c001c0180902078129003841b00c0119000041882145e060107216440d401196543d00d1280701000510240107400e1665504441da04508070540c0944e15040c03402800703141003010743c0d04032160744480c000c5000045c40c05010f41048034008980251400348082200c200d16a41c0c0c9030b060440d80e5800805d60441e003030042c140da03008000540c440d1402c000842c41a440900200081006400c000f03980c1c0488010903802807003001005031816101040c0031007089003074050750700200b800c0202031090b41c60300c001100c4e90407242400240140d03010042281c265000741c5029511907401c606030720030f132400e60700c950031264802c90b10000c0d0340e5035410811820048a120f103c000d00858a404084910382d982e000e0401302100c040742c1022800f290000310407440c200103450a62140b07407140c01d0701d0300f030644c00e00c51310755400c2c0648a441c40c610b165a030350003403161000c0d07842e07810a040207040004281d0284010310803145c06212107440c0421080c05034041c1180c8003ca240003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 469654316 1250 469653066 469653083
    0x20a0317071505010518090304230f030601120b0a060515091f050a050c0c27090606060921030f040f0e04080a08220c0303080708190c020c030a 63
    0x45140020b8804021030b030980d8a14985401809103460f040c1c1c00100740c4c0100f44040080e40c44d59500d042c903500955000d006401015070500c03040c8130703140d68004214074055034010910301002e8201030301c407542406005104806203000c000440c0040400c1070700480d0070320340000c15644410114584240d051808441d88000081c02c0e12142040c0c0100840303d8031070132480b0103d4a800744020320601c6050040820000046800409400180b044c02200d16008207403126229501c5400f403890080f0940981400d40d8000009190640c007140b203a110b80401041d092a010700c0204006180000500202c5058000d441e40300c192403081004141400200c0b142d10348071403406c0e180c140d40c05940d8021602608d0b2003008d1000180d1194141d44c0242c521307082800d440d81d110654900c0700e100103c0412020050841010240610f001c100f074282d9000390b4981c051a0380b0f91105030b404080555080c01020004a02c04841c616654082e1901041c0b43c81942e00c0381c281c04000a14005810009541e000c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 469655566 1250 469654316 469654327
    0x81003061107110a0f05010e06210f010f0501022107060920030705060d09031806030207110d0c030605070509061c0e0f0c0d02010903080a030507030c030603020901050d020a0317 78
    0x101d0002043c0c66003608079a03003541141000000c1001041c079110b0349040c004002861400f40d0748601c2074810001e412a49109580003604900f000c00740306440150f10403116030008202d5000846c404000e994042e0000c0c03030f075400840d00391001800c60f1404002486414449030002034810302034108018004c00459980000c034500000070074050010203842944032600400c016201c40041da40c0340b407000d00c00040e455509060a46854242c5104c1000c00e82e140700340440d200e60150b000d000c016004d4171804c0300540d80d40007444003ca013207110162000d03107501020000942d054002c02d91298440c40c05030700340200e04010a4858018140c0c0d844005050f0403100048000d62180243c1c16442400401821101420b9240c441c100580c0160042269241410030b6900940203100210b60000a16544100b0703100e00030000c1000f59100c100003030802c0358101490340b09006900a40ea001007202580d03910b44400c000440e54a036008030303000580641d0010109006848183c00d90080d15030071541c2d807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 469656816 1250 469655566 469655573
    0x70e040309080d3f09020406030210020d120c020c04111909090f020306211e0303060a0b460909060b031e04030e040c030e15090d081003061107 63
    0x5601c2102006103008103001d001380c440c05015000d24032101010b00010300300c0081d0010070007519440e08082d4112248000031200c507940040c0d1404002d50a0340c650100c0e44104041c0c2c0d0590382d101117440b00582c0125035000241c0b600340c2c0140440c40502d50018a0841c08010415410f480c034802b03140070070348020080044202a000300901500b074020b04614514241c4002640d0341029080461142c9102c484c40089850410085000e40020903694040300b0181406c1c543d41ea0044911764001c3da224080040c1c6541840700b074072500c820350401030100802c8602d500e1081e08038024180744c0d0031011036060502c2d240f040c02160381d806095990240300c41c1009245810758540d5400b0b018094010010400401c940340300b100107500d4a141030010070303107807800c048811410b4600c000b54042e01e0b0503101c00c1d009805078041e0404500750015078000c21008a115500c2010444505001c0d400c400d4060f41e06904c68100164803403400500c4150080e12600e44e18101c0d0207111464aa1100014850062 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 469658066 1250 469656816 469656857
    0xa1a0909091501031506030203060406050105130b011b030c0c0e01030b09030306030c010339030e010e060105010e0a09020a210b0d020907030603080304060207021203040305070e040309080d 83
    0x8081e80e40201101c20b480c8402d10260001440060309494080b10881c0c000e0f503075600070400540d0010112189420305080180007420f017849010321964400000a00404807801100c403c014140c4608024660703074110340100500d01841202008911b5650000181e040003200000c1c1840495108996040d8541502c014502500c40300a40e8000d00420007103980c000348203082001e0070b290100744543e248195290046c5440b60740e4103503c03203201d44000c2c80d050602010010000c2980c0a0100c10b500100b40790883c1c40c040c00e0000d154000d44014000d550141d82d05168414000c1e09840c00d5994424149080f8bc02440c1442d0005001c40050b040340d14102110140e2a12014802c12a01a42a0010701002205c4100074003924104000500080c006c1e070180004540020115950789807034a0080c00940c8001c1b422031182d204001200765190001007a5810b07070394084003e2060a0611107074051a01d0020001c03000c100703012a0114400d5401d100701c01010750303103449415580c142055040e80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 469659316 1250 469658066 469658071
    0x6030f060506210d030c0908060a0c02062a13030b09010e1b0306070f090b07030e0a0e010503150a0f0e1506010815061303120807120c17060a1a0909 65
    0x1049540d403c40e0001040003c1030090081e012402c0002d8010300e281402e9500f04910381c4040c0b0300b030080800f007003810100d5811180c1fa801450b400d0ba01d0300c1d40d03034080e00c441c2d481c0c040700100080c5c0c3c0340507401e01c180d81c4544014107001c015001c000c02c0095480d907400d80c0d480ca0031034901200d030351120701800c0c80c41001c00c040039203aa10003c01d082441041d802190781c6105c010319840401448040c1481c86038052039206001d85101c0c1c0c01c0c01e42e960803d00740a0144100d4012460061150840001e1110013040c40c0340e051700d0000380582000085501d41c0e211490380541886895135580f034091441c5a02e600c203141e40c0c4240031010b0000342c003451150100100c0c0041440d4140714082c410001113802c951424040b000049606640310319920120100100468100901542c107000d042405203802500d414414440c5582c3c040d09080301ea11b0344e0b000c0d10341070302804000c9019203110800803031315502455403101000e0403801070f41b903032801c1d601144070418203014141c440c0092941400c1c20501003196 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 469660566 1250 469659316 469659349
    0x510080c0f090a05040f0210030608060901020406020a17160f030806030d020303010911191e11190204020c01050a020c01270f021f03020405120610060806030106030f060506 76
    0x404030540341010960b00040100503000c0b569803a00041e04206002d80b804407016009001c022103100503140140c014a024024003c2c140328180000d801c880c0705000b120251a17481c1d018280e800525a19070100c40d42c0b00702001c0e1012010702c04150070104c50841c2c1d040090040e113048036500043c1c18054800300e0050076044c001d07005880d50120294000040703034119220001c001604d00f24040c09180640940c5003c480344001d21741303080c840e0319409103603142c1820011a1108640503400010340300e40b4000260780c0007039082100c6109400501c810444001030001e40302600e026102d40c0d003d400c4450450b92200300030b60204002101c5a000d1144031a81c09140305c080c220840201e00784603481b20550b82c0101079041484083c0c04540b2401d08801c4070303409010301c000e6020408803024010b50014021907002c0d2507a00080d0655242c00200c480c000c0005801070b8140d141404812900c0080003410140c15640301c020000c00076940d06281084c0c18012100000d86041c510100700c800c0091030f2014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 469661816 1250 469660566 469660579
    0x80109081201060f0804080c0a0605040b1b070b041101031107060e0106050f09010506070303111204050d0507120f2307020f03030703140703090e070c050f070b0a120f0510080c 77
    0x40b158100e11700a80050700141d5640c0c03500c000d201d0700c510b05548030100403d4170b0304010070b1008018251000c103000d2041e1980955000d55084101e0380e050048400c05400d40d0210b501042c0403400e0000118000d00c030615011400d07010280048503a58040d502c00c0340d00a0b078804507103143d02000c0c030500c0d004c0c210441d4000c00038412040012003444040c002e29124480c005042d104142c06a07104001c4410000c0910791100440762a51200140885e004c1e64107000781e2281c135111603c00d004071414250320910000e5a65406001180c8806060240c54103100c10929031029031541040804000402580f030a0707558041881840381c18101c00701b000d80a68414410034000a401860071582240c104001980780c0320281800c44200255601140c00a9214401d00509075031129110070220301510444038502c4940c09000d03034807032b11351143c200440003c0c07200c02000d44c031412400d400621049070201d245a4040c0b094000c64034251506000005030704007c00103480d040c0002c03642048102c418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 469663066 1250 469661816 469661837
    0x61603080f190203060303071718031227031b030f070807180f09110405070e0109060f1107330909021b0114060310060f0b070c08010908120106 63
    0x200349000b800c0020b03081c2d0044002115520200150b0300c1a03900840031110a08002800600c07039030000d214a0644441c0010b4071005040c0026000448007240012500e462a9000c1d140d40c0182c50200402c812141101288001e603400c018103820440c0700c6d82e140d0794090500d001c00d490400b030191600c4070744c2c20900042042c1e610202c2c50300d04680382d0900c001c040690483c1c4840061201c402c014030604c0c0350410340300920200307844002141300700791000c02160300ea4140c26039440242020803030001d580d42e40144102031103500800306103038560502030500c0e031403045480e0500d1129080940686070801c01c0c1583d001e507840155103072000071102285941c0551200a0410a40e0f019204d501d40d0002040c8460540d141603210000514000030004410010700d443c10b5040c007038035003503c81d1084c0d91400910001d1842080c0456900e510040c10f041c0c03a01203241e005400000f025075100c40c1002000401000030301030000100e1049a0302c65651082c5c001140d5680d40603005041005900850f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 469664316 1250 469663066 469663081
    0x1b0a14160e0105103002031b07020a031419050109050c1906030914030d050a06091e0c02160605030603070603020f0703120f021303060605060910110c061603080f 71
    0x101000b02d503800d0700c2c281704c80080c100845500005031045106612039480e0030b103410481d895000c0c41c01350034a4010030783c0203d1000e900d0301c1e42d03000d54180070354040c150301800c2000404094040b80012140c0040d1060407100805003040c1c02841038080d035503651250107040030800f0a004048082c50219410151004c072002000c141da0014042c100505a03921007407070071700a804006440d4026070030308a9950b012201e22030000b41c2025100c00b8042d50800c0030124845610303000b002c0b01005e00b0400d0103005104400441c020300390810303555082d80152914102000800309581d000b503c6e903903c529a890801c00249450f02d815a4425000c151051000356035844050017105e082c0754041c0b4112226200f4000c0740401080c1403010700d40c84510000c1e1500e1303024275180c1108100da001d49801c2010943d1401800010301c160980642e012821941c01442107001e1400c4a03103034101c031801c56000040c100c02244050344012104d8030301516544100007095442a041940304402d004504c106003031560 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 469665566 1250 469664316 469664329
    0x315020307020d0323041101080a200306130603080304050d0f27180c031d060c0c0109020915040b180a0905030d061508070c081b0a14160e0105 63
    0x50703e203080546031803c902880d030400300198031340700b003003811001c0500f0a450005c3c3d00003060307091140400c20307120000d5030380002441078013040f500b42003039085003501d140481c030b03450ba1004003020341c42100520101c4920350b04e4400c401c06103101c2c0400903502c2c10301c0c0c05c0c02460044000c4404c01049210b292800407990700003c0e4000501c9606502e031200c564220214a0503c000e8002603a405c0c10036107100d0f00b052041d08610312010054074104040d03204180202e016a13032580d0001202c0e0702c0540483c905c80f45100091058101000c00003609040c0c582c00201e81d24016180080b9650104011820600c4e00340b060050401e000c030740080c4c26100065002a51580003003103c428195140075800c1070000501c11201c030301540312020413256496440d44000c0309900d83d80c02002070405400a030f8164000e03003900100540145100b03080803e11005281b030076a1800c4220f03070b240104040440081c502940a1800d0741c501000360800c100c5030301d00c0c1d40342c8000a61000ca01300d002d18004200c1910f910 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 469666816 1250 469665566 469665583
    0xb0708180c0d14011406130203010b04060806030f0319081303080f071107030f050d02030a1407210314060319020922030305010305070f0303050a030b03120c0304031502030702 77
    0x7a600a00c00302454104410403458030203540f42c00354240550f000540d106024054030442c82101c011444407000030707812040340024050b10480120070070040c0047c502030344e0030952250000341282d646808031015141103812681c2e180c00080c24050101901c0c0390480c07030440c1d10910800840c0342c8110a42c90007003802602804500d107010350030300803901c500e200d001e078040c0036a400070480f9800c60f502e16165000c0b50b01d5500540d814002d200002c54000e201000321038240b051b40d5504500c0024090000b101f41d40700010480f03801900351803d410707507141401d0403042c030103060b180003c511240303560464502d003006203240d10a4100d198800c008030264499840f00c1e0340c054664144541d0b072401d450b074183c141f0f8001c50300070401704104102013682c16008203040e281b08a0a840405694030007441001d1101d00004000c03c00c1404410f8007503220354400c40844000504507a0020843c1601140765408030110090a4100080074410301503001002460441d08040c11803030f41c902540025242e9202 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 469668066 1250 469666816 469666819
    0x19120209030607230f0c0c06041215021902060402010306171906380a060801060f03061e030b060d020a1a0c030d0f0506090403050f0c01180b0708180c 66
    0xb4190f030320f0519613002414140e10000d80300203641d1500b00a0450780d06800400540d40c1c0c034440c00f20136159034180071017a142120728090b59001203003002d40e908080443c000004008155082c881c411500264600504c1071242da40c01500040c1024000101520025080460810403500f00102003100c0002c50351001400e0750b03030800414600f86000d0300501164141a4400209406c81e1610504141682e41000b250320460a101001c600c060000000b032510901d404200d81c0c500401a090061850050b002d9581c030700010b09681700c1c010884070480151608008000c080414020480300544068110504407a0103c501c0c0d4283d0000e000b03d034030390190010407401c812450300803605c2c90303056400c41111042526294240d010180c002042c01c08400079145003440041140390805244d11401580c05a54903071424444910082c0294402c44100c8150365840c105004090180313100d51f1070f924407504045143d420800300c001d00c0650041c090340c50303052480d0341841040e400050b5042d0f44000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 469669316 1250 469668066 469668077
    0xe0714120a030203091c050106080309091302060412110a0b0d0c0203040819050708060703090210050a2f0a06020a0e0105030108031c0f150819020603060d0f02030319120209030607 79
    0x11095005507000c4946c1800410395820000041103200000c800307400080000d4406400d1562800e10342030800c0c1035a034000c1d400045c2040140501c0c04504007260302c0d5802030200032440001d800103c0e00d40c86080d0b1010122030f40204d01c1c4c6940ca000f0380540c0000d0301c00381c80294140390a0042c0c907a1552001080c001e00d520811041c001006018841c0350002c0030200c00391841403400d2803001e400b415081008038401d2542c100789902450040d810341d0801e44050761140c076511400400c0d410a40c40c640000d003914140c4880c42d1a068500704025000240300e80409601c81d5080c21001d1700000440440c40c2c180041440148403009000068442c503854828226454000300000c21000740724401c0742c1d04440c2d0800c00c01c000461006445c0b50704a42d445400c8490301d5004400801c540201d001e8000d60014080005c82e1851030420607622000e401907284002050242c0d000901d5a8070080e40410011680c1d0951a0201d81203140d5411481820300203500d01485032000a0703c80750010100c405005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 469670566 1250 469669316 469669339
    0x30601031407111c1b060e0102040b0705061b1e0d290402030709050d11041b08070507081b160b040821090111010e0714120a03020309 59
    0xa1103508280324581103070000310100d0401950040c20700c60f04540380155032050b982c90f12041540c01e90103a164030201d03a941781e9032010801c013680c4600d494034030a58100781c079625462814002840100014000e5071000366540b4102c1c03030a5810320000525030801b003441214611103510381841180c0c2d0302400901c00c0340c078010711038880c43c01e9802111209444c60703103010701d80092590380c54001a06e0b070841d9811942d880c582c080820041c1d03c411100807001811a110400c2071741040d801d00300c4000d20030070000007400010700c00b00c1d003120b104014030502032a2005400504a400a02141d04410185001450040b00b519002c10300c2c41064104404040001d00f800d20001d018081e01809260381200d81040075078445a214032030b000b034040d01e042c42c080c0c00e601d0200408000300545035485200c40d010f0401241c4801501e040b81c0044c0321100325520f401c52250800000d228035030182080c0207c001d03403040d20070180a013103588605c06910325800252488086900042640d9058000300c0c0c5954043c3c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 469671816 1250 469670566 469670569
    0x7170d030e01110a080c07390b09011b0b0703060f060201061401110f0d08190504051b01021603051f15140d020901230d030804030f05040503162303120306 68
    0xa1041080c0034080a440c010078000183c0381d21716050141e0b040c40d00d0104002c3c08c0c5052001e020741c2c94410100f004004111300740d46540200c03640e00d690180b0b018035404024403600e0310100b1080807a07140c00001e5550809100807840007103140098002d0784000c12031035003000c1c184400c40d0790002d205030500c0b0034211b615a8010003001014216807206083d14400c00003904043c0c425001a40c8042d050b041402149286d00c05503c01d05208941103401007000001054400c0541d4501420441c110f0081d1003c0450002405107404020b6120300018608648103120040e0300485035030038022483e0610254a5070003241201c20b4081d100600c408a43c00000b1000040702c80318800d20081d0000e003800000203443c0d41f440314110140c90385181141107004c0e510200118208529070007404100c4042c08240824424644d030407001285091451a040d1107200081c90684e1141d5181038158000c4828010508000e000034801d0000070460700c41c0454440021381c0302d26143c01d228002c5107011000402d503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 469673066 1250 469671816 469671841
    0x6060614030703021605190507080c09010e090c091e010905070e040c022d0d0908070b0310170c040f1116060902060442050c07170d030e01110a08 64
    0x4007980642107460040c01d400000031100340c039480236a8507000d40d15000501c54000f04401c80810390061200026a0030046501509040908007042c240300c2c0c4400f00f59103840f00000e030750041d1107041c48440800000c0c441e403040c80c1416000411001d05000078018140d80209049031150030403603010540d084d0301c00e8124580000840c0d420030705043c4403501c80c1100c0c1d4200c903000368601d1341e41c01c0d16079050b07140744150741d40c48046c41000f200d548100c07001c20800070f442c03028582000e540301c58040e0b1141e035000345140306075102d00701c800541c01c07240d590201d518243c802c14000d48403501052140d003594006e040074a0041801220200e45042000810408280e22403151240e00a011548568403805840307914140d103285000c030700708032041e0348981e00c0c0c800305507030840042c0550f0010110411001140d0b50b0f0000c6c6035000700d5105288011480021025142c0500c04a0f240103005090340c110300141175800d2000c0010350380c0d24241d046510501c40c8812104140c8940c00c100c01c10341c072000501e059 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 469674316 1250 469673066 469673107
    0x170112030c0512090a0f050d15150303090e0907061b0201030209040212090f06040210030b030307050a0b07030624050702060d0c0c0215030603071a040b03130606061403070302 77
    0x82c040c101000c0e410a1107031015010b42d85080d12074800c5d0b15103604410801c0c540c24083c1a0380250294001c00c0055180302d1a22a50860801c01080e0072005040340e8451840b00c2d04120040364690304203100318006090003035840100d190040c080c503403030032070041c14190000040310304000250070380c423082d640290101e400381c2e400900115503d0400b59030000e0b0000040d941c0e09010b008451056080041c0024414000d580080c2400403c1405920980090240d0420f180d0140014401000400c406020020401c0e0040c03d03500703070174900364130000c04840c0e041d01301c400840b040305071078140807603510300e4050540f00904110340c0e203002600010300140502c4e6a03110701c007410200100c80b00c3d54000c2c6405900d6100b550030210301e400000a041160004951554040c0d101e0407080069800540b42110b01065030b5050034a0203456010845042d8011180c6681a03580f8200540801125228440c024001450b01001d0020100b8480c0c21318400600740c580bc041d0085400031780480c21101c5002c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 469675566 1250 469674316 469674323
    0x403080604111b0c040b012604020111010e060f16021b01030912020f010f110304060b150a03060e0f0907181d010c090e0106050703120b09040507090c170112030c 71
    0x580440c05107500c50b601c102084e4401d00650501e00f42084a5018655901000b114260107040220394000e8880414800a0059040044108000b008000c00f0305c108076804c102c8401030441031a201402e41400314014240e0b09500100096641000e40c2c04140390752180c0759618900700100000004802030840c1e03920140200802c62000c10070150005108045004100000d00c44c1900c081d4481c0c003102c3c0c002c446448018020030005000403c0317503001001c5020000c04c1c1001a145050400400350410026040403d0340c03424140443d20010b010140c0c0b01a0010040c07001d85000040c0d1601d42410341309000744034400588850105030160800129111101004d11440c0c441e0480c160191a2410034100403e2a45001180450065010301e05890803502c8041c43d04001e540c0c1140c9641c004800f101c10381c1d070b803038204001542e0b441c046240518002c0703008104150a004064007180d420740c607840709101c0d00380b4183c9050008141020b04542118042500c1c22034907041c1078866005080c40117 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 469676816 1250 469675566 469675597
    0x7032c040c2a020d0c1203080a060b0403080d11030c1206030c06090d0c270b01030902030303070e01050702032b0302130b0d1524020c0a030206030606191e020105040308060411 77
    0x10801250b450201e9501c54008d80d1040310310744510300b03249c04407150b034051030100250400050002c2030510000340f810b101090700008402e01000408500b03600103480d8403480070400a00e6105a045600213075400a80c110f0103848002013090004005124001d0202d004048090036103040c09410310300d040c018259800041403810480c0c2026004124840c0a1410b0601d8809000313600d500c0b0340f080e0020183d01400a5117191140c2c0c8017982c40f01c030b03e6000541042010000d8000585050080c0001c0502e030000c60321990444c4110f12802c1450807040504261042c052184031001c6144080103e6040c00c42d550f90721000c13802c0d4100607048a01c24241c544141900000b40b8481d030800c445d1010703500e036100c0c00c00415040030407601c43d103064040c154061907100e002c1c000741c0340a900a54000307000800a170301c1d0954251071001030555101104000c038840ca025603489444030b001d10648000035200070401e80c545950090200c840c050009400343c0c0d40e607501950411840001c489110302c448414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 469678066 1250 469676816 469676819
    0x1e06061e12030d14010e0412140c150604050c0f040332070501080c0a02060117151501080606121501110a08030a0606030c02060a0207032c040c2a020d0c 67
    0x414090810211210083d051801c0000b07400314401b403a4a00445c1c3c0708441000789583c001007103e10800500000300030741c1c410420030000c00c400f08100560004500d20751592460014200012030f18010300b0882048403c1050303026182d601c80440301070700d40c000c441c0d441c200f03101c4a0b040d80144114448007951901c042500112482c00035041c0110b603c00d90b02d4071690780e10304585d40f43c28002d440100000d23a010400500c420a148001c96a201240000312030300c0e95072030340b0124003010047c0c030301c2114107407210042c8400e9684641d6013944007400340d924924003007904003003480300d43c0020303c1582c960030203010b550440da00c00c0081800c07180a0804962800e0581d08058415030310036908505002d103013a00000da014002d000350110200340340c000e40816903440300548065400304d0300c00c130100316507458a40180300d000e0007001c031314614040c1c00c0b88100300c4003001d01c4200c035483d401a5060100c6000c1201ca01d0098100640b0100126551010085e8140c07011072421034969070010000041d0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 469679316 1250 469678066 469678087
    0x3020708070b0a1b050406030e0f031209010b0307030807060911060d02220e070f140a080106120b030303060f0d050d020c01091a091018081e06061e1203 67
    0x12003502443c0656001c000c0000002c00c0000e00f0310303203c04441c002c81c1060108001c81400780d0300c012507070030b620015150303a50500c01e8460700b0340d8020045060b0b81581c003028402c83c2d4038240700c3c4013507844081d8024aa00c07400d684861a0034040c0000060509448405280400c000407092107103040b00500742035100c00c45440c40c0f00c0603400006a9503640350071681c03c00207000d000664001202c4141c00b40e422a0784541008403406590500108e040c407114036203120001e8010001800030350b0442c1d40e049150350601134002c0404c0d07024101843c01c1402d009195071250380110803a87c11480807105010300c45500702c085000100a402d0290650040400c00341e09a40c0101d84110380c030109030307aa03107120340e11080c0612990800392001c0c2c5270380c00f0078004101c40c1e0404c200c61044500031814296800c440b01d0190401d5500c49800c403640607001211200c43c040031102440708120311a0024124614251002c1200c070401c9500c01d50815a04c0748400b65035484d04068046074070156020f603a41c40000c40e5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 469680566 1250 469679316 469679333
    0xe13060606030204060f2c0d0f0302010c1202072d050105040606050a0e0c0d020a0e090403020c03100b060304080a0c020a090b0a090b01050910140409050a060506030c07080a0302070807 81
    0x200e17600125a0034119900c0c010322071400c8411000c46a804280744078103107124000a00c2504903282d800202c208180c80c00701e1100003000d00e250b48681c3c008030b11a400d40b10000c094910720600082d916005110782c20004402111003440b16000032442e10700080103d48001c034201114001034410351804060000303001c0704d900501e00b500c030f042c0e4502205640d52500c0c0100036008403442c50558605100080c1e180d5916001401d41c641d40d07207000980380009000092030b50340300b5101140545d01c030402005060405200d081d611020340c54080040300c40b00404a80c0501c401440145142000100290287c0c01a0201150190080c2c50814025160780940f0020701070648410b11030201211b002820400300d029030030526206030742e4030b13051410781c50901030015101075000040c00bd901d60211543d18104020348008d02000c200443d03103041144412080301c0c07031074101901500d8200100300c400ea0048040b10007565009401e1540d81074025021030080c00340e00d10040ca030000c0040c18030148800c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 469681816 1250 469680566 469680569
    0x605161202120a270e01120201210e0f010b010c140f010c0906020c19090218090c13081c050a140301090c03050a0b09060d06021b0109030f180e13060606030204 70
    0x1c0005090107900040210141c003203403140c1702e5448001401844000c0720106003640051044c1494a403002181090324448003402543c070b0240350761000e030703003000c4001040718900f1806c000000b000032280c0c0000007031594591400191032101b655480d640c40307010400005110a407540001c000d801c42a0400415038801440350b0001803103905c00c180414a00700328100e48600f010010003060318a01084800650030003068001903070f114403041e40700b03904c8a4544a1141d0440c450440d0f81d060301002d11410301e00c90341c0060119500041c46010301c0d0488003180d042080071030900644400c0b10010489100e003a05420980c0c80318040700005048056401c101903141e8651070900c2256104039444007140c0b801d1646540c01a12107011800d41e0911001d8506060700900000d0f02c2c2208000d1600ca03c1c003000c010701c0342130380e549104c80b10900d948500c0300c103850348092918021000c02e44140c0b040c000d4440c01451090000710000c038007000c0300300d04013190140d80402d050000903500c1501030000c3d00603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 469683066 1250 469681816 469681847
    0x1222030f050d050a020318180708181f1d0d020601091103070c0201050d0902030a1a0f0103050c01121d150901060b0706090201020a0212160605161202120a 68
    0x880b0003028003603000b001a50b13442c008070b41c021410044000d000000440340e41e101070343c100e03500001a0325030103400e0480340d100d120f1039115044a8206042a400c081003070000c80038003900910030441901680c3d003d820001315031030700c001c0350080580b6800400b03035403681c525507440e1007164a0040240e4010654030704890707a00004110045081a2000841c80111030050010700c3c00010f02c0015802440602003118100e0800508003402e58082423808800c040c0989000ea415014039484920400d01c1c180e101d40e1546024087e545941c1c0c50f0750760fa40b041003440e814002d1070a0740b403d1510a642c480e5620710310030000c00b8000059400c40c1e0791940c3d0140341c03a2022522440010300c0f40c0030140034500440d22802c6120340b034a91030b0f40340d410003000c21b400d0807070450246a101c0303005a540d8100c4408030042a4002d0a103030160b05c0005800c00310640d000e0030038020240311020054500a201201040c0c120110010f1410b00c0c101c200d09112801c007400340c1c60f081c04904003001709e42c42441710b10340480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 469684316 1250 469683066 469683073
    0x5040906240510080403021e10060605040302040e010c050f030c0f0a050304030806040b060702061308012409090320070509090109050105010e0f0115030e01020406030e0610081222030f05 82
    0x30f900f0080355070003001c0790050003591201100c10452018007034490307542c2d48082e0503250740740350362005c28050316042e602c803000094012a0074030551030548210710700c81c0080e40c001c000880788950017404600441107583e0162502000141c55034401800310b41000d6000030413907990303203482c00c0003412f2600241c0d42540003030400000940581441c4c4a59400480c00901850402c0e64035820005107502081c00303140003645120b000241000240207050442d81003141da0f00032204a482498100d44065019680d480e00342499940429001508039600d07000313140000c0e00500701006102d00d802555400160440d111104000d29024194131103620b183c4a4802408180d13a14040e10316001c005440000c1d000656200411000b07104558405a000590401051114105040608a8002c1d40c40000402d4451501090000042c4101680a610303200250740c0c2c0c03410500300a40d14000d0f43c0e111540b03060f0015003015601c1d0500c85984a1440100e80500c90a0f26442d16155001000c00101c58520 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 469685566 1250 469684316 469684339
    0x60f050603011103060d060b030f0c01020d0201020a0c151506080a06170c09040c0e01030804062d1103271c110f1f0917010213050409062405 62
    0x1c1e06014030342600454110761411a00d0304810040c511880410031150701d59591098109901d050250401490210000d0300320103541070700184c10241980e1030340003164030404c20314000e0398201003103086031a0080306030101c402000d01c0307480081c0480c07d00200305a1085400203015a0700965051142900d014280130320340c0e403807000c803032031008031520552140c024584045c0c05050010310307543c0c403070300510340c040c0300a0b55611460101e003801e8100380c4019400050a02c107280c1c11030507a00c410200c849014128070340d541c9901d01c40f00c010130712105c20410304050300a10040f01b0030076145841c0d100c001e1220082031404e00c050f1300d841030007110b5008101600c1022003150042c082c2041440d0000c40c0c0755514124030040042604000c04802d034825881400c1d03014080d040c4542c2d8202e24907a0b00d5801209003002d41d221000c194881e00300c85180c2c010070203c03032250442030b500740480381c1c191030200b402c0c0024603102e400b50006c51404000401442155802d00c00000f0005044a20075105070010740d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 469686816 1250 469685566 469685569
    0x1d04080c0f011d0c0904080306030703150516080f160e040c0e0a050409020a0b0705070b0a020607020c0f180a020c0f0d0f0302070c0b0a1403100311062d040b07060f0506 74
    0x9131030715008a680222503800240200c0c0c1198011540070f00010240c80610703840c0e9a8424500c0354202514417156501d600b0070018022254001c00200350394100801e491415040c0140c1d43c040003001850140311020900008901400001451040c001c00520103000e4415000705400c41c5c0030a03151203030130074410024080c2445d01c54a68201e4001c1c0125108034241034689940303501c1035008481c40d100d000310000d503124510000c1d05540d160384d4050400e0f800e00440003803600050780c944c184107074032007450001c0c1070b03031107100c1c1b858a41160f01000110382d568170125002030142c82c0c4510081d0040c0e40404283d000085030441c80b041c40d94580f40c502c6c07c00801c0842c124003a046c001400c017032000c2e409010000044014216000d582e04e0142d9407484415686400744d003056505c0c00320015010010300401140000c10b52112205942150616405002c8e4160100740c04943e14400c81054100c0f0a80c8440c41c8201d802802030008015602c072020b01d006801030056103040f030202e518210105105 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 469688066 1250 469686816 469686823
    0xa031707051909080d051207090e1f170327030c01031a0d060f0c05070b06090603030d050108060f071805060a0c1b030b101d04080c0f011d 61
    0x608025510340742444030b038856421607030000314045000d10400840014020b20100405003100300182c4d1410b0701c4114525035486940310107090300d01448542002800220b180e50754040d0f00240e031071080300383e00003d40104d02070703442030b5080389100c60b0310b6500d24034001800000810840c201810350041d0f9145515081c108280c613407181f6a4540c10540c3e8000b015803080d0060503d0150320041c1100c0d5071800b030005614610f800f6400c58030301b038880b040908011140d03c99140040c449007803140c5401d1f495030b40d9000020009003014848c8855601249594408200760340e40c183e91813008004658684180b50754038441100c50701d00310640720380010b030340c1407003024080084032510b1036031401181804100003098000b041c2c1042040400000c55004c600c2c1d45212104500c00e22040f049103070b080d4200700b407101000a2040c17042d007a41e103100700705170000305807521000000000407459035151890490018411840321020520680d0307401074505a041d4040c449032145400d042c0c2c001c000c088103591302c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 469689316 1250 469688066 469688071
    0x30f06010c0c060c0303020f0a020708010510050612180a050114060f06030f061f0806090106032304020114030f180706090e0405030d051f23010e041d0a0317 69
    0x2c6080303039010030000c0600842c0b0310740c0b080e4820304000d0f003000b400c0384140000d50000020240140d01c06041080381110030b204907900132415002c0c2030005828103010881c54450a900c024202880174001802041000101c4442040000c02e0342c200b1340d041e051250181c034801d4100074121002002080c000d240000d095601e2120161007070b41150380340e00350b58000b100000d00a640000c4d10301040248400ca000360114200380c55280e10f8a03d081c410305200382c50505800c5201414a46403010f85400402e50034902c5c804078a5000840c11350b92440101c0b8a00d1030240d66420400000c02800314000040a40610844c80e0a0231400c079010aa904140e590160388110000300b030145809124003141c8001556006008408032890858060700c00b030100c440484882c41c0b00c8d40c40540404420300825044401442280b40e0a500c0c107080c4054814000c0710007031040d040c007040310007455040e20b607030300700680c03403402030039480743c40603c92183c16119101d4443c210001400000c0c81c8202c4288034001a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 469690566 1250 469689316 469689323
    0x1203021204110301110a27060207270203010e0702010b0306040209010915031704060f03090302070501030207211d040608120c0f01060b04051516020f0402040f0803030f06010c 77
    0x1000303807680d44504480244034000380341c0554071103010f0413801c1c0d0340307000920001c1d0340c99440d900c08400c92081111600e0b4405d41040604006003020841c4660020300601540c06522002c0e05c540700c1c040c01d00c10966840c4e5418007206002000004444452802185c81100c0b290001d01030f480043c000c05446242c11640250320145140041c4400b00150380411507292540840c6480300d912600c61410a24801140040d030a01c00501441002c0d8021310481001c03c050800340f01c01051a030717020791a22240c0c02241d0403d9408581d200c18480e41c2044110302003140c6400810100754036800810300402c3c0d81410b40c000c50b51406042460400348605000c441d07808000d000c00e80e00c8002d00072007a41c41103014005a100d074040d51900a00207100d500028000d00d2486540c1d685400b0074051040c80c44155020908420f10003c00e0007013000c5000003100394121110002d808581001600030b001c1c40e0018003186d102c00c035000c26403540010045000390007c6040d12030b1595210011145020501c5005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 469691816 1250 469690566 469690597
    0x80303060d110d15060303090515070b100b0705010507031508121812010e06070c03050a0810090603060b0405090705030a1103150c0a27050d2904120302 67
    0x1100800d0707000c1c4071080c0c0c0340c0005020810100c10358544184d410340c000070079076990380d41e182c0810400d40c0100844000f8401681c07901d48801345000b110540e0701400c8409040340c0c0071030740003548296058803010060880021415210070450074064000c0c0f40c01c0715000c010a00e03103d10000400d04805450084420050062402c5510b040200000e038110801740c2090501300c0207034a041d5512071989a4451454800000f050440100c1c154a000d030050031400c14408040d602e0030200768000100e9010300b80d079040030340c1e850700c4070713170081400c21049c0d445045200d16003200030040010305d40048030b924000302d8041c405607c0d000052a1030341c01e41c3c4901c5915a001241e10300000d4203002480501c1c039401401c3d15001444001c0a011803c1d08450b002000078001401c00b28642e008082507208501d401840520710314086440d020b900001e0041a100e2010302c0e140320204480d110000c2c10300d2900005c041400c1700d81f2401c000c090f420681e002ca4002c40b070310b10705008481c400d209444440380c442c01031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 469693066 1250 469691816 469691839
    0x1b1204030201030209040213080312070e010905040b0a03050105180c1c020d11090c1c051014040e07090c0207090203040c0e1e04030f09060806060406050c0304081b010908030306 78
    0x40d0f00941c050210140c1041c7c0030710019a04000c80c084060041483d100507507548c15820b08084424075000b800c41c004d01080001000c1c80340d034007811403402d0781c9090b5070025011100ca400120140c41640c0001c00729030800d020441400b41c6440c003e9048604c1a04a40d03600c12101c08000c2c5515042010101c90740401400e68003502d4020303045900140500c03208081c140d98a00403074200f0303104644041804500103640060f280340c1da1401841c4440301c0d08200140e0801200081d0a41000e100d4683e91490a02e4034413020390300c1d584203411041c46402110207031540c0740c1c260005400040e00c440c000d0302075904005040c20290085900c1140e1140f80400011b0034844011007684001e04040c81000703d42640b130b66000f01a80415024038003076100c03815245280076005100e011582c010001700a4a00180402c4e03480380016901910b0320383c10059241c0c05510b546501d0f501480d40f181c0498884c400344241150398240740840303007440c203903550075410362108002540da1009940c0385802000904a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 469694316 1250 469693066 469693069
    0xd05040f0e0f04122003071a040c0509270601080607050a02060f04030e0301020d05040c0f0e04111206192306010c1401060f0810200a03090213021b12040302 69
    0x31413499642c00c07030624002d83e00304034100907030020302005200300303a40c0001010020b0041c10080b407000c121f450041c1170203603d000c1d90b07800031f81125845200e018107000c4003c1120824a00040000c80c14a81284000c2103003040e1095a90f20083c800d111040c09110041420315210300d00316050140c040c2c00a0025855801d681c80d50f0043c021302c00d60806c598a4143c9006503020300027030410600414010070282400d0070f001c036035404180e20840c403003410100200044c401b103e000507400b41c0c03c883c90303280d82480c0b400440c0c2c502d50204418aa00d0007001c1c20800c01d002910065800100f62100030000c1d80c222000c240c414500c58003040e100c4000a03400a07029610888041c6804e5126803204a070134890f0210017030035601c058008144200c11502c0903c000c403420001440310f110f8601d03040c4005013000421192445180101a0a00c60001908003243d07001e81c2210320700b950701620194841000020002c001d4000c00b00030780751044100b01c1c5000d14000010321601880b94080715600e800e10310790 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 469695566 1250 469694316 469694333
    0x506181e0616020121051f140105030a020c06040305040806100501141b010c3504020603150901170606090106052d0703230a1709010e0d05040f0e0f04 66
    0x104030304100400280d805c0c64054900300b5043c501041c2808200c03810704090a082c68081c0f920611400c2000c81c5003040700c25201c164042d058182803d100303990b600e032124160064810100c1c500c000d44503aa0912003010f07401401001140c8405055950340c0d11000407008039100d451081310b0020701c58400b0f0620280100d8001c000c80700b054201d0f0001140c0050003a0300707403001004501d002c1a49a19004035100614441204007002d5101030b20600440c0b50076090041310103000640100000700c0010424990351146040c000d500800d804135560703641701640e6440007115a0a070990003260b0100d03413076040c00c8005a06035900c03034032900c0c2441182c40700020007609042d00086076140901101c2d4000742e42c0c10003004000c1c007075550142d1160b100e0007034400100d210005002d51403410014a5480c03079200f8410b40303030080441101c095641340c0d20805070150a0510390071919014407040b20b86c01742d4206c8001d204075603640c814400c185503504d9242020070404c0fa01803204982000006d00050f4140307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 469696816 1250 469695566 469695607
    0x3062d120109060e0d14120a0c02030d02040f170102030613050a0603061a04050f010b0304110d05060a0f0f0b010206041527150908160c0506181e06 65
    0x354000901c0108a84503502520f490081d903a5060b040400d41100695100d02c2801d0070304003808030b031454040c4c00d01c0c3d5803038035041c010030400905030340d4412000c02c0c030f1007071044941d100700c140400c1d900c07240c656a41600600c0148a4110a9031510080c40800c01c0706009030381c4210f0008011482e60506098a4070203460000d0100d96480e42d01d01d03003c80043c0f41032045c50000883c3e81305421480303104030140822201c6c0030341801c045103c020010054800420122903110f6031081c07241d282490303c07201092001014810007015030040100300600c4038180d6100550340c40004400344080d05540e5130700822242035039070007401a048000058040b0340c0c25103082c0c400c001c000c20005003004441c408440c0d011301c1c0c0319404262841c480105002d010183e003000f2a5404501c40401644485a88800b514441d01040e0b880030950460118144803c0202c0c1c0d4004100203058280e40b00d4102140070443e000303402006225801030200c01080410b032078140c0c0b01100d005003d20b442c04400200f14101b18410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 469698066 1250 469696816 469696849
    0x509100905220204120b060319020d120207030605070804020a090b060423030d02030a0210060605090d060b10031d03070c180b061303020102010c081b0f04050604030803062d 76
    0xf0040007a80d0221754903401d201c1d070301400c410425800c10804160910410b840503810110380280310710050382e14540c51460351035001603900310f4103088100603070400400342d002401c480d28003001c0001282e00541d0040c4164400c4030681035075a12102c0c1070b01140c10402c11075400c514280014442811152510605009010280d40d5020a0780b80007e180000f01c0c0380d4000160000701d280d2070015010445000444400350040c40803c0c1800c01c002c0070340c010030040034403441c080503141041c04041c0d40304c40e0520b803000d480462101c640c0c160140150405003a02902801c00032501c0840700008800e4405072036000c070070016040d00e4007500b00c004d550070780c009003041691800e10b1030940c0c0e1401c0044c8200b440ca100f01350402440c43c000a17085070402450b6806100c159401c000c1601100400c02c101c444a10b28079640320901030a42000602032500107039000000010040180301e205405588210400c6605912200100c400714106000e5070b0402d1041d000745034503400c0076203004200400904030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 469699316 1250 469698066 469698071
    0xc120319030b1c021e0f090a0213060221041a0c2503060b06190305070e031f1b02070303030209010c0f12021e0a14030403080307050910090522 63
    0x745500041c1c80c020109410010300d442078400d010850808030803220031211905c192040100384a4080343e45001c804003103610996400c000600c40c0c0f013a80e07064550358000400000c4050b503c2d00d0f00a50390b001810445152070b10341000c2c10701082035803002c07141070b82c81c200c0d844254861000500c2400303800c0090f485115020f4000000183d030708031240c01c18100070368100954607600d14140307002140d202c0791945024040800001340640c107041144079000070070b8035001540c0c0d41c942030304560b0842804007281d03243c0130700c1080541c400000d519800603021504000c02c801c51203840031903c3c40c185000101d000d0b0704043c0c0104007080c041c0e409001d0404041c101890030071103540da40e01800c40450030856032001c400200c080316650412890188200d1014646801101c4072143c51761110420001004000c1030105044903941c103105503001954810700c103075102c1c10410006099904002d083ca4010462003c01e002041d00c10710303480040300c0d00600074070f2100f060b01105100848a24080f00c80c100c1c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 469700566 1250 469699316 469699331
    0x3281b1814131b0804020109050402030f04022103040b13080109050601170115090c0f0801051309050118030504090b0303130b0c0a050d0504062312040f02130902030c12031903 77
    0x801c2c1c0f0a2420210301d648000b02444c2610000d13042c0c40180d00b109020740e10504c204142c004a49040383c2d0004e4040301c1003001c0040f00090a1900c842e149000182400b0100b40099010844006018150300182d40d440f02c203522103a001d4202c4034202030242080d40031900401c044030910b080800000d0300c1c10b00100d0030003d8526840b140c403145030301c056100b65541400392105540182d09a05890851030b0030384042d45413a0004055041c01950302080135660202101000000d50141c1811243d41046240340700711401c0c00f409c1782d04903104401c055424003022110610300841100d61a008000c50800742d6810000720001c06c2d0403042e02c0780300c03500c100304580300441c0041000c1e4100629030f0ba10a5501c5052805c01011100c40880c400500d03000103010039410241c0c0d80c1500e10344101440303945003941d80c0307081650000c0d48010010f5000b804100700b5051803206a000801054003d40807200c0c071040d0482800310003060080108140e400500030108204615440c055021034680780203d10b10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 469701816 1250 469700566 469700591
    0x70e090c04060b04091d12091f0e09010806090604060207021801170c040e030706150b04081005070e010801051e030f010c020118050303281b181413 65
    0x1202c9580020340d035201e0100702040103080314003540e0150095a51600f04400c45d20350515580c120741300440d640c69a01082c0201e181d11607103c04d8601c1c40303182000035001c3c481810082d04041c020b41f5054040d074451000858241d000040c40b601a802070002040a039070389845560080d00f010307500302d03030001880426800c000a4116001d019100020511290304000410549003002d079203056070050703081403c5174602d110003005851449070040c401003040c81c41c85000408183c21500003542c60f00010502040c000d200003810812403654500400490700c4000b4141e0b2510f000ea0300c5180000c20140042c0100c0c10112041d0b4804503840c50f0440302c682d000000603007082c0d04104070403416036407046052504e030390900568255490762000105031500c0382d00e6050301c0c5d12000b03144482043d211341d040e404a64210550031401403002404000c400b545a4020840b0f441d90304203c400541c01540c01001003048800d80821284003d00d5202150100c00038082c042514151200c609940c54100d011403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 469703066 1250 469701816 469701821
    0xf06140306101e12031d01030c0504090203090f1606090605090609040917070807110f010c030f2006040201020c0f06040306180f0c030309060801140f1306080c090c030702070e090c04 80
    0x685200352100700a014407540031164a486c841c2055042505200c0c4110b600740d0024201c4090702c07002030001d41d80340c0c7c40c03800c41d03071410740b145152a0aa01c00c02072480c00c4181814807020542e0801e80d11290030a5607003104807098020003e040798008810040001246001c1d4082109030b40f140398503640c0c0c540d2641440480303030400348055a0310400094a10b04002c0000c24402148000315040c1c148410040c0000700107001c4020f001702405851840742040302c1c010402854161030800e2001840309801082c01d8032103a040d00c1c1207025120308940c60311240780c40644071700c010070301406090400349580c4400c4040d248550300360587c48451070500c0049101d5800080c1c0c0240500c207004065403440c40e0003404031340e643c0c0c800020400c0c07034001400001d601c4002038168580c21104881043e01c0e400000305a4035100300020440b610302100042e4004003c100d044010100721240000c07a542c9a408512500c401c0755a40c0068000e4413003408103140441d0750f26044141da8048074500c03100325020404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 469704316 1250 469703066 469703099
    0x61504090c181a06040e0609150d2306040201020c100311030901020a080f0402030604230d0207140103090f021504090906090204050c07110907050705010f06140306101e 74
    0x844036112000b03001080c05034103c50010ba10182c038410b00c2c1c146452500c02c04040c000c0c0c8a2032103480e2540215908040c07950300c0c060900402880c400402d00503103050780180c59015031103002c2c05a16003500e42040004900705101701d030185c0140190071141410400b1003c100186101890b68940c1e603000115070340c5d806148103601c000e0005035609400c00703000e41038980041c101236818040d01d04000050314007042e01d039001544503034418080c00f0384048560121100315850b00c018441c0c01c4c411a4070f01d0340010754504580b140b010b161580f8500c0b0004409135803501c0b0b406080c52029409500040c1000040b607100e01d2141c0c450300e030910361201924402c1d03812000d0169401e685803031004055180c18420260000d12102080385030444a51f560003602081a01c06803092211a00242006014008447c40243c0c07102c0200002802a003400c4020505806002485011041030703004d0780c100000d146000d0104100c03440c0c2c0e603920742000660484c02008400381c415200003000203414410a45014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 469705566 1250 469704316 469704359
    0x91f02130e0c04080c0303041a1c0203070201060501091505040e180a0602120f011203030506031014090c04060810020304022724010c0803060d12170108061504090c 72
    0x50f510361a041c203c910b0032480d203244138400e070410031042014080b0f5645a000440c80c000c2d019851b440c0c0c0844410f442c0c1c2d01c2c07201a2868900010030041526419401041903441c01d880e02103480d81c82d000020802081c4215110102d0400c0000380301040c041c079a119408203201d41240b9030600700d01041410406103c84c11282690089039a2424120001401da0310001d02820803170301e5850406603000d00f9210400180070b050f0f50f0808919240c805000769105005034400511001180b100c0e84000660f00722a0401940642c1214020740d20f054084d0600f12391801d40201042c43d0b820b102c2d03c0003984041d10407130307004056510f2014038400e00341c04509200405120b03c5503d1400301c40c8031016048d4408000c8100f10401008001c0b40c0c0c02892007404103821903516600ca0703451801180383c4c00141c0300007400003500d10b185031041300d0b4407240081c0140c04203407554280380d989020655540000340d54216040c081810f04c0405130905038007540006010320078540000303503540c40001320003075a82c0024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 469706816 1250 469705566 469705591
    0x3020604060f030c021c0c0609080316020c0315010e09100504060606021603050318040e030f2206080c0c1e011514090105011809140708091f02130e 65
    0x1902c415014412001d02c60b886001400c840c0c10384071441c19102201c80780c02c2c03040c090400c10703036002d00c1040d51040c84000c0d4418130311a83c3e41000080003104050400804005101c0c01e510080ca600740442d1b444182c0d40ca030840c004140e42030081c03000d007941c0014030302083ca01c100307500800428981c4c011540554058030b80010400e003000d800a04050f100b0390442070443c11200c042001800001c201c1c0c00303240101c03ca2501e4103c40600090242c242c0c4000c40302c2a10012443c0c1036511205401400404418030248a10b0b010300001c01d599241c040c4500c00105411000059110300307141c008000200c02c0b041130311130040c1040a44050019070b840c0300a5141c0d510704081e6458180c0b086500080c0590200442246140c040041d450740c2c014024181008016060803c1c4c506100402801812060f0b030140440c000c54424403800d0442160725a00150120010a818030344c045100d41010141d890034a541c0d020011011000c2e6100e403120709031041e2001000104541c052034440d008030106100d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 469708066 1250 469706816 469706837
    0x30702360c07030807210507050f040306050717040803010b0a0c0203011a100c11040c0207050a03051b041a22110304050d0302040503071406090d030e0909011a01080a060302060406 79
    0x1300030f107a00800c10404d1041c441001066400e01103004c44030000a4000824580c0e50f20500b00c9031801003d66040c902c0f400400c0200400c075143d08460720aa00039034840c4034000680c10844650401500c2c040c041c00c03030402c010301c914501400100040480342c10300413850001540485d08550484542100c0d0325014a840c45aa143c0202003103406205c0d4134240c2c404a0068036842250b04000421a22680e65a074480c0c00480c000d001742d5005050007044003000717a0b9070f814920f8658840302108000320b00417100e90780b15407400744140d884085075940c4201150415600303002c20b202e080501c251055494a49915261a050041c004200c04440c12203480b0f0405207040b914007114268080c00b0f05005100c1440789440020f486012103994803604044130000c240403405038861701c0711050f003100b80d25040074240b540000070041c0c4030b502610341a0a0740e45503a9800d088451002e0100c2c0a41008111a07640c0c0d845045003603006100c400d400207020b9540d50000f00d459105901c09000b18800c0d410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 469709316 1250 469708066 469708073
    0x5010c0908060c0a081305150109110a05030402090438060406050f09280b0118051011010b10020114011202010503010501051b070b0417030702360c07 66
    0x40c44009040a5005010301d041c40043d9102502400030603030100304544002581000c2d01070703000b035078564112069030941c0594201c0c240041d6030074060340c04004d04000440c4208038091040781c07408901ca45d01d560942d10349600300070200e0000b500c1500e861036416205e030030580692000003c8a5003100c594035409040e00b008290340c0000900032231241745402e0042046444d40403490364016003c0300e9078075a941da40802003401594104102c08910b0642c0d6080c840c452003544840e0a903082600c40b244d41d0010344c2e6001440342c141e8010540c11000040744940d000e402449010040340d80724001181c2040c0210208440c482000359060042c0e4441a004c050382a11500141c054006000702c2403010307840350006855448103100f0281044000281545c0c03424014003040300d241c11403820b89501c0c0385e5401c1c6404058000340180c800c018043c01080d00c000c040003046a50590740604182c5500d000b003203d00c2c2c040c020502501c5001001d03461400d2200c02101150b038444e5144803030143d142c402170704 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 469710566 1250 469709316 469709327
    0x60105040c03150303030c1407050a0c0e070f0807020f0303161e05040b030a020d0921030213150509030709050103060605010f0804060902031903050714010c050d1a0a0305010c 77
    0x144001c0905141007500041c50b480740d4040400d980c0c26080200b400c0ca03d90390121035119032101c0241d40c860b4003017000300400c0b00c08103466040f1409420020b0f000ba40790000a440744405450301800301d4401c28002c103109000d8003150b9403040320750040d41c4285c40c04030000ca081d5803044402c051415a002e0351040320300e0300002c52106420000900c3c250700c030040c0318042c0080c800c0707003d0440b6144022000a8401c0c689404031a400e40c00c00708240848216803612081a00c982d030903060800003e11132450800f4880d1095684007515081c01112007440c000c19012102c0c002c6841c0c00401c00100074462681c0c07010400a00241000100000d6644c0b460512500701c1c0e4a0b034001d42d040200e030b919072004180e80b201d0f01c60741164108600147e0710f200b920020b8500000b6403100c901c41c44071164141d017855000000740020074082da02a5191680c4600981d08071140701c01100d0125030144045807903a40d042d07001c10281400c55444c003030600d003280005011044640d0080f0703203603034407840201c2c4503e0703105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 469711816 1250 469710566 469710581
    0xd060501091104030f032d0203090f032109040609020c0a03020c0a260109140a020a0905060d1202031309240f1a0d050702010e061005010f0e0102100e06010504 70
    0xb007011508003420356581e109113282c80140036040250a80303510050765915001c0070f90f1000031300001308400d2540e0501075200d400110340c80b4401c1101f11409009410f010803c2210391702c1e10428a00340e1850300320362161070741040d4000d940055843d000407910851500c020a0420400401000126401e02d402442e00c1c1700f130014540100003000b0100541154200007407415811603418003075100c2c213001902d0042c20301e2032010342141d001d4040400c4140c0082114080f850003541c0030307100551101046000c0c1c544c16542d003500b040107110900040f501d03481604c07031400800c0c41aa840e200e0f043d912510040d0854011450003581c450001200e40b140c0000002c1600300b42c0c8108101524084010240c041203128075000d40d00d003803000400b0b40c9110401c84141e040501020002810b00101c020300030489a40c040060b4813503c1e0100383d0040e18550300300708883d0160345250302610108400c403008451411001d042d44181e50040d00041c4050041c0c450024042d401807885601d0081080143c1c4d480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 469713066 1250 469711816 469711841
    0x9141603150f0e10021c060305060601031104030b040b0f09150403110a1a010f0b070525080607031e0903020a020409030509060408010603060c030b0306070c110d06050109 75
    0x88020400981851441281d5100605000656807034a02c101c1000d045645041d86040c040c010901101e8029030740501140303d07108400c00310000c030707142203d42250705a0001501070307403000c00064020740c0309805c4003a43c1019900190b081503600d81e03494072126001d550484800c0071040c100182e6800b00c0701c0c11640545140c00502c070600780a0a10180044060005001c100d8400c00d10a000c01041152100c0d20354022008481002d07101c05200c1032690a0003000540a0602c0002418240c0c2c48151012550001c000d0161101c005884040705503600184004040e12600c00203884403042c01114854005a1000710b64071100d4906640700c05c1b50094660302300d41c5441c1c0c0140c04260300140380401c20381c0c150f4000a40c2d0109080c11381d03031401810700050b84503074000780114010740190841340889100c1c0c1801e104c50081d044090b13041d1054902c10603019401800000c203000d110b07400c403085160189000c5040b103031564000c1110048402400e45010b5111001045881e04c58820f400210b0403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 469714316 1250 469713066 469713103
    0x306090106031b050918120c0c0f01080c1c11040b090109170703061d06040c03050d171f030503030c070309050d23030405041404050c010c0b070516060914 68
    0x6040004080b0b06002c6c1c440007180c0ca41c42070800c90090704002c1100844808540b031500e5800c2d99000569510b1414940c0d8000d07828101000181d500518403540261021041c160900d000f08000c0d80381450310700c81c20020741e82c840c040c0d00444400c01c5c0051014111150455035103d07400c1002410440b81da51040c40307100700340c888044020902050550580b6400300700400c0c40004228407001941d03d00d1144042809418103200030005082da8840c1128462800d07558601115002507500000740c90458070040c403064001480041ea91402406400e40202a180030b1500d9484007403841d00219481c024000b00021400e0034150818601001400100c2e44e049025005580b644140c4820000410309000000b80a91791507800b4400c0d64007500b0301400400401d1801c800340d044a11050304c040c0c41034051a49902c01c42d5102e60758003030049800400d60815521514011181d0f86d0001e58040b950400341c01040c070000d03e4034000d842e2141d004440080c044c0103595200c50408000710151f00302c014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 469715566 1250 469714316 469714319
    0x5310203060718090e160e091e0f070303030f0b060301080318010c050d0309030f080601021e03090909071a0703021b06161209060318060b0f0306090106031b 69
    0x2036000a0312648808076103000300f001400d01003603403040a107a40144804a042c00c00a622a250026907040001041e09100507540c0d40e0350052a4808404d0b1034410785a000000d03102c0c0502610031039400c19034180c0c070858442c601c640310510f09240d600c3d0000c0740040d40341c41028220a086004140d00c101c02181c80500c0c5500d84207485a8074440c02d0083d42220310101d0304500c00d03a002d4408801e5a076000400c0c2d41c2540c2040c0802401001e0511048020840c101c400c0203c00d0310a60409100341e00680060415995554101d210120700c03059107684d5210401203151907881c0e2285441c000c0750558018610581085030a50b41d42c408904910f44000701484444c0200e58009201c44041140c030003a49008650827003c00d106208140100041e00f228003002c000700115162034100d0b1200d141e545c03044160302d4000440940360411203015140c0e02c40d0002c2c4012551550100c03c1100000346581c40c8890000f000c02d0034000e0448102c00c0a95681c1810070600c20f0854200c5812484108182080b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 469716816 1250 469715566 469715569
    0x30309030601090506210606190b0306121009030302190c1a04020303120415051030020d0c090c1806030c0c080c0a030e0d050309010f05040306053102 66
    0xc1d4014851100e916480310701080c55510361000007249108004a00000340c200381d2083d694694042e668a4000c11030f0325151580e800d5401c50b0b50003950b01098196156465290421044640c40d0325245054001d014440c0d40c1e8001c64810142940d1180d18003684510202080400030b1407a0004502400381c48000b140020300700546001200e60319958070a890303211800442c3c40c500601103c4104405407106100034040300f03440c0340b601d44285407018811581e0b5804850400101481003044500e406100072410740c2d00840c09002240810b4581410310302d442d0001074001c041218199016a11440280400c04160159499503442030812081d40c04120300ca5491a14852060704101961201003100540c4290140c0c44020303000b04800b6140d101740724100b600c42d002602c0c1240403888101007803047d4106101c0034071003503420401450504070030800548001100c001080b042080c100004000203109d8400e02d800350001c942d0b20300b000d240300c03501040600310340352545020300d0949a522005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 469718066 1250 469716816 469716823
    0x60604120312110d0e0a02130903030905030703090f09060b0409050408091f02011d030d09031b051501090b0a050f010e0a12020103050c19052a0109050c03030903 71
    0x200c940302030040000c228142000c580010110601c00c1505080444a41012400c803001c0c022080c0d01544c20810f100664003030640d41c03042100000c0d00f15000311281c18881120340e00c0091030034064100414006070554406041d94072100045001c111800014000601c035650741c04040d001001080103070508142e00407400b0302030b0f0b1058082d103646a50000d401c00c80c0040c1681c040d4000130300a11210007500000074041e500b0810b00f0401986850700746490948940c07403180001c40b08001542c03502c43c124201c24081e0020490079800d2003a044501c0081140c000340c542c10090052020f400ca199182c042505000c8061340250707001402c003050401190380b040c0303c507c11600108e4006d09441402001a1120078070101c001d60f00480200700011789030440c03824101c18a03c00d076000c100135a01c003142d1078100e015403000480300d04044000d0b04d281c60b014100820b640a9282c100c1d40340507a101759502560040c1e290b210300c5d565180c0b00884200071003000303a00b11000c07084014500748401000407994 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 469719316 1250 469718066 469718069
    0x108060c0a030f1802100f0c02040b0103020702030d020705040c090303050a0f18030503070c1a04090203191d0d0206071202210f0708010b07030e060715180b0f060604 73
    0x5540400280050301d1400b070307030040c0780c24080494188602500c0ca41040c001c0350034002c0c260701038070b44040c01903280ca02c0b443c044480d0100302c0d200d101840b85141c0920008000b400d003d941031603400c2102002607602009585c3c1030806030740c002c0039094200401d00041d20850304801041c404140c5051000076086016202c4401041c039040b100180954000c98481070040089086061300790404014000040000c00040b4081c0c05046209991810180322102e034840701c4115016062009105581d6a41c00a54200070307126210f030b08040c00c0d01c00c2c00301102d009a1028200300c0c85004036400142d4180318184c0d07841130a00140000b80b50508015000f05100081000070355030000c1d40c00000000c400c0c02c1038918408202c98026071a007080914016071041d9aa036000c03500c0b100c00001d510140c41c04885038154142d480ca2802d240d070700140203c41d0005e4074100e0b10b4071501c5c03400b206800100c0c8101c002065030381000440d49001c504000d504bd50340a001c104041e50044100b21440d16404120350 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 469720566 1250 469719316 469719331
    0x103080a0305041a010807061106041e060f060f080f010504020a090e120d021c090c03020409080702120c2803030c080f0f03010302011b020306060f040618050f070206010806 76
    0x9081d5528070f00b0b8411190245500c1c1e01c4c0640c03410010503184c000065400645100e601c80c5c40b240d044504a180d03072685d00711030003000c21040035002800c8546019401090a209131008290415181c10304425200ca942240740e81902d604030401294408006e01e908144c1d071903000308081c1c14070345c0108800c0768035030040004035625010a070004040801543c0700141285200b25240c980c0c04072003a002c1d500c407503c4481d42c0701040500d440e0044c0a4880e81c5001c50340440210a03052131503080c4806070280c03080540710014144521005038545400700c164140c3d10b40003402500064504120002d64900c4801500105600c9031302101c19030071550000b0703260141440d03521010b2519004042d441880003e00d0001c0b0040341c1c4c40e180781100006541600c3c401d0300c98840010710313002d68001c0c06851142c007035810350007100400e0041c105154003180f03081010740045111354481d8011450405080c2d00c2c195255610f0701000142c801180100c1e0304001540701a021030b501d450901c0303984a50140048 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 469721816 1250 469720566 469720571
    0x11010807050702010c06180f06050a060501111b130c08010602061003081b033a050919031202040f050405010807051008070e0d050f010c0302191218080c0f060103080a03 74
    0x414881f80442c1d620301c2480d44180b40742030010030382c90070101401c82940c18000d102c0c02d00c0004200e070360003404503046d0200000c00030036540c01034010f60132148004101d400d8100d070445400b60394856090080c0700217502540c9a20119500d050303030081c030385900140700e0140200c402a0910004080100b2141d441090b8440c602d00c6c544015109829840703904402d4030640c00400001407520307281e1a031100d1481c0901003940c2ca086c0340d0843c0405480041f2230300c2c0711035084070b01c905111f080650120743d00140030346040c41044441d90030b070000700d92264100ca03089100280d01003016140c203000b0340d40940041e03806444070500d041d001c50a2000700401c800305000c84d44000500440c820f40301362003166801070502c0300710352003401c046840c2c4512181d445019401c7c4580005000c1c000e00844000d14000e10011034014a145400c85d10080c051b002d14410039120300211000d8040c1280ca41d900b1809490903e0f6a2400c0c0c00307c0d103143c005001000050b6401043c010404100964291002c808090501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 469723066 1250 469721816 469721831
    0x911061306351e06011715030609030409110406140f0c010504080c2a010513090e06060109060c030c17120c0903010612350711010807050702010c06 65
    0x684010038610b00010704540003201c030101034440001d02d20701400200304040b2400b002031248100401c41141d43c0360200b05040110019001031034262944860140b40c020074502c9181c0000303007015025100602d40e603001160510003264207100d02001c100300c0e010ba1901d0b1a00c1c0c00c002a00807510428080880d10f0080707041c60f0109940c204507100505000c00170002482c0c50f03c0e00d6420354012038042c038001d200c0c01201288120380381c0220107000980913200780f84070031004011a441e901c0076800305547d03589c894001580c3e02c528064282d01e400c05401800181c50058001407180702d0b103900c16004c0154894140000c25000021001031580145400284c114180c10302002c5c1e01c00e407107103c810040d40c282080a0701c03144002034090320408500a00410f550f8000320030315048146405007a048500b160620300c0528018410050b03c0d407138050084441c50f5020180d1260404001074032240c501c00f055140039a4000781c095481095414102d06103c199000203001200d141001402141da40320b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 469724316 1250 469723066 469723097
    0x160c081e10050c0d0612060501050105091e010e03030c061503031c0207080f03131e0b19200729063109050c04060b03040305091809010911061306 64
    0x1103904044004d03805206003035540c84000e012010030042a0340d010714140020825610070030444042500051003000c243d4100c908501c07042509200407414072421020190581d2014400780c106042c402010f00303040d150001c5260f1181d4040d8008034400e410400010301c1903200c070084c0041440840c1401622841c0c40d00c3d02c40320301d114010354a203030004044100540108400c440d00b1030721780f0038180190135039044a013901c031a1203a424000c250f80100400244d41410111400107071080404021400c54901c0060b400503141e0900c40c54026040080c02030700307200010544410043c503140e0327551100e4070b42e00c1c800000c40c040600f82910075a00100c0320300c10f00240e1500070380d034148044689019040d40c0e20b81d1600a103802c0708101c4640c05030043c40c020b24a041e00c10001101c0803012410b29640d299a0100c42c031307a100720b90440d8841d0145000d6a1410700c4a0542c9100b0301750040000b9440c1a641410140300c18940312107440ba640802c021060f40d650170503140201c4607903042404000d0030419 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 469725566 1250 469724316 469724341
    0x50c0409060e180705060a14040f0e0a050705182101020a090f0b070302070317070501020708090f03010b060405040911090406021b061308030c160c081e1005 69
    0x20300100c402401e20001264411501c4a03990140c1004200343d18240010802c490300c68026115056203c241800544d018031300424460f8100c54204c20a90301c1c00351601c0c40c0c5d04103480c150304005042200242080444107480c4201a0460400c0c20094141510071802c00110998048142c0c060076580300c0311200180d80086414070420035200a545628025800526151161150f044100741000c000a690b0400c0c00c203c42c1c2013130b003560140098505603141d10b88040c03502d090511b90200100312100110b0000c1c4090002c8a00c141e031010b65441e44c1c0300402ca5a40d072400141440380c0d00d07003c4407440356603d1034201d80403078405a81c0810092103505180900d400c803039050507000020482000100040d5600070301c8008501c40e080101d440fa807600c03a55448404880310141000c5607038036a030200f551b29004d90340c08144440703d00d1030301c2d80124641008011140e001c8a61003a10780382401029003c1c810a0107415916499076000000442280c0c1d5410040340c40403e8903a80c0d6011400031407146 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 469726816 1250 469725566 469725569
    0xf0d05150906091911040b011806080118050702060a051005030a05030904050c0f0306040902060c0102070b090d0201020a081611150901050106050c0a02040f0213140319080d050c04 79
    0x195400c8091511a10142e191202280c039a001800303115004000c00104030190345201c0d0300040300601300c0d0b205106200040c0307200101e40f418411003042c20390900c0400350240c0080e021682d80c0d8500c03545400c0c941d41c0310310b40940502d802d00741000c0810503100e900062455104412020204603511429103c0e110507031035030006a01402004d280800703004000004081d0a03200395010040f0340da856210b0205401035a411030300e00f81040022944500d40703500040d1142d070000309101c2c41c0c60b810241080c2280d1240340c0131942c441421081150800c01840031229400950000b5441c2035440a0300500004006100b00503102440398444101841103511003d2440080c044924410f0960078003d12903404a60040c081d40c24031002050300f511a10694410046500081410001035820400580100201c000c07070680e082c801c0c95170311000744003c0c3c1e008060708540c51250948400a0500300600d84a01c7e00168080c4201c903c0052294030444510a40903800005e00d61a100300d404038901c02c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 469728066 1250 469726816 469726843
    0x6120e10110f16140a030c14011b03090201092102090a02090406120c0f060804020108190203160806180103020d05030408010908090f01080712020a05070615150804020f0d05 76
    0x701c3c81507088551000030b400814041c15500344880c01a4a026680d10540303000100014551100000012144804244040c5d503480012804514030344030044e94504a90642c40000e84420308c4405550b040a4800054103d0805017403030058003a00c2c60000080302c00009001e6490300000401f643c580e0360558000c95402401400400c1c2e0702e8005919140007080241c441240c101c03400151129110b08200c21a005900c4e0060180d0f65070700151480c0c0401030102150284000020034111121310055100c0c01c1c51880000e2500c034810343c01465018020704090107410048040300820000307001150444c1c0d412a90380a45103071a140250079402581e00018040d03003049480710400c0030a5000c1c255200060f0b9003140c2c070642120044030b0200040c0c6000c80410483e0741d2084124610781c004184486e0705040c980e10b06401541e60303008581c015919044001d81c00c9a05102c50700035206040800c02c41841c001049082640008544a002c4080641f00d00100358044040243c18072100c0c03a540c50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 469729316 1250 469728066 469728097
    0x130804150207050a0801020c120f070209010f060201060e060918070e0f0115050a1e020a0512030901060509010605040e040c050d050c09010b12150307050a0305030406120e1011 77
    0x103562a0103591400b05002d100d1090b01d0b015808950904140f0135a00464a5500101480062041d014126601800c1403107103580301000f1103c05611403d40803402002e00103003101e022032405e44002d003192529000084036103a280e0038000550b4800d0f50550b040801b03040341c1051041c00b07244951520302142d00000e600c0500500b004616030713505c030003581201c41c640041da6140c014000c0440e01c0e48595041c60003c83c5046030022441c04448821007a41d5249004450300000f00b611180d1410010102040460100008100030741c0d07800e002d2040140810703124100305504144025000f802180501c0700c18006040005041c040c5403640307070008100103407200702c2d03460150800c0f81e2101840c405460298460000008250014508403401420403054284250303c440c000c1c3c1300c0b000105280035078140700700e00340420759546610304030300114400e034003c540d610314004000d003201141c5066800054a81401d001c1000e8010a261115420304440058209040030380d5681d580251800c1082402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 469730566 1250 469729316 469729349
    0x10e190803180d0e011806020604060e1e1b040e0a080c10020c0a05060610050904110705150907050a0303202505041d030f07050a08030717130506130804 67
    0x2030700030f4880501541d003030782c0c0c1d851950b00340c3d1b0408010408901c210340050703000500040100d8200d5000f15030030100a030550f0484c400e1585140302c10b0042c4060040c0c540c1058610070030010740c00706d1890290303400703070380034000100400038030307601d401010300c02800d002c500003a920180802800b00d50030320010150115107440005030f00340e03982d20703100302e04440e58881d542c04075a15142001070b070703a981051a80c8251401c4410390500007e000601c004444840c0180110f8000035024061028840542c400c0402c452610141e02c6250010303a901950082480d10400c0c0301103075215058071070b4910681344180001010305610782c9000003284036a030500a400600c20142d074030f8540c0440445004550078048003c20322001310500d0901d410303032200c0780d01c10010b5150741082900030f8081940510b0540c1c9401d11541c0b200c00840c1d0044851000207120b5607123952110480e032200e140c006020207212001c5400503960341d6aa003501070510140314040031704000401c050b0390f040328040c2013202ca01a5030344 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 469731816 1250 469730566 469730593
    0x30a06080d052208030d02090303070206160b010e0609070305061906030e01060503071415040e09030d05150a03060e3c0d1403040804170d02010e19080318 68
    0x1e80140002c80c2c0c0a10f800d0300100c3c002482d282401c001d0714240800786182071b60303075140080203520031104c558041c007091142e900560b9950002d080000000c55607807041c0103051906661101d4141c00c0340c03840c201c1043c01d0184a03121200c00e90303800009400c00080644842c800280c01ca28400b9207141450204103000c10100c0c1d040e00100851040003000340b02e040e84403c01c154036400e0501032208002d01110f492a200c1c0342a0002c1c42c8400100b1070340c10710b001d48640c8440c0d0f6040086401d0201076200245205203013a40380b040507407100710b16080494940c040c00000d654244140b102800a81d1a129200c07800d000500c00c05c0400c481c844c14015101555400c488020a182a00f0070f1141105d0303d081c60540b02c001c01c01c0800301c00c8035034621400340020807910349030750005007081e41c0c00b00b070030f0001082c01c10710701069640f1164181d009080b24486070400909450800024001c02d07000500504c2d42c01e00400320f0680641d500c00c0c8816102c0c0d5031851000103603550300305409030728498101c0440b1207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 469733066 1250 469731816 469731827
    0x110c010902040513030e04050403030209060c0c0310090b190204051e0f0603040b1b070c03060911010e0a09090203101514100818010b040f02042d03020105030a06080d 73
    0x50520940782448180d45280408081e002426000b4000c991306d996035404600e46507109580c064480e050040c20001020042150794102c0d0606d010703194001500c2c403490340f6040020301c0400e50105c10034008842c00d0b5840c1f0400c0e04000d050002c44107a030104c00104204160141d07400b81c1005002248179495408034480742070503000e01e180c0150700348451248241400012680303e20780107220303c042510f48083c1c101c00080c0640f0991a00c0303030180103500c0050790003803003640154042d03a4045850010350038010343c0500c81a136128180080c40903000b0b5070303803200a81c030b03022500c1c00c0500240101450020a09024a0840c0f841d00149000c81c0d191206503003440d80740a5441c1802e00c40580c50064060114030010b1019850110f03224400040d112015844001d5046590400225103501c2080109007590030340c0303800a0304071ba00410107209140d00d49980141e00700380c0d101049c1c204208694540710300425400080d0410a0000019490310502e0b00003200070720011084031040d12801000038607 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 469734316 1250 469733066 469733081
    0x60a0302100c0237030b0c03180a0320060103031b020d0c0e1006030c09050f03030c101a15040e06220522052509060801020331030c06110c01 62
    0x500d4910054404c80b101d8002524106030380e4440f0f604100b03515180251584c070740008140c1443c025101c005c01c44503100c2072000991051090b00c55181d0707201010108858150140a090b1443d80200010400329903c8046080950510100c1042c4003080b80089409a83d40f07003405002c010707023440c0c0014805121450301d4454a4402260707800325854078012816100300e4500030b000911801002d000615040c401606803c20080440f45002d0b04d095501b07040107441c81c1e4000080340c2d107201c0300110031407848840d070781c080c4102c4000d054006948920b81084c0a98050126002c5900c2c0000c1c0040c0c542c603070301410007102c600c0b6202d03580907100ca040020341022100b1071003d90481000c0a030140480541e044640c0d800400b600784000c0c120000303401e0302840e408004c1da81c1d95820000481c04c0c40c6224000c0075011000c0003503540c0c5030410503000404841003910131034403400200701d6256030201c1840202c0b1a4146001c18518490781400000792600d4500500b42107000201ca020310300c0158031240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 469735566 1250 469734316 469734379
    0x70305010e0a2604030615030b06010f0203071b1701050105130504080a0e01031107030816020307031b0501021209210405030c09060d0b07111005060a0302100c02 71
    0x14141c001610603441e120b11003001400c4140100a84603054008000d45041040e82c68507142013540e80d031650740550b041035850200c0d040004d00284103025103180083d50204081c00d10b6940c003030550740029502e1044100181c840c050788140301c0300101c1e5460224008001c50300400000f88842d8131094020802031007014411344c403042010312189130a00656120304c1c1c10500030341c10000b01030030650310105079442403410959280070b00320000700300002400440b40685e4409185141400c0a00c000b074410755000c8080d07610901010300043e81c006091003500c01d1009601d450101d00e031034400c0c068002c1010702203220682c0e1041201c040c0b000104100700000b2401c40004035504101c400b800c40c452401100d400d608084840c0c41241040480c5035000b02c005040341008107003940b02e07084815401d441c0c010018083c4d0084011003001000860b0403400350b05c00410507418503030f000500a104601c0300074003501901070207414039806400300c054416000b410140800c0b45403003904200044158816 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 469736816 1250 469735566 469735571
    0x52209080f0a020607032003190509011505060313120903051e0c0d0203071e090c05041d01120b06030102130803040915080601051c08160605092b02100e07030501 71
    0x10040c901c20b005807d03203481c024020401401801c40e140002c0d510080192508881e681042202e00c01d1a100d8140b04220104c00005e018040c801400b02400c5154881d0340300d0071081c418040ca0245000100c40f401d41d00c41c6650350b00c020320400984190300281d101600b140106150703800c0450a00c0900840c0001c80c0302070300c0c0c0e0b024600c01041801d480811000e07415511001d0705010320900741d0010540e0300184103010321071b19625515202514400c100b081e00289022404000314a1080003d0322411100b41001d48035604010040801c507d501a000d032081070030001040f00c6890a42c1200d45003016054821703440303a02c41e0300c2c85a89900600c5004119071604013840e450070f210519110035280c080c8098041a480c2000700141d030411030303840d810040c14071451030000441000c010900c02d0036800c00b00c020404582090b80484400138414103e03500040b0529001c4200c00344141003560342940e21000d11000002c00320f1030304150b064000e800c540b4003604804000000101d020444e84140c009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 469738066 1250 469736816 469736821
    0xc120c0a0605010b070f060e10060807080c090112030c0f0b1006020c0102010603150b0a12050604030e060c06060114130b0702030d110601091a06030a050907090501052209080f0a0206 80
    0x1c404245c49400c1000e4000d0b01c184c001a00001c3c4503070040100e1a01440032103c0421210030039408481e040c2c5d10028840e444544100075484d400e1000d1800d03800308840a007010741c07402c0802c91390201280c10040c20428440c0140c0b0422034a50000b242c40d0303800804401c11031400b10704807580010b040c054034001d88509014142c82d036105020320b20a99070302c9186103c000e07600c415800054605491203941c4a422a01c0115101604031184880d86000740300801c20781c02c1c1401d0140130a60340301c5010b405850100024005000009889030300501c0a207840340a8800c0c803880d038940c1d03004000003140041c00701080041c04150040103408440e000724155200b13482400001d56040c03003071802c44012038001c01c0042000000c00d6100c07401c6405d111110050400e9081700103207050b482240d440c00c1d00d03a030398400c1c07108100e000c01800300a408030420800065060900041c480c030f07015000ba50020410240280c90041d540e0824880305a00030300e00c5440c0ea08460b060001900820743c6400103200b40d800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 469739316 1250 469738066 469738079
    0x20d05010801020f070b060310110d0c02010204050a050108060103110a090806060405010f0e040f05061015021501050f03031201030b2401091203110d05090102010c0c0209010504020c120c0a060501 86
    0x211a181e51504c080c20745400c06994500c0e1240500400c1e095047c09203100040c55030069000318685800741c260144d989114000346101214261059081103a03c1808180899100c0138024001d40f00c090074042c10f180d49440040300a000d0078902403500756400b040301020a40c0014402c01a24800d0342601d5042c2e0b68032040c40112007091054060003440c0d0300c800c2140d401605009038201d40584440781c0e91450380d40356135280184c04e8a043c18414181c50003040b15004403044014219107030710141403109182d10f8981c0c01c417032060040f1441502d40b10102143c555080049075190850041085440e40c0d50741040d8200c3d94007200c0c020b00c803500941c01d0031a124a51100b0b120b10940507180c0040c528101040c104500e01c055100700c1c02d2042c8040983c040380c03820050700c02d000b80240d50312070751407175201c00090070b46584c41200803d12076a1a41c8100507035a0b6070007141518030a0704c005803105006139060f840e10801804202c580c080c00501d0020f08000840c0c48107101d401050148603a998030031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 469740566 1250 469739316 469739321
    0x90f1302030a0312060603110301030b0417120f0705130605030a0b030f010218030f150c1605060601030c0504050105043b090c0a0e04060504020f220605090403020a110a09050a020d05010801 83
    0x2454500050010001030000511a110080c6c015000e8030300c40c0c05141180014103526800b00f10b41c21080020002003004914200d0c181e5075001640b413501a00380f4040e420303040c01e04c01c2d243c00750343c05000b030200c0001d00d8165160704c10360500c20014102e401c0c100307024244500135401410324502d98008203e101516040000380741c806200810010250002003143c4d008050001170050010128108117401c80340d81041c0803a44c03401d0081d80a4403040c10b10300005801c540b5192005000e004090104010b0350703800000340c1e01269200c2d080c52143d00f06400d185240c5004001c14000e59180c41303950030080e402c221240c64802d4424900302c0c3c0459500030208100409680301300941070407500e001500140c0c06400c62900030b4030142084102880f454009502003c04d1030805d02903034013107540c40540071040c1c06860004d00d416122603034103042546000f034440c280301784081c10b40c2c1e00364845003240e5208c0b800000c2c002d1001c3e04080195040044000c0003a40c00300c150082000d0a100003ca400081071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 469741816 1250 469740566 469740581
    0x50105030c09040f170d0b09101508060d0507060206041e0c050127120b0f1003170d05155410150905090f1302030a0312060603 56
    0x40c040503480c0c1d2550f5810f20007004000c0304448212117034a111030790342440740280007111400407000c80d820b40080240081400d004120b40400d40713611908010401d15850010000b10580c80c042e51340da640c40380440c2c10308000e607500402c40e11480c030000480b158041580c80c0a50710408010003515911001c00d01841a0030001034454840c01004112070741c010040d00b610380c02c4841440700c0042000030999142c90040d030042440c020825020010003d004401a510003540914114a410b25080c6110705001c140001810300242d21203401c40100c4c0340701590750a801e4004240041d1901c2d244444020007003140342801400c406041c840c80560b05074441c0003c10039022001c1c0d02010349112108014054800f61100c07046c2c284c0c4103055058040030291058150358805a982454150816131089a807111841000708080c0c06001c90350b01e6030780c500c1e041210814840013a8803012502c0090a041c102d00a44c10321074041103404054004600c6001d043d10402e04106a560300c000039820703607180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 469743066 1250 469741816 469741819
    0x8010b0405040b030f15220b0604051909031214090a02010e04090c0b0903070510050304080d06050d06090b010b0a09050d1a040f05010b0d151109060f0c01050105030c 73
    0x1404140498140b50340b160340710200c000c04440c0d04042404c0b00c1420b000e201400c01110101000800035107040c01d8000f480c0100c14001c0c600c2e000b034170649a002051002500da00c0c400e40d03d40c00868642d40d035079100d41811f500c0124041082400c140b40107801c3c4182c80b00350361340c5c190074030390b00f546a0320b900c200d158415019107000e00010900f580c01190145401a01c0ba5801030b61b910101c0c0100e004100080050135184030700c80c0c2d440d016002010301c4d112040e030026204105010080341c5843e132040540760801c0c1d11004071501e4001014030f4401411050300700c141c2189d070110342c02081c800184c200224141c0115800c011990f22014502c130b4510031a0070140108a4010081206040c6506130b114203034042c0ca5100e03000c20903400200310340d4070282c80540c1d041045100000a2050a100b21003420101316111103c146295a400841d038030b40e8411030042541d1b506103418881150b80441d03003219001850f0540e12070010482c40c816400c030801c10902d540c07030703d800401c1905000540c0c4180400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 469744316 1250 469743066 469743089
    0x5010e0405070c02190f06030204051c030f0804020d0b0403023901080901060b040611010e03041a18130c021903170a090f0c0608060114090f040b0307240801 69
    0x1070f140c0903c0700703600d005581c040060801c8500018040c1003200464003a252039500036070f840b4600410050a50510b44400300d0814900c01c160001036007080030155a40b140d410000d0180c2d840e4000a824045a00c5001c0c10000070141000105680840c20300050303c46080c0f0140030130708101400300c03000341101c1d812040304081081014650f005d03405450b8000d000310300100302c040c0c03101c21800301b5420135802800440c0b0504a6145502400e000d1840c024803c500110704092408503031103414000c00401a560301030000c2c07602c107003441b11042021441e501611001041d903c0c5040e003001880d40c0c03c9414014000c0d400b610003041700c0e18200c1d10400d40c05980d000c0c1306c1d0b010900c071303990782e1480585100c009603503851000d400203607d020410360a40c020900d18401503d4420042d01c4800d0041066042100c5c04440800c0e043c4414155241c040d000d031818070307000304154003143c020f040048401e81c0c1031060120020341e41094080506102284007501041c0101c10030040d1100902809101107080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 469745566 1250 469744316 469744337
    0x2120a060305030f0903031603020303040c1e1401051306121811280306020706050a0e120c07180b041803080a11071a0a06080c130f02070b0c030105010e040507 70
    0x503058020317004500c0020f003641c1ca010b800c0704030301c01c41a000c11400c0300542c001008110500101100490040080f0324031800e0f03040709114000e040f02c90303500030050401c40c0da0044100c180d1142c1c0964040e656240803090318a5110000074141c08000e01c2001100d50412200c2e401b0360040d00e000000340d41d030010f50040c600c6401e400300b0041810020800362070000d0320305036800909804c0c0035180203501800c001641c0c1d58545c2030250603518020b01c2e100c1c0326420003210050b200d100003800380c0600007041d0210381700c0c140c0e0501d40782032032441c1d800b031a01c0d00c1180c00780607440b16090b404a000e0321400c4404015040c02c078400b071506004100e2000c0c004c514000001507c65009406c02091aa101004c80b032401da195511041003080512001011141c6981080a120410701c0741c18042c20070b8a00600f40c03d401f802c000b665000317503000903a44458480e0807541c04804141c056800042d402900420145080020305589070002d2007041d00190011030b41207030f607041601c9031500500c400e564840705d55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 469746816 1250 469745566 469745587
    0xc090806060402181c0303050f070f0f02070b0c0f0d020106180504171206090f160e04060f03030221040e01030803181006060e0415170a0804030602120a06030503 71
    0x35000600350310030f03548120002c00503603929141c2503179441640b0a6442c403064000e0500074100c1d4002031000004e402101c05114401c0c1c0c00448145c40d0b0521854106002c50541108a040c0540d5601040b01c09402241000f41d040c004076400941c8a044002c40e241d481048400b00c0c03e80307c5510403c040d00f41e085501d40068084ca03000380342d105010302c6a510003801614402c0c601e0b40d1200240200e007030800800c1c0145841d00c401078a07085440c0c001910050b00b02620403144031008018141c041c0014001001c1c3d541e00c1d184c12060050680b42200d04103a6030300c0c10080d445607099519541e548a409040d01c0d43c0004880c159030a613200801d40b0326180e820740d580d00050340d102030213240c00c48400025802a040e401c000014195401840c08140c5515000300502440c014555584c440e40c00e00300110381d01c9443c02030040498800741c50300b440c044180711403a824140810400303400e4140004001c0700781308142e0014000160401c60402656039100108400c8450318003000b00300e60003c0040e04902d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 469748066 1250 469746816 469746821
    0x8010326040605070b07020a05060a090302160b130b0408030712030f060906091a06091909020408032802120310080303240603070212030a0e0615040c0908060604 71
    0x903002403449104191002100c1158036410981c45440081c41c000352110030050700c881c00c1e0b80c01c180b4600080ca1030500c0e5a4815413103400041000341c1c0d5507a01d1045005141c801c204071420111039221401d504c3c2c0d00c0b00b0318504180c1c0807840c0111078484176040082e940300c1650454084507482c102450505507203035550070055001024050806464521a0030300d80c1c0c1a114510040c00e86040020b0309518014515003a107c0b1045184849410306101c4149a1666030031190f07400001c60303008600d10048404c1c065070ba00c0a803c6071030302501c04500403400d06c10010080680520a207403000c03050201810055000e03060714902001030704880c1c2038002c00340e20400910381210f095140d80034059250700c0924035540003103c402852100c901c1104414072031202c1041e521990070f403078071403031440c01010203980c4010031a241880e4400010001b8020f6130f040d40440b80020010741614a5030800400320081e120204144034807451410207511501d81c000d0466108440e240300c00b52540d0707a20711040000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 469749316 1250 469748066 469748093
    0xc060c0303020d0510080d0309030e040b1c050c04110703020d11030c03070515060d0b070f120c1d03061005010804020a050306010305030304110303030103020105030109020d15060507060516080103 86
    0x14150240f001c3d081030441800307450b224001c0d41c40d03402c0d012468041200d03d003801c0803115005040ca441c00754000319521801c0f4200420003910041110404000403500c204260121180300d00340e40c00c0f0003c10403102041c0d4140f880030803241801840903150021350148601c80c40240568415802126041d026482c92012910014103803810100c440d242107056500410701180d4680101901c05003400703602070640e4100e401500c5400507070b08641e8030744061010142800062011104007143d520703216510b450301c14051f400c0c040c070180c061004050500011440300c41c0c0140c105030a501003500b00001c042e0302c221200c2d950200810720f490300540e041c61010380306a0f00701d08a0280413900f51000c1081c0c0c0c1c0218440d8004503500d103054140710014601000240e4417a8001700f00420150303a0007006d4071b0641e90309580041e035580304901360200410701920904410038403241c00080b001d0700034018108242c010b203001d00c4035035a80d201100c800449400f9401c04204010f0042c00850340e0100d9011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 469750566 1250 469749316 469749323
    0x812120403020a0506010807060306080606010507031b0f0b15180a150312020d02060117070e0613092108042d0b01180f0e0618190b0604050f040c060c 66
    0xf04032440584449042c20001d8100291035400041e04109940d0316104060080c445c06001d400c0504101f40001d10074803070001d01804004502021280e40900c504d1001c5a60b03501c80f50000303c0700e80d42e2514500c00c0408650b028001a0201d00c01d8400342421000760b8009400740d070452040c0d80e1510803e400414105000c0e406415002070080001090f01e0300c80754205009400500ea00610b5400003860200140c20084c0444010112915a420000355080950f04c0e40c04c1420300568524022580c1c0b00c08001490405505021070041400030010303160a400b15070304508500084004020388508c0c01c1035900038950000f01300800c02c0e4194262081a00045d42c100c40300c02ca03c1c9946032071400c4a42a000144204489983c4900707040c8544524a0420030101c024850381144800c500d854000041c6011401000d00c107400044400074001c0940d00f8404c03a1155041901038249226601022184a4050752400e2302242001e00e401e10080d110b84d500c103055540e46800c01c80112002031080408a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 469751816 1250 469750566 469750573
    0x191509180f170702150702030601061103070809010c060c08040b100b07020f040b0a2310020c010f2c040e0c0a060f0309020a122a0b091203040f0f081212040302 70
    0x2e10040ea10110256008179841c42d800d40c80b04100c1c0109414910180e000d9400c0c00005100c0281d2504080103440201d6081050507407600010700041c1e52007100400d00030a0390303203444110b00c04150030201442c0140e010342060750040d0350b00c901c0c400101d00c0c0c501480c40006403d222076001840e1910a94480c0035010304046402000c07103011401c41d0401c0e800610202c4880f03100c112080381c0110720f03141242030071118252112560100030303495000d900d06490400514074188800d850003500b2030580041751795400800765400c040740c840100103038009144280d01f0840c0061414200050740c26080000915000c0054504001500c4004011038804141a03c80d01c1c03c001503038070b44504100a0120061110081402e8540059244164103001c0440e6180002c5400c0781c003003070004001078a409005150352500520300258141d8054000222640b0001030007165541a4505420484600010344404107490fa1407003502c58507081c1307041980c86824498a08145150864030b07410a000c5d0055 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 469753066 1250 469751816 469751827
    0x703080906090d0506090d14070b040c0f0f08060c130501050a032705010b092809080c0a051006030201080601080a02070212010e0f01060f050405191509180f17 70
    0x2052000f06407880c25505a00802c08012200200348161110100c05141c20304000154000d45199402a1f901c05889440c402001904125100c040c0002411101c015118000d031303a81c46142194805000c0c95016010302c4c0c001c02d24040081741500c50048501b40001b48990400004484070317002101c00e00d0405407030b00c04141a001d40d400884944181e40c61048031018403900b0325900f5155606000c90140f504074041004196200d05003c1d0004000d030380d0985012244110b04000d001901c0700505015400038280d0582140080c00b81409032040c401d81d40010842c82c0c0003821681280f03c080e0110310108005006584075528031944050a2003005082003003503000f150f018880c1d01a023080b241c1d51500c005522180c00c019a82100300044000d100c0142884082842803540b4410140615141c0340030560006404190524041c0035141c1089a40321448505081110a1007090031592402072008000e016410b0303910342d0141c12006112a40c10240d4444180b91a040c03003102d201e00080c0b04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 469754316 1250 469753066 469753069
    0x311130c020102070c1e0902030711010e0601080606030304060806100507080c010c2a06020906091c12320c100e01050c0712030c18060210050702030903070308090609 73
    0x4840d202611540010f031200e200707240c03a202803c060740116908103031811000e105180310000d88825124800c00c056101d0b110444c05481c1401200807076034545d42400801c000f00000015040e04030340b03105040340c0040c0c032020107140d160310032801390303500180030400043c0c0103042020124540707141a24003140391500d240c8407005d05400000c040d008036516951a41d00c01c03980120421280c2110380c07840120303803442107010310280c00c0710040109007940101d01c0c0c06182ea91841a1030600c01d015021100b035042c0d01f0016031001e20b11040842c0c0d0300018088402c20386104600b8880703090b2401e54403122915004003014180400320a09041c3d007942003240d000d030a04180300009400000e44e002254884901811a0a456005101d2080d2007024070403003011800940d503420aaa141d4103000902d58905442201c803072008503061885242e050b100012030950000b0009031140842108220f180c131024422070b100d1081242495042d88404800e0003c0341c0018014001c0c21401401180303480480340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 469755566 1250 469754316 469754321
    0xc0310020309100e16090b101b0312020d140405060c040f0e09010603060e07031a09070506031504020304140d031104260a05010e0d0203030f010b0d140f0a06081204031113 75
    0x1013003103200d16101c159502590400708e0000c02c660000307051080d05280f40c0003041d5001c6104020140401403070100810460102d54101d81202c00794030b0052100f0700075980310300d4a054041c0da0840341845014001280e10074008251802d40e90005202d40b060b0b490300220545481000d06041e03625581d079000000018071520070342d00d0b01a8040e0103001954610704207040040c07804c1c03042981c203520341c00c10400310050100382130b0241c99007154201e48a4443c850301d010003a00c003904540d04130f4400014402448014103000740180c0c0c01c1011503400b00b044900071816540000040c0754890781c24070081c49138101200c0d01450f10704d544004980c0300c0c140d80b6001c52426a0078542911303903954400c7c280000403814001c2c8964000320780000c500d075051115580c500543d0504ca46030b50303035101054100a540c07854101d00c01072203143c40c17020354509280070051241a41910020701840c5001c500107048900459031074101c0c05504121030811b8034546802c2003a012611043d94840e0303000c0440c2550010303a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 469756816 1250 469755566 469755569
    0x80a080c091f14120a020a05210a23011401020102072009010803180409020f060a090e06010c03080a0f0b1f0305100302060d0e0c120c0310020309100e16 67
    0x124100e0001404105000c0d2500e030842040300c43d2000d0401451132107400384200d0503044100d0100041e41c07041800d004076120301031001921a20f203c001c51070b03580e004800c20f419004a0080a04002da510041d1801c541000003024a941f00750074100100020070440a10303080f052810b00002d0326000e41c0e9960b42c1d8060000718210901c241902d56200000c0c20803403403e501402212006510b09400240c20320301c0032007502c050a00c07847d1910011402c40d00c4901c0309403401d1790083d00c41c5403900a1003038083c1c844400307401047d60480c19603001844561003000c0442d0b0312601621000110740b2003062410103081040c9501c1c0456484054084254841c4c038100d2558003c000d200181c0c0c0141c4000040035038002516900d6200c9080005002680e15413044450041c080c480c00a0341c5031b0580d40140c18008007081803a400407000340d03079240074072002c942d1140b07131902141510001c00c00e103407440040780001d9504025642c010518280400b03441e80c44804d410312007508807201c4003084100c008044406 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 469758066 1250 469756816 469756849
    0xf0318030f05010c09050123040f0b0309011401060e0405040c0b0424090b0a030509121603030b03010c05090d08120c0a02012d180210030203040c0b030103080a080c09 73
    0x300c492040c1405020702c00d10301c950503d490b0001741141340c10002800000c040170310250030041560303c03603025101001240c1c02030480c503000110444d607402c01e43c0c900c0e410407906050a54281001c0d40c2013038844402c4036042e6201d980b15019000c591000b80030040c90001d20440b841801c032100441c1b08132114001d08000d1408a00912942101c8021071213002c000c601400180301c60750b5414080e113295041580c588880034500045c6a81d5915101450144c241c070080c2e209000000b10107400d09603480658400380c1c040c2e1401e220301201281403600700e071201e03200e03540005c00910142c42d0f10f2602d418040142c0d40901e0403075041c24031440c00e1104030081030314050b98044d0000b80403c1007580a01403580340c0c43e000d00f881100c0f600701c5500f002480030032000071420503944001e40c229812419084407000c6401400ca056010714520002d0002d51050f201030311512089100020130080440449040e01d0780300b81200e007403841c24030060310825005400d80f004050144511000e584030702c04141c401614 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 469759316 1250 469758066 469758083
    0x20703050d0f05061804030c2030070807051c0605010e0a0c050a02120c15040f05060f0118050c1b0709110f0405120a02091608071b0f031803 62
    0x40880800805e0000200500e0610a802c001c010102e500911000300c01070300300011102d1504400f0006500040041503140d101240c0007030b00040d0103803221502e4010f050030b4500e54035424584061035942c0c00c1e920481001c0d912000e0188040c3c2040300031071282802060b50108266603035179508060701c000342c10a22140180314200106021940180d1540301c0b17450a101c0e1410990081c000e440341541503845049000010700400310b08820481e541c41c018045e01280c4107030401d480c001341d8541d4511403c0d181c501c44c19010a404018400001f030480700204200301d0000808070605010b4a00101501c01d049c1c0c060003640e5982e071840d6411a200c03405000500010f81c10072048004440f02c2c92202100e402c400d10041031204110070481c2c050710011121500c080315071500c46031600b07028000080d0402c0007002440404a50b11034002e5040c140350311095243e56406400302e40003040800d070100480c007822040b0010031200c07030500307141c2c500078600001d4041ea0800c680c1619101580100c51441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 469760566 1250 469759316 469759321
    0x180703020c0c0a0b0a0e150d021c06082113120b07020606010c02040e1c090603590c011d1503071101060620060415020703050d0f05 58
    0xc0003801107816001d003c407607154100742400469101030142503219400e001203c0301d001542e690385075506440500c0c0035509541c4110348100304000e0b4000e02085000101e94824006039200903000b1305054a020304014182e000820040090200d0412a031404036001004a42e00661110080305c024002c011881e01d0540380914140351103041c000c1c01c0f402150000414843c0c9a03a0014580704078680450b80403030403800d201c4007141001c1081e103030201140900c01c0c0701021540c002030030703e007203490300c1c0c40c00c01444440c031109010480b50002c1000d40901c0c55034a124600400c502242c4028101c00b0303034a0240c0d20f0000308500c00032440d810684080e40000f5503082c013980e0206054091120403d54018652103400118103080d03250605c0c8800110301000181900303109251419440303000d80028403280d60344e020041c142a41078800d210400604606c4003600030700000340a40a55400380359283e50031034402c074083c0203400001044080107000c00c54601104540d0081030060f8040e40300008190 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 469761816 1250 469760566 469760587
    0x30b06010f031a101404060e130e0a29071d2407080d0203010308040f0801090b06010f14070534051003020903011506030b040b03190218070302 63
    0x807540074200200b6003031401c00314800b052820f074512042010340d41001c4005801a06a400c400700c800b50a0756000041000645280c0c072101003030b04200d0940300c1c4011210700300f59202c00c1c0c6035038134508a102e5000d400820001440000150b15103043c40d0b400c0d03840c04d4409100914400c0c01507810000050000c0e2079100d014102142c003990364401181d29188465034921084101c02d0403541442d98038102140d8802405060021919840800f207021562903840385465080c581040c01400c0310480c20801c04204000b05114100d00e85402c960103aa0b107944a400440d40081d1a071640400c001000d040c00c04c50001d80303005800307034504c980b01420074650621000c0f40c500d09920b8900c06c01013000710811a058808c0c0398110700752441680c0e40e5100e090f0030a4142d02038412940090380540c41c044d101e000c007070740000c2c120003515850f81d814404022020200000e03a43c802540c1c40d419001414a02545410401e103e0845403001c2e2211a000d00a808132210500c41140d2050200e5000642e1270300c0b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 469763066 1250 469761816 469761827
    0x26040b0f01121a0a1803030903021207081801110111030103050f03030606030a020906040b0d1b3014090a0308072609070b0a09030b0a020f030c03150406030b0601 71
    0x15284190103000c441c00d1a4654012600e201000d41c3c02e4a031816001c102c5103082ca40180040c1d10307010074005042c4180d460014000c0000c110300350010701482c00f107202d40000e0401111001a080103890b82071205203241d01d054240640c0000741401942440c91659042c00e0007091003030501040342715225851030803c1410322001451044c40c982041040000a950f241d0a503508602540d200588950100c03020803120301c43c030340090b5100c05010404020107030050b0400852400032241007641d1a15240c3c0640e581119988190010070b01c4070b00480c8a054104450000601e6445021943d51101c501d00f80382d034502075032082040e030060580a810f054112421079041422442d00d0b0565a0300940c0c3c80d908a6410344200b080e1680c0b6001040c202c1c00100107000c00341c0848000c450381c0d0091040d000c4d00c040010b200031901305044200050310042c8900c01d0740c04028051850f14a5650b61020301134465000809101c510901c051405106403564030446005e540305a014001500340358001401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 469764316 1250 469763066 469763069
    0x1e0b1f030e0c0f18090a05061306200a0f0c0c120b070203120a0903200c0f0f030303040b0705071a1503010504110609010302121f210326040b0f01 64
    0x103860910f0201c3d0958488240d0f001000e21020011042c503141c02c1c10290900c2004a40a8140c0c4503a074140f21000b8001d0401d8100319100300000c021004140d00400980741001a00b1000701105201e007045d41c0d8091210011040e0306450040348000e296604c0d1684a01d5070303002041c40c02c94240f85002000700d40400347e5003004482c0011800c010242c12148640c1400400d03104546d511000c075042014003139006401100c03404030018090304241401c6a0b0765a10700402248100e80c00761420b802818620580c0f00d0070100603015614690b104d842d03450880e10060320040801808004410204200804040002500d0201141107080400c0c544003000180d401c0184240d00d00010f02000a00c0c18a1800301c0c4c0c00192401902d90302c0d0703000143c00900403401c0040c01c5603001c038104083c0703010010025007010011501d081c443c0e500c903481421442607007035083d80b90454020b400c4c004203000e030f45180e140002d940c044018003005111f9030b00c483e18040c4c4081b286040071070103220550303501c450410b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 469765566 1250 469764316 469764319
    0x3070804030b3d05041b020118020a0b090a15020105150111030904050c0c010c110708010203010f0b030c07020d12030501050312120a090204052502011e0b1f030e0c 72
    0x20000f600401a04400b00350091000f40f40d200b40c07032241100484560142002030400400800c496a88902c2d400c0400c40c4520103c1e0041d4a0804041842d17000e500c0600c14494002e40200800d50610104408691003110301c030394172a80038200080d003d0b48004088605503400e500204650500b07034502c501c0e1103c80105c1758180540400801c2400c1d000209a0b8440f940445001c504d0340c0724200030074828891209400411b5003403104207000c650304000da09008901d40b40880c4c0240790380c0c0e0101402c03400207000711001103000210810410310064007035504002d2901c0f40601d05192580045d07401d101090341250200c1351b0040305001c00740c0500c2901d004200a40c05042032001e4040604024030440c1200b041001207071001c0b0300ea00c952640154078250303002d0030401403410424010b9801000e0003014100c00b00b00b0b500c10180091042c0188940c4181102e1002685003401c0c60081c06850540b55080d000701c0e000130b0200d202c402035068403894440030386001403007807440f111250820004a1076075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 469766816 1250 469765566 469765591
    0x3050c0405130b041d030403030801050d0b0105010c030207050607032d020601091a040e0102070b130201080712140709060e011103120c07140d11010e101d03070804030b 74
    0x10000768540c1400c00c2c103807035021540040d8000074440010020300c181060028000c45051003607440c20000401001501d010307484150460b0398034010811042405203004140201c0a401004954091104512194401c0c0180d42d402502da402041003074214110940c0002c080c43c0c1d00680c020b48040003080303448000c04d20140d20f880403000180d660350f4103100d4024601d9a680603110220b000304048070607410001d00c1404802103040c0082c1c040d4220540940e007907050480420781524030b5080c2080c1c290b074103031610126555900b1080e148003441c1204940046d4650600d0880e5504c941c1c0c0c02c40c450b642c1511461806030034000014001c40080c00c4560602c03500110300c01042500001b40c4440c02c00148080c900e695942c101c0f0301040c050810300808150312001e2000b07141001190960b8034880710707901e01d070001108200740b81c286c42e04520380c04a241c11081c8049a90f41c80e641100d00c840103680070040742c85142c1400c1624582c403405060398450400310702401042450082c0079003100410300300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 469768066 1250 469766816 469766819
    0xb04051e1507151b080c0c0a15150f0303030b060301180903050f0706091704081c200304060e09010b0703030506030118051c02030a020d0c1106040b03090609071206021305030d0f03050c04 82
    0x303e98400c003160002d009d0400408500d4001c1489800c41281100e442c1039400d2044d980349048030380c0041501040300403a0801803012130608010382035a0407110b49444100c20110382d5500500280698a000c1e170030460304000184c1d4229201000b800c11500c40c03280000c11006a0400c180d0b030588039240004a014104400c10040e00f0000349480e854480c524490309060740035100740d6400191449080d01c589900b0356003d581e10303011001c1c1c030446209840d0380c041e802d8005c08100c134143c400d000b1000381345410310103000400e00c241c1c003061b4081070140c00020b501d010340f50643c00b104001c440494882e40138030040d004294a030a60f45504034040d00041d8204148010003030345504c090100c207020855004d00d0f490610542030a003c01c0400040c201540d00d50301c40005165580c42198050701610541c00410100e5070009940c200311011441682844e070700755619540a0b41c00140713241082e0b50704d64000b2420356402d00c0f5841001d000c2c0c1d1105140030100358030180039548028074601d1050002d000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 469769316 1250 469768066 469768087
    0x2031314030c0f10031505030a080d0605010e060301140a0b0310051302070302060f071701090207140a17071412070201021c0807140c070b04051e1507151b080c 70
    0x2036448650307542d04001c9000c6655100d410121b2415501403a458400c00c2144002c1c491410010400011b400b841404003c3d202c50042d00c010300d4440c03070142c00160402c010480d0410102070b01200300d40041545048a989000e0a06e494106841100001d9080c6400f000185415804090030303e51210b010742c10301c4820346010303407a0500202103514680c00c803000540d8a51044252000d005410140c41d24107503100c0a41c0c40003900214001c0314400540d11030001d810000240d114440c90340605e14040c0e18a1045659141e0b820900c0215103240c100e1340d42142c01401801001413013010314000d6034807071401d4000245404003500c0c4201000f10254500f0b00d01951240041d58440020b00f0b08080710f0310004025040791003003a10340c441c1800b0341d00c00420700c68000b50041080700c000b1548101000c0c0364507001c010100ea10100d41e41c0c89103c0200d04c00494155030040c2070038030302490340840018091050442600c2c2604181001a50b0300c17510f09400c40d8109072040c1e081704501c503420b03040c00c2c05142d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 469770566 1250 469769316 469769329
    0xf0e010e030a06050c0d0c08070e011d01031d0307050a0204140c0702010c020d061e060603140a18051e010f1b0806030c060406030509100e1c02031314030c0f 69
    0x300b0140001d078407140003c0301d402003075040711441a0703000c000708a10f00c010300004017820700c160b802700001984507199070b18640c4601c010344108800302a00750404c08020006400904041800800e070710f5040c180140800d4040c0080d00e04240100042c0c03401401500c1048101c4404a61b070001c02d002120903c203903041076005440846074282082c01a02c421800011099420050000e0005081c00c602c20000184140004807040701c040d81405056141e07801501686e10b482e40c0c20811541060014500c0d4510b41c2001c900300c030040e8800b45000c02143c54540c01d104c41e01003505902e00840d00b40940040c0244691100e5100300c900802101c40c01c8114129440081214030041090324000308400390b8092001c1d50000c00c000301100d5450384e80c3c02000c1d020b800c0842d0b00160501440c13504c10f0403140140508001001c016000d049001e46c010a219001c507003415486003144420702c0800b05000c0c8204600001e001c4900c0085c6285111390105441c1008031b07201603004004074a00f8030851703141d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 469771816 1250 469770566 469770583
    0x21305270313090204060c03030c0e0a15030506092e090203180f06040f060504050c0913050f06091f020c010f0603060c0906140d14070807110c0d0b071e0f0e010e03 72
    0x51400ac903a450852a040740d911481c250416401142d00c8400258880440e8800c4101103594405200365034818007000352080044490039480d281a02c0c130800400000c060001400300440c0740b00c2240c5403142d541c81c0c100e800450310003135600d18955013544440802c2003210030002c4c02c0c03401000146010b85e00c0381c43c003850700c2d5002000b554850003c00c04012061200c0c0301d071740c0c2e006854500b40f0701d032500003010152503101081d00c2c107009448101303901076408038a80e80310344c0c1040000c0c400d41da841e0a802e4202c0141030129207510341e00f4825040e0308030080c00341e200c0564040001160081c1103081810884040034000700c140f0040450803c0004d800408941c403096040592548a43c80c04c880000a0054044049240820501013050300340d0030005240c0078510342e5a401850a102c2880ea0359100310300150f142d4440690744001001494818030700383c2c44207441c6081e21010422482e0000b03004606100080447c8046d01d100342030340d03408003101403c0e080c01d107482c885910700340000c661110f844 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 469773066 1250 469771816 469771823
    0x90c011e05040b2a01150e010e060906130908190e01080c0f0d0518010501060903030c0206031e160f020a0c030b060609060403050109050c0904021305270313090204060c 74
    0x100e40c41524124443c0b8581301e2107160360003600307034800c18003c0c0d60081940c1c2502e600c00c54200100131546d1240030484a050b1040d1158103c51a03c6100c2088240a0010481580300a051800080749100ca003d0051041d02c41c00007180c481d2510b0745e00f120280b01810008003006560001c0c0d80c9036aa01543c01c1d500000c0310401103a55003c4050b43e9103185c4a41c64088129508000501c82520b8881d20001c00c64204040200b0007641c8400c0110b41240031440050001084500460b01620b000742c011900690141204400a448451440c10112003118840303240a01d2034003201816802c203201800c0e00c030701440982441c1d07540c3d68482071440920300001d440800d1113800106240c55901c12214601c0c0020441c50b104c90b1b41340340450190004030411902c1e401031604100f01410007560140c051607000348034100307a2410545100c01010010b00c01a800b160f404000003c02d620400aa0600507203100596500c64541d4100520400b09601241c6107501c1000100b03c40d030350000c11409003070750 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 469774316 1250 469773066 469773089
    0x150b060c25090c21061d0c130308030402120606010c240e0313050603041110140a030603020a151403091f0b01030f0e0601180f0203090c011e0504 64
    0x2140c0102418101c068119091843c50119030351040ca412814040c07103031101418500394001030b0415201030340c882d0711503820140314a62446480c0f00840401d190701840d400112400d10b00c00000801c0e1060344c0394416611404000140801c0d070604090000303d410050004009500700940000c0041c14055000b52041e00d241c0111600c0005034030f10700d05600d01803a01840620811002d880e103039031000c00c91040c4070301c20940008050a2503005e40344103540181c0340c0e00c00f1450300010b0218000640302004104100101104c0e25140a0b0001c3e2403858129034000454600350b02c180034014420b900000d400c8034100b8003c105581d80403641c02d14a184a03081982c5035141c41d1225441e0003148081c0c20784c8940c00e1005002c828940d980061a004002da9084c8031185011080804039010009403405079004400140f05041c07249640400d10030b0315210001e624440c51030054100e070015180885070f5005000c3d00364881d030b403142c2c0d99495080c02c1440608013200000014046101e5445080704004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 469775566 1250 469774316 469774363
    0x106050a05060d0e0d0806100201050c030402060c3a030e06072003030a022503022104050603090715180603090f06020d0e06161722150b060c 62
    0xa1030b04441e00e03040d9003508075802c43c03941d805c0113400303040100e9006024034502042007030218814010240100400301400b407450b2516000e001041d0711042c1008a02d105002411800d601441e5017031007448031816091030030b180d0600c000320a680c442442103080509011703602d074504130049900c41d000307400740c1403105c0310300702c0020301c0d640c45025007080c0040c45c00b0200030403112784500d400426a00c58040300094a2815002c41e88801d17200e048405801640409050201005146402e0050b02d02c0091060b0400741d445002600a0b48200d608001c01d800490040002d00d5010400004090041c24155030f0b50082d02d05400c450029403091404040d226040802480207014210103080d800041c02d65440750b0807483c1402400042640459921a820008201502011a440c8046400c1e5541c003103c0c11401d198001c80d0001402c0111486144009420b03100801c0c3c40c1c211510344260081e036810403001201c24110f4440211090080c00100003d851444020030000c01e20b08007040071043e81d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 469776816 1250 469775566 469775587
    0x60904090f0804030602030403090914160504080a06150603060302241605010212071110020c0304051918180b0a1d0c0f0307060e2b0c090e0106050a0506 67
    0x941030301c01e000d000d4038800a03001c42130000f660000d510450291300c41c08070007540c0d4032902e401c03115000f40043d0140b10341c40c00700d0303070100f64041c01810605039450310504083c0c03910b081c2810008040012140301c0e80d5400308041f01c08040240c03a0040940781410040d09213103801060701040b03480503203a1a850341a00c090b07a507211000c140c5103401820145000d00030080c3c50854000c2d84000d40100c00d261101000a841a20603d64181c5d80075118010b400109111080c540280d0000a1145203601052001040a40380c0041a0315001c1c1d071140c141941d58a4074541c1d00349015070b6a201c54907281400f400e044c40c6c441082c40c0820156104881e900d641c0c3c0c50440c5c0e4002030040c00c404c4c680740c01e011008d4101c0e03644001450300d240c0c00c0817035610408a440c11b04043c0e582e43c140c407848020031405a48450103142c8031251484c00301e0111180f0b111201e041404080c07108a104084507048000e5005014042e1031744107040c0b0000d000002009030504020008214400b40c0c40b130316205040018881c45032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 469778066 1250 469776816 469776833
    0x3030f070302190309080105090c03031c060b0a090608131a0703020909010b030105040606021c0c080c010207060c09120201091a041d091903080411012106051201060506090409 77
    0x1a61070f206540061000c515004188580c90f20400b0340560a02011850360000822b21080c400030041c001d41c0350042134036110002e8030b40c10030695480caa640d14001451004d0000a2200b15a03554640c20218100315000d8103041000e040c03000c07442001c59031000020022040042030783d0900c0000d00095494140440c084c0c0300d42001d1640000d510340c0001b50f40c04895000c1c5041c1c1c0c1040b83c05000e440c0e00c1d00300481c3e840414041642c0c80030840788040c4940c500400e98150260b00410020b841d0400c1d0402079402d90348040c00460b0f9041c0d43d00c5000c40050360048000303000c1e02044451041410003900000c1400046020701401c2d481d441c4400068400d285007143e000341358581c1d0203001b900c480d003003121107031500b22142d03010b0340030345190240140410b048600072940d058803070038296115521084e01030240706400074180117101e01703580e9408050961003411102161004501c242c20034042c444510805c01c0e4644460781402d500303004540d10300094030103100c3d042e200011301720f80b2401c049a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 469779316 1250 469778066 469778083
    0x1e06060c11041104051309150c0509060a050c0d050c1209010c0b180f0604060b0105040b0a05070f020a08010e0c0306090d030905010219090603061d04060b01022e06090b03030f070302 80
    0x20f2044a1b5620116000c2950708401000b901841e000203c054a20000c607040d1030300b82020100065003080f10020500d000800f80803c255949485410401948410f0303140c00b80f81083d01d404140b01081c40115402e04114a510034142d01030b001d030030f084460700060401c4080003401400c40385000700041182c0038000500c1b00303100041040b11155007803a0211031310b6a000340c2d0203941450404c0d08070103065014104031021500b00c4c000b018a004800002110b036a04006421141c0e210404440d601580e1541c01d504084c000080000907040709410b4a1450f24a203248418041c0d04000d041280003940450f0221042030182400700703070146a46003040c0244107101003550611402c414128403144d11000314016a6141c2d02c00b001415100d1103020b60b601c3c0001c050006840e0b0010004000171102d8018417410103040c0102c0d06003e442c0c202d00002200c44407244184410684542c02249074640100783c01806000b0040003442d03684400b00361a80300354010107078121400101c8008042c4204807a04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 469780566 1250 469779316 469779319
    0x3091703370b19050108041a0c03070f020a0c062001020403060c09060201060b0d0b01120603050616091202090709080601060302030712020306100810091e06060c1104110405 76
    0xa1101c0340481d8203800c40300d4004024144035103480e0185045041480100b01e050b00030080880545290500448042100400807507c441240c00607600c0c00714a99100c50180e142c500b8002d072645015140282003031072444981c030840d4401700c8101e01241c0c540c185c4005540070b5190803140e6420a00519104a074800844035041d0310000d000420302c85236610089801540d5510407520503601c0408078207a51039405241d074648020848071b0080f081c0c80d48064468075060500118078000e04502da011117030564810703030b444d0b0001c0081200c0d0300703c498202d0040e003156051000e140e80c00c002d540220050308000080c000c92031440855a20390048607900300920680c003c032000c542e180c00f8014060340040d507008000c60000a002c2151108600031380c6e00c02c8401810784140441c1c2480221030220010b0001401c200c40c015000c640d0309100e000d228100c00b440705140300c503a0402d03640b01d006c03103440e0360200d030411030000f52442c0000c0300c2c07644952407050b0454000ca442c01c5041c0f0341d004148190380c8002e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 469781816 1250 469780566 469780621
    0x13061727010b06270604062703120816111c0e031b0f0618040f0e01060308130e0415020d02090a06020d08091204090f060803071b0603091703 62
    0x501d102c002c5a4110241e005131101c400c098401000c1440395601580c0142d101041d1500b00580082c3c2403000e41340e04016030000c6520003140e4030b80350f081e9004080c00100001035036200403c600c003440b0000c0d629854003203160040200c180c0c1119192203018541c110342c0c4c1c03a0180c0c000c190003070b481241e4000c42c848000b0107590702e05030b07403019a0303039000c4060060301d0040811002ca00021315180060300d05509041c00ba824281e10340108010040600004100c502590f4149a8112020034420f01000c1c0d8860048a5038818a402d9060000e030800e90180c20f02d94032403000c1000140100d040c481c07014910740c4c0c0250719940402441006402484030064009003540b000040180e80060592aa610180c540c651180c480c1d0103915210020f100c1c42c040c61210030042086541151360102c109120012000610f1603183c0403070741e085610801041d5108075a01f00c1440d03141c003100c44083e000740754905041240045a94910700120100010140f080c80e002c000510b04000301c0380880c505100c4480741 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 469783066 1250 469781816 469781827
    0x10f0b0405011d0604081605030307020d26031503100209010219060b04090b0708090a050613030c06060801050103020a080105070905061803010c0f02010b0a030b0115120213061727010b06 82
    0xa195074107c002507034040d075181e00300d0005103401c010048450194000d40490b08d9040b050f2240c00100d1a40a43c031b5040d0214000c0b40e008a60824005d14007840c143d40d14051403005090030549003170002c040c0ca81070b49104001d555800d03070700000c12050720b1031089032070520320100381044001440e6501555030050b0400715028108031070300c01154450303242501c8071005915080503059a58801c5400244a41d200501054891304091000101240b20380341203402c03034000d5502c00083da18203510072030f4203a4465005000714542401c80d1801303814218001c10103403800d918000c12040c0d00c3d10409001c2d0000041c043d0650240028218207400054020301c20303000000c0b401011420002100801075103440d54084161405c0d8103568102c0c0c0e00100e100e40030b6420001044000d60001e4801000c1c070011140c0010746000900140100c03141c1032000e00c0c810351070b02c10050801c60301140c2a880800e1804208081e403114602107880741c60889041d0b00d54503d0681c4107a005103e130304121980000c0201c2e5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 469784172 1106 469783066 469783079
    0x100303031e09110108060d08160602070210020a020910060203120c0c0607080702060f090307031805040f0207020a060816110a0b07020d0206010f0b0405011d0604 71
    0x614003419010001d103046a41c6180222200d600225103660107603008030f40c5c0d07980818181c5100c0c4c2e600381d960740c0c1c86000d8450010125094850240c0807018801103031305540b50658081c08046090318114006507403690002000c03403081d0740880004240e80e00541e800c074102d403546c2d0015401c20350b100d0b142d12900c8000400c00c80700700c5803e21141490031800c11016000d4841034944101c030341403445009041c07200041002c45001140c1c400c2c800c10207130020403110b4580d0140f0301012440055000c0c0b1000d02400d5118580c031504001c451209848180d0051080701e10803201c843c0403940d107038025941380b0000c4501002c000031070f15100954900400700c414840d40c0040c10341c1c1e0080004e0703071803014110040d11082d0059001000c2101c01e180c0412802c3d014001c000b62188100b46040c41c000507901c1076008050400251004c10303c440180c00031203140110340100710b261107984400 = true := by decide +kernel

theorem cover : BRFrame.Cov 469604316 469784172 := by
  have h0 := BRFrame.cov_init 469604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 469604316 ≤ n) (h2 : n < 469784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
