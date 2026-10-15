-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4938
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:13:07.46246+00:00
-- url     : https://prove2.me/submissions/f0c2748f-c382-480a-9e6b-4fda474d757c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 887949640 ≤ n < 888129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 887950890 1250 887949640 887949659
    0x90105090f0303040f031a0a0216140f0f010e0c0f1c0f020603040b01031119140d142413030302030a15080c0102210f0a140d0b1203090a 60
    0x104800d82e4061000340004610081c041d55004059400b87ca0041080400080e4041802e08020800c612142c01801110000004040c0c482d6205620241466101e07845030380b818038001c0c14030703a80f41041c4100c1c01001200c20066208a801155103020384517001030b0324061007840c03204c00c6c1e801c075004500300c007298600c400224904500d252182058918a8a0740e40000303189070400d540035140d02602d00010402c010080001141d01c00b0260f03091552848805820342483c2018400c0d400c5a0008140d140c0c8190380c3c190400c0003043e80051204906138284050325510054044005070507840220400301c41d040c8001e46900c110000c8003540410b40b001c1d80d00724003a400240141ea50140c40300075002c500801c2d08a05006041100001c102c070001c800002440c1c4002d207104030010190b09040320100050304011500e242038140000e5646150040003111103d40c1040c2c0c8102c291004603414022246c26001030074a03031808c580000a644107400d010b134681c070031802d403207611401c60701042224501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 887952140 1250 887950890 887950909
    0xa0b0703020313050d0525020d02102c0f1801120309170c04151409060f090115030f0608190602270a090c200c0d03110708010209010509 60
    0x3c0041c001200c40e0340c59580d0074903104079070f01e14001240000c07824071800e03a156840182d0710900403078002204032244d00440c013040c2c014240030f030081c20305403d00c08003c0e011b040540c0c00c0300c80c00f000285486008442d8600011481c401003481404480210456890544a03e072605a4a40310a940a0b40b80400303200c142e030346102c070450034000d440000040d2481440e01e10800c500c02d510107805e2900d04001080102c40c6080841c074a003004445060004024442941d01c90080549945e0340940b590300004444c010042d910550060b003620000c164040c0c1c1d194241c4101d0b0f0306440600a080e1005e40b038009030f4006010310324469001041e541030720340c11888030a0a442c018000103140842d071313240740d440c20116070981803034400046201904608090620b800109010700b410030031260342850041000d078410006440b240a081c1c6840d40c1c10708180a003030800d080046c2405041041ba140140820204038a940f40d01d00500744005034083c418002c581100c0416910b2500c1c0849680400c1641503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 887953390 1250 887952140 887952151
    0xd0201090e060a030b0c0306040b030715050f0903010510060e0f01080f13061a0102100603080901052209091506060504060302070312110715180b040f02040c031b020a0b07030203 78
    0x80e0f000b040080410807448460b80614580300c1d005a880c50140e06000c16148291044c40c060740c00f9000030014900c540c000c0c4100e032440d03843d19698a00c204d40f41802c3c54014584001ea05528041c06e2010606c08030702c526081361213a44034240c00240c0c0d0003c0002e8468000301761400305041100294a5a800c1c14900d40e003c20f8a1580061650070303070b00c0c3c450884090408c2c036488c2ca100075814111640e0100a524503a00300300f9001e01000d030450351010114024171003204d040c02404a040340c264030700c505500c01c040c045401c600314480d507940445800b600d582e8074160784140c0c000c0b04007500011103000d03840035109540c649601d03052402c1c204074004d500c000005d4040111088074003044080c94002c03100c1d410310401c02e482c0c0700c5140c3d0405c07402c100c000e90342103030440b031405903100481c98444900c0e00b810b40d0840362140d00d50343c81c1e00301004241407443c0b009500900d000000a08039405501896103040b1340e4448182d200c072281c1084e80c1c1c038255100d02500714441180001e24441c4283c00641d07000d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 887954640 1250 887953390 887953399
    0xc030f051c23040b01080f0615060a1101050c030403110102090a03111318051c21140708040b0105060903030711010c05030a020f2e0b0105040f090f0b0d0201090e06 72
    0x200410741c0e00d01c0c9240207590031190b29504a00401100c6c50410900c5000c80468000d0b02040c200504440081200c842d10207001d2200495250035040c0900e80f041c0000d5540c0d00280018542001000000d83c0112003c48c003140e4803c7c0c924500841c14803d40d655520003401413400141161165402c0741c0d2442101c0740d0200c0d00201c1010851032900640303400c404942c2c400c249854181c60310f00d04019800085100558905429100711680460803092000120425039960000d40385510007500c07068882519468100090001c0741d503020300300e1071065000d0140004140d0b291410403145100b010b0841b5455030044c005e45d00803800001c80c0c0210701005042281d10111036030b5409007140c000380c0540c00035800007621401c4401092011220b02034030303209400b625020420940856800d1524070f000800d0380c4050480860f405034080794040c0c6020f046070b0343c01690300c4100002070302c1c0b4800301d072186504024400000381001100c171924254140c55544403182000324820b41140010504c0b03030f00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 887955890 1250 887954640 887954681
    0xa06050f01031e020a0207150201020a021c1404080f160513051008240f01031703070e22140c1204170f030405010c0e031f0603120c030f051c 62
    0x10007002c1c4010640c02c1603d40240126234500105e40ca800c3c00070380c01c1802564010001c00404d6039010550003000017078144035002500a11000310b40da101e084420b120602c1c1c1c00580800d103e040015208a046448070440d000b8242101d080c0221208034800d1540109240f0300300340d4290803603080707030b50700003500c101824035103607941d03407052034031300d030b060480d00b0040c8184184405000c01034042607010442c00070354402d652540d07039490b80343c01152000c02045800071001c9a261031081d684030f112004010100004118209040604a54000a001c4900e0318002c1440a01d80b00e900300c00340304204c00103010342020403103061400d0340b1000a0003140c042403007903062180c000300b071005051084404040c4940f2860585091380c2111004000760007403014440d0800d159940001e0408822030f04240e0081c0030b01030034803642015012a400c01020500c03030f841402406a448900d900d9003030700a80e00c400c00040c061406856520a100a4440b960886c0020315440034854008603d000c3e80d01c004100c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 887957140 1250 887955890 887955941
    0xa030e011107111512060603041e080306010f080903090d03090806271c110c280b0403030f0e011202070b01030b07140d0e1603030302040501080a06050f0103 69
    0x45503803140c2c408036140c0c2441d1003200d250b03081a42c80c801c418054448003c2c58602951a05000081c00900245c410710740000090104103000900c1c141a4605204011600400b803410640e942c004a07032490000d050f810711004224821401c141c064100741020718075004200d024002c1c13030300d10184103030b00344034202d0f2000034411400c1008610801c0c0b0b0f42101c00340107025410220724031501c140381c884654007105451803045106070b0000980022401c0c0160340e9201c0c000304c01d007003106013040c859012840d0740948000242603a079050114800e082d484003001d880d0948007a20740158040680000c5414807241580d50044405040400d014144402121184034100e016030384941e00481c1c40319604001007040015140502d500100a400c0c81d2044107580d400307104443c00342100c00324080d80c46a204842c10032040c01a40c0285110081078045030341c581c00c028019600c00d20500e80001d05403000100b00c040b003845014244d41d0b00400d0510084416401103015025007076401c0f00c0d508113403c9408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 887958390 1250 887957140 887957171
    0x306132f1c051029010203090d0c08010908120a05130b0c130b0706060509151e03011415030303071d01090503030d0605010e0906030a140a0b0a0b0f0a06050a030e01 72
    0x40c1820b05220b40400c1004040201c541801d41c1c1e00702c1c0c040d51482c140c1d4004d030b0603038000c8103a44040205a461001040950500800d480290fa0200405529000901c17050100800083c9190f0203001000c00c1c1d01c0d20340081c1001201d9044545407008034001722a00300003604070a240d60400e4902c00c0a508140c0c07403016103e01e03540244d010004c10400050000c08215440c003410004010854135083e041c034041480c105898880c8030400e10611201805d030451031100c00710014007207070240c02080285030416010600c0030054861030030186aa000c40035903481c001040320700c02d040d070740d44540d80380248400480030351010681003418080c1c60280819161020800344c20100812500072400c940b8110000d4240790b40c841c0f07218050454801088502d84000130004002c036840030041c401c0b40c040c200007504000d01d8560080004d0040b03021321903002895006044005001c80342c8201291120701000030500003882004045402400041982c5000c1d034010050b00c0d00e01000030415035400c0d407052 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 887959640 1250 887958390 887958403
    0x3070503040507050a0b0406120b13020c03220f080a020607060c03090b070206100f0b190203071a0f010e040203070504181a010e100308030411010c020306132f1c05 72
    0x7030306d548201140c1080940d038004042600300309040800c01240d8054000700790000d103801ca1050b022900043e6101034200200100c0d1203030030756601c00d0b40312000700d0919100c2d003503850310844240c0400c03040701241c41e03400070400c40500f40c0d00404084c40c1005543d100300103002010409424140d60f01c030800d002c2007100007441c1c41000c040d805071400d80361142c81480064040e420001ca101e500e8a014007840400e18200c031410350a506580d0445602d40c0e500300d146110761a0028400d60000700a0036040102c1c01200e80036845503440c0b8020b032380e20741c80300482d641c008541c040d50590102c2d10030001400d0a030f0040c01c100b540c0704000305000a542e1503500407040c48140200304482c400c030040064150b115841d90300440b40410030105140344d62aa4112400041c2014101e000040c40c02241c0b03038043c3c5542c0361070270780c0502038641c50315120320003405070129100143c07020325200040b84505005c40c3d20500b00d03e5110211210480803c0302800340c055005140ca401c0900c551710301d90302142c0100501c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 887960890 1250 887959640 887959649
    0x3050a060321021e0703080706150909050705010507081b03091c110102060c04171609240f060503130c150e041104152001140906010b03070503040507050a 68
    0x1111250340081001385030013840c0401c80420001a0200c4003200404940328003244d4008840c2519000c40741030a000800003014200344500d090000010b040c0c04076000301d01050301450540747c03665615001918148114900200040010803030107450903580080448070180000840b030900101801003145c103001c0c41d0b0300001e19a2044141d908000000303100c115010740a10240c81d482c00d01d10300a0640e805980102d118282e51a21511400201000075940e0081c504d80710740707800ea5843d00703814001e00020302c00a01c1c461a9585109444d005205400110340f4541287c800480c90498220390340d0b04068071a42030041d1030b804c1359001c00c000c00d43c541c000c2c00b1102c1755104031320740d03903c4003501e02030146403614006d504118105e1403086804044d5802c464a280c00c113211503481c050b080301c0703020f03e51105081c2c0f03000c08100d548031030205500103550740c01102c2000f24942c440c1c21051741c1c1c0d103100340310705400396504100082d802c1d03100f0b40107990441c1c856003c68039455143c800007544071280e0f810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 887962140 1250 887960890 887960933
    0x304230d0e040b100c080313210e040507050d09060b040603050c1002011a010804051603080a0909020702030a030315090c0c1e0c2603130602070e0f0703050a0603 71
    0x91401e190715051003014800c000072a5070902c0d1240c0c0001c060304000c190b14010f000350300040300040384504141801400941d1101081000141101c228026022218010030009003070801e8076840741070a104290207030205031121810888070b080900c2c064011071404880e0749803075a80201d00d940b40c50061501841c4501c015180600c09942030000000c00791014800f103a051a6465680340c135416103168040000f0b180c4203203c1e50350350520914141c000c1561100541181e00c0010500842c000a0281ca000d2541e0b1300c0d48007a6101a00e0303050b80141c01c1d019625030080c40340c0500080c041e90005034114050005003446654800c030b21022210720144c1c6501041d549698a0100300090350301d03007159012040b0602011401d511261143c080c03d00402500c40f80a100038038004441d40e07413180320400103a080326aa450401002c10724400244a21005403251080104209400d43c2c00c0a21422046242811540e0703051300840103401d01078143e00741c0300e07541c03040400840d020074464000d0f20502d60 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 887963390 1250 887962140 887962157
    0xf090c0f041d0f0f04061104170607020c06040f0e0a091a0105040b311107050106030510051909060204090632010e210604050f0d0f050304230d 63
    0x40e50416042c400520b500350788408442007002503580c01c01c0c0c694000d40c01400008900a10789030038145440369420501d03000a050901004180e80050014411405030307090742e881c202c151080c001c0500942c000ca03201039444182c28001c0480440600750712003801a800f003050b48141e20350030000c070006804000301440315001403145080c0343c00342c1c080520042d2101d107050075150400d115041c058000088002410314844c01c44984c168001c48581b04180040715500c3d1010b1500038001c10540c03004441c28042c1801100c469802c070b2040620036400d00c009240404440444a80102100401124038036824000031405001910a2401074040000040500c1d40c02e036081895a4204403503603803a05440180100150364881c1a4482ca41025a10a44492804103000307440502c0c1740490319840c46140204414000002020311403079075018182c8200c1e4003071103011a001602c0d00560300120700d08001160014220418021480110540004a4011030480c203030034040034085500001e0180c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 887964640 1250 887963390 887963429
    0xa0302010b031b0609040b1e010215060105030f0405150f092509090f350a0207032a0602030d180507090207051c080f0609060f090c0f04 60
    0x9201c0d810052004800405003696010a01d00002c3c0c24048290b01030f400104050207542c070740340c20079030440354014000841d51003103002504050b00c1d036a19181c0140703d0740e030031401c6182e42d50380d81501481d0103940b002d14542d40d00103256141711000e04100d0b10fa03c220309020a0341e849011103107001d01c3c1005650300369800c00303000940c80c0451a003041443c0140041c40d12801c44205102c1c00100e4800510214400d44241800044006070510103803c45100c0381a08010101141420080c0d4821701c07040c1c021310380a042403005a00400000b00c016a000e05000d002251950f0024600c07000304400b4840d21203050041184c00c070249902000160744081035071040542d450050101c1c00541d00001c050080c015111f050385e0300d00c580f14100c0c0c1a40d00140c0c680034407000b0302c400a103c2d0f09103640080001c8580d00018042181101c0341d600360b0000da0302041651074515040350061100403c1c2112040c80c020802c4075254010b0086e401d0160200701582c0d8214a0703002510051800c4240581e025600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 887965890 1250 887964640 887964643
    0x20309030307201510180c020106060809100b040f0f0b010905030a03050d05041a070e0a090606022512080d060b09090109091a0c0d0c030203061c0c0b0c0a0302 70
    0xc10710115021051400c43d41040b14001490040c0c00c90090f5507203e494890040c018031a80b00da4100e50344122100844040c01c0d04682c2141201e65031640c000c01c180c40d580c8008440d051303003d80303c01d40c154000c0e105a45002105400201211000174400501d1501d40c02c0301d841161664114040075503291040c1d0307076041da000f241d02c5000b0130050f8003400172054039940042c11031260b2000c54141c1662800804c0500282524920b1011a030719400d00c440e05004001403c0c03921b1001390644180170440010500400724052001110482c2e0001c2c003581c49000b803044009819a655120b8405580d00d001458104e4441c1e18500103000c2c544250350303002c0c00480142940c07596085000000c90411109189441e541980c90455520b1a0700283e411511710700905490807030b810426076809400148030402d01d02c01c3c01064015400700c0200701075000d4074030590a03130104541c442c1e0b002c400c00c0d808402a010452a035100b0720b00c156201d11005460310b00c1e0072a40d4000141811066000b410940d040540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 887967140 1250 887965890 887965907
    0x30f0606081204050111100e16060f0e010509011106010909060506030105010303200a0b07090602010e121b0a06060305010b0328020409110405070e03071a0f070213020309030307 78
    0x901c000940b840d4003000c0040200380c40f4503c0b03020b0410030090204140144103128854440440c1c180c18000c45000000721503440c01c0411006409290b00640000e8240c00784800e00c1c4400381c29140caa034000c880c200151081c1c0c12692a16052104903111641c048100340a4540030b406403010000300f818040c1044012100010003407402a0f00d0040103001280d080608036503502c240d4070840d01041020500b003070520400c1203000f0407003c045014048040d400050540560301c0c641e0023001000c0c04480202e558110284100e0b143d000d0410038844203585801c403014444984004a5510351030a40e90b40d001c0390781d298415101655554503500083c68140314004100d03c0c50700426030031080c0302d03810444205858130000d2084e95103186000411070003440c602e108000c0144100841d00e00101e0191065072066a00b038428040c5072408680c0248409071462018559030140742040c00ba24a4007801d0b901100060b680030102080c0b800410756180010351042100201841d03e0741004a80a0603259 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 887968390 1250 887967140 887967149
    0xd0f0c12030c031a21030c0f0a1202030304150e031204121815080601111506010f21021e030406020702040525270b07050613050a0b060f0a030f0606 65
    0xa00d0130030f80c44043ea8034414010343c2440c036560140601890750490b0351651140c0b010154603401001c14101d209140895030300b4106000b0722041c0030a0b51854000c0380c40b84802c84004040f007155880c10717032034401c0725031080f01c075000710800701c9141c00070242d01c1c03025100b02210b040340c1036200c0d20006a00542c0c00701140450030241d084810201d410210240e4035660303142040d80403c1002d50010f00140c3c030079103100181c401c501c425140c0266641e0300d02070003410125a440d010618044d03446c01c0071886541c3e46d5481c42c1400d003174000480310f4420180c010758040524207100703246010703640c188009684001c50189209a07401680e8002900c140300540303100604400d4030003401d0101110350305c07030348800580c01c882c0c6241c00c5655000200590200c140c05030740000f100d81c041310740481c004110900800c03c0ca0f010b4403c440e01903440082c0f6a1807250346010051168000000200c000343c04008441e41187d03000b4203070480c2c0118100880d94510b015441921443c00707010703920301030141c940f25500180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 887969640 1250 887968390 887968421
    0x30a0609030e0d111e150304020609060406031409071518080607081009060b030a0b0a15180e06030c21190303050a050105011d03010b0d0525080d0f0c12030c03 70
    0x17803682400140d8644c440c1441100d0703201d8004002000c558a4074112002c10f01e004199644a030b40303698004009240c80780c800441248404080342c000300000a002d011282580b113507074070031401c541080b01c00a40e03041d16201c16203821440800c180c0410320800c4e01c40c10b465078945070603160240300030724170040b60340c041c0d02e00515000090103240d00c02401c43e0380c000d50070035020406161600118a1014050707006440d0000124521000940e0000f000c0b140c7d60700c0d01c403a0f04002900c483d111a0b009200362081a4564400303c0e03c001740e814000020141c3d08007d02e2035601104a40341001d00b0240301140e403c943c0b1b28002085410543c152040070307009902404200055070501001900700740c50b0420041c0c800482d0740c0100e81554094100702e00ca6071002c0c200461064041c60007aa0320081d02921888056402c207800001c00b4859a0060480303002000416044c1b680800c00d44059001185510400c5070b40800070b0041440400e202980004a50300042c1d5200303a80c00040449590b034015040740e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 887970890 1250 887969640 887969689
    0xc060f1a060724151e141c1101031119030b010504080d0f2006150f04141602031c0b0d0b040b090d1407061104032f01080402030a0609030e0d11 63
    0x445d0300d03071042d1042d40d4503160014111803035000000c241c64100d01c41c00f0802020b08040804001074290a041c821030282c0b41071004480c2c1d0410f80f44c103801441070f03a588001c110315800300020b03c2a00881d2861006060003071425403244425406c005041200300f002c513003800d00800030141d001103035001c210100c0c50b15081c510500d010294841d00d001d004815116140c45d004800755444a081d0a94003100a200300481890040e0403030f82d40740d08840184007103030302888400d00c9a00102c111252a24801d8890b41d20900d0f50000710001c0000752030a40d00451500d40110000381c3c80e01180d40142c3c01162180703024501031a98510b4194441101170410604d000e0158600c4481e07400d071103070300b54000130106119400c096250a00e01480d0300241440700c4444c071010b500c41c0c3c04c082507065001c141d0001c84c20710007a80c3c0107460000050750b0080d0198840700b103800104140790300040c5168828607201441e03201080014101020385101602c1114114801c00300616142d02c3c081c0003807100442c012003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 887972140 1250 887970890 887970929
    0x1207090e070c081b010e070519030f060209090702011d07051c050c060f070c09020421050c190f080606030604030807030b0d030c060f1a06072415 64
    0xc02009441181804074141098040060701e805643d41854420f820b941a401c164050718041c0401401807145801001c0002c601c0781405034121059104e030340034204a151071aa907a940f0300011071000c0c0d0302154280017402c01c1d40c0d0341c241c665006898581c008540680c4103030044880c00c800c0d00156096501c01501040310b03446407004002d034076010a40d80790000c034442c1415402d1020303c1c98019401035001030040300030b00003400602500c0b4003030080d847c00980c64074848000ca00c0b0b01d000e039000180700c942010180211000c6520380c0d441c4284140e0391840d84400100f14968003102c03418141203000e4100740903400545440100410150340200307041e0400102082d2200070150020b820054502c0009130f5460090304505101000648444285a1f282c20001c0c81904140d0045442c80d05201404440c01f1690003203102c21200140d0310740c0c50403480000c11001e80e000c80404c45848c018001c080050f802c2c08081e032401802a4000454403125040305007150100c19089241111103079101500c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 887973390 1250 887972140 887972159
    0x40c0801091104080d050c071e030204090201031509050a0e06040206181206090610061d04021606021b010b03120d2a11010b040b0105030f070306030b010b120709 71
    0x40c11540301000000c0c2d542c0c0c05a208048510075504407015512520100500340c50780b0000a02c40303646c50f9400d43d8030443e00c1c1c10b1420a1171042d41404c01c220080c050f01400036103410362014440901c1414001500e00d0740722900719844516074030446141d55228200620b043d614003c21100f40705040c0174101c540b4043d40051080c1c0501107085075070392a0408502599281c031003132000140301050450b0803a103003141603156602d00c100c9c1c1401c2d06400765100055054051849a0b075401000780c0052207503003402c0f0130b0000940150048aa4120000000101140f07440c0700a059032103000c0c20780c011551181100c5429208000d840c10301950003c5030040008122100752115051183d42c007103113441c40d80300130354002203a03014505001e0140314202803055421510000907165044020b200400e20f6101f00400c0b5109106118042081000061004242a440c0c654041407500300003542a4517501c8501061800742c10150390740000150002e410388194000c0c59000c0e50529003404440d09010701d41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 887974640 1250 887973390 887973407
    0x605100311010311180415080a050d090e2404090507030203011b0c0803100510030b090105060f0a0e030a050715120b150c01112a0d0f0f03020412030504060e040c 71
    0x2000501c0040002d08540d46e1039800510b00400d800f10362845080c0c0303411029440d400100401c80f170078401e1010a91555018a17044d4085031070140114940754ac075500541c5800345c64810508052590701c408003480c0e40c0390b12071201182e00a0700107014a9003588185801c60300b1541c48800200903042078201d03120360042c606001541c1c0a81455200c0d2a24008a1098146504115400401a200420065850350013417011000440e1590070a0f61b8030020310000384911801d040c00e0005c20003c4203005030103690500c1d003248c00a0119014600c2a485450900c607042d00110039504030404402c00e10742d80701c81000d080042d0440c0401c089000700d0001402012080f080307100251020501e00720000d07080d800b9421558849400e1540c80b200f0f0181e00040c110110034003108029009028442140000303010442101a034484d8026070410403401c0d41d083c040540d04c481010380800001c21040d00071840006d00e14425200c880d01e1b5821b00c14044d002c0d0003003080d4103000d90302c2c2803800d0704c0459100000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 887975890 1250 887974640 887974657
    0x9210c0d2106090b090f01080c040c20030a08010e0c0a0305370e0f03090103091b26010c0f05090402070b1008060f1e070c0605100311010311 62
    0x302014002801d0044072070070208120448080c0307403074400a4160742c0c68120b02c5168008503003004c419038500c0c0c00105c261800780100203071948480e501d00b00ea030800d80c5c008110b01c03100d814045220034000c5800c00e544580c44442d6940d50b04086031070001c680c1c09c05600ea003d0481198244e0452a200008080c640030300e2480208041e101e00205081c2c8407010118500c612929a84107103840303112800e400c100301c0b007001112001d46401c04084e840c00000c0380080360001460080c502c0c1002c403200440261100b82004e5650b0311038440324030100c084901e03099004001424600c5201c60b040c0303001d080000504500800f0b1039041000c58480c155209000344000c2c0d4843c28050f440e5000d08001c28024051124004c094a42000511030700e801c06002c004221018402100ea2a50702d8060840c0c154905507500307804030501401840044003000794042c1c1c0100c41c0d280c4280035060b50b4580c0710a03540203542c03020100c113492405009104078100c081c0000c580c282014411102e10312a081c4c22442605071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 887977140 1250 887975890 887975897
    0x7020a18051b07080a031107030c140a0804030f170705010902030106060c030c0b07050409020f0d050a060f12031b0308150402030c22090c18140604061209060509210c0d 74
    0xaa84a01720f00a6100c2c090310540b5049090716503d039454090107103074200c001514140e091a4803a01a00000130f100303642d880d80079050500b0140745075942c0b2001803080030100c400b00b12440b0a10310f483e101c500504106402a0001300d08000c06005241c2140e2a61304281d040003400b40800d8003180d003002070080c1c4a580071002d0301140c0d03602c1d10129500d0140e42c00c004407032800003400c8800030300ea42c00588407100c142c15003005032713889004548048907550700c50902078a401c100100400801100a006142d0080c180300d01484940038011611180d604800c4010910302c80038041800280c0c1a002c84103001036804500d14141405404090b02401000401612080340c1128540420505050041c84400024071540001c04000b40441020321151040480d0150002585000c000040e020307540d009081e482ca06070400c8411201190381c14940b0004540340d0307a4190000d107152240900c82c0034000050300b004010034580b05100c0c3c0203d050500328030b0b418030400f14089030100320840305000504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 887978390 1250 887977140 887977147
    0x10e04080a0e0d02130c0936110d0207031d031b150c030405091003020105120703020c150a0b183426040b0f0c07020a18051b0708 57
    0x400243d01080002c070700941103001034640f20003000e075a401c15651990030ba290203102d59142c2c1046402c0083c1c100b00380c0440c0000310604c00140e42089400303078421020940114104801501c0c00003103900160f5a44c0800c0d40c001902d20a06520468000c5581c48031002c104400d26840d001a80d0380c9024070032402e210069800c400d0199580c1407182c5103042640c40c03041c3e1150a80385180751240c00c035114680c050001c0d14001140c108100f0713003600a8940c1615441d00b0422103100181060400428060138540c1c20001c4c1010b42d03604100d14187d46603989442440e61800364070040644590340500c0d801600c91100840b010310502a031141d02c020405410915411400149101141081c00701d03030440d0261884c0312002c6034001100680041c00841c1c04441c5028040c56400000c000c0f603010717080300c0c4400041044281c0448809400881c416042420304031a50002250040030b40e0100303030010112420790002c2892405041c3d40054440c01134100d103c8003105507070f928410403500811001002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 887979640 1250 887978390 887978417
    0x1080115052206030e0604080304080d02090316051903020d0f1a0f0403020c1503060d020103111c2d05090307060e0f0105090304060903060b0301020702031f05010e04080a 75
    0x210251210782c03030142d003031186201d0a01110404140ca0b03001d244002814030081c100400380000b1801d005c0d503401509503165503100c3c1c03111103035038200f4441c008500fa020009205582e41c20040c5480c00100c200552040740d00e40004c00000500fa01c5002840200b40c030404c00c007683e248400410040d400080c4030042c0815031500b90440e800d00014000b526015034188100081d48101d0544124440e40840b4420880c0404221000e12000301340808504d0420000c2c1e001d040034031240010900c18140400c800313441c1440c01380300e03420014440d0300041002102c414407c25502a1041e180d0800e442d0014500c5d84a8030341b40c01104c0c4100e480c03207054170b81000ca00c0c445410003c0f900e860360800c1c000c100500d805a5203644a03403950051034801e41c200000b1904010000c000c44040340c1c00740c0c54003ea00d528680d500c3c006002415001c2c4e61555082c05a0700150310706002c81c0604900401c40a0240000c00010a003102c80682024500c1c3e00366504010004e68031100f00d9007005034a0a1000000907103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 887980890 1250 887979640 887979647
    0x10f020c011202040b03010b0c0106120f030e030f030c010212060a0305030405061b070e090c0a15110a080d06210302151302030d110c030604020607060903140c0a120e01080115 77
    0xc0f98085020401c0001c0002341c802251800f5201385d05015000384951641c405140e440c4400b4040c025040c0c6400320818000240191100815140060159048400042521ba0840d00603a10008481e5000140b1140c4840c8240365507900c108111a005c450394250b4403201c0d9039014500603640180303800100740422220128090305010400800c403405a074566401c041c001500fa02d0000c880d03c1404a61002454555400c03800c1d501c5c20600b80d181c131510303180c0850b44881a417806400c0360042d00e00e103001240703810009000105002c580400c10320b140050344904000d0480d0780d29500c94050504900282d401f1031202c0c04178020020650701a01c0b407441661994400440095142c07040d118000e0b0030365088591041d44059150580ea100580c400906444003012a002940702d10100410300002c2c1840e8411003440c0e0003841d01100701030103401c00c136005a010707081c101d92035804101010108a8010201c51680800c3c2c0b601080801241001800100b010701400400d90286030050000307130320 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 887982140 1250 887980890 887980897
    0x160e010b0f0c0a0807030306140d0f11120102070c05011e120218032a0604030f1415040809040f060b0307110c2808030309100b0a0f23010f020c011202 66
    0x400480d5555544201c6c83c02030010080da1044142541d03400b95080400d00d0300307010000000c1d8102401d54054100781d5540d117061440048090303800341d00f040c0d002d0100f10702440985101485290160642800e040000d090784200300701110110411440c41d0020a61100c41012145001000940c4400101c2e0303c200300340bc403021174280c05218143c4941e044043c141e40c0c1c00300340b1040c04032075494400000213000e1184114040608078241002c1000001038250040e0140030301400e007655000c0c1e501da4401d0920300800d880c151001e8802055018483c81d1034804c14442000c0058204a554509038000d51035006c001c3c0400d0510105000316944410300b4056071000070001011000c0e040e03080240d15120203600c103004042d107030040101054444000044900403402d0f800203001903a183c034500000b501481e1b041c02c1d082507000c2c1c00014900a44c3d81d20781301805644400c3d149201032403c1d80304d18a401d800b0751504109501200448540d004540c0d00c81d182c0003071a00140c1e41a8113840c0304007a11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 887983390 1250 887982140 887982143
    0x60604030204140604060501030e0c011206091409300a0c05011118040e1f020f19030c090f090917191106010b0912100e160e010b0f0c0a 60
    0xa08142c4110f0003e0504a0058032610040f1400c2000b079454400450460b80910088065a800800324400725801100d1507007d02a440402060841d01c4005070001c2d0b421820000c482d20803420300307210b032046c0c1c00d110350011485c2e520ba0351721212582019501d594400c00d60300814030a0000f80d00d48920b480f4090746c9409541180081c480600f0340300075944650700801c0680e880c0c0c4140e241d10100ca00d800d01440a0700007201c4000e001c5480980140c11504440b00b4090803107540c2045000c010f03441c000050003d20141d609401c28403005140090300742c808041420b4108030644070300b8050840717900c54120959000a000284440740c03880e250005502c034031000014140c000c24a160500b04040d800511007040e551400c0c207907042134021903038514080c0150724076041c0230f0200070b800d4100b400e407681c90b40c2c0300041110b0a03d500d07118982c04450560350a4149038100b0700300c00c012040040b596400604c0204400c0c1340c50740c5050b40c103103030310b015450804104840c00611968600ba04010500d4184e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 887984640 1250 887983390 887983399
    0x6020d0507200f040615110f0c122811030c0108040803071205100f0e0106050706020d090210030e06060d2012060c1908090d0f1416060f02031e0606040302 68
    0x29485203c80c1745c100e00c0300c11b54000040c0400e10141c041c1c1401140e103800a40100004104c0050700c10108860480c100b40301c1d400d0303442007041c01c6c030b0040808802c100d03513a00414003c0800480505140c40c1c0414000c0c0c469010f07074030441c1085e849991006a09074041d070443c2803540c80307443d81c1104580303912001c12024810b40c145401d000310149007270b0486044844041034014940e0f510710184000c2c0b0002d100c2d900c04a00144840c0c0045a5690024420682c1906002038110f00ea9400242c0d0b06220130307401c0f80040e0303684d00d107400701240402025070001411103542815842c0d5641e801c0c402003a03040d40ca503070385c1d065800e4102c50b501d0306403031103012242c00c0f81503800c030b80750042a84003103070000d01c980c1568403142c4014621190044003d140981c484602905961510010036200c00b0140711181c0d0030098158902503400d002100501400300c183d581c1110000c0160825105652081c164582000d104009219412460341c81080c5203c0000140b4980c030354402c00090300310b01440d480690407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 887985890 1250 887984640 887984651
    0x118020708070b0c04090923071a220801050603100b0310020904060518070909050c0708071506080c1203040e160e040f020705191709131506020d0507200f04 69
    0x30007202641e44408440880715404c4c0d00c2d031400340823907500d000c103104030002c00c00a24a08107004003080003c100310a90700e40302941092aa41162212001b254044185655038100780300c86840d042c00001114000d01c1c00511400420750006a25176140c916081d0300158005500d1006481c3d54220800a050041040e42e510070022482200ba050481e01e1100003825848085101300e240d2040d0360088205000e140d00b0240d0503135420206510002060b600340040c60018131040d50385020b0030000d800404042c0142c03c0000081c041031202c1100c5052440d0024081403000c6800d454030070317610000781c90450080514400050318802c51010003075070014103214010298061a4000b010003134403030b100b06c4010480c1c7c2c030103160140140b1b200003020380c1c482c803801d41e143d103800501801018400400104400100c28040000c44e1010008481c0d6800b0141080042580500c41005020681d082945c1362410356075800c10f912f20510000300805070100d043e00c5403074481d1101a90030007400b0307000700300d07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 887987140 1250 887985890 887985893
    0x103110d0915090b0f0a02090a0b04080d1e1404080d09170d020a0b1e0109050109050105150a0f0309060e100c050a0c1214120118020708070b0c040909 66
    0x1030201c004040e21035214110031002003814510444002a80140b0801d04035104d90b6000310070960003410b03038070520b50240031008407540c0300100880203045c190303c016500d80c1303440903403400e21030080c0c99102803041509400082d0380d0406900a584080e070325010081c1d00a00610804a0256802044d0701d0700c190380f0700460894000f080202905c0c9201e04942840b1541c990700d42d50b4a40b58141c00c401a0010750385800054002c411403178010214440c400c4002115801d11241d14809a02c10200fa54558004008646291107241c0c0540401e0b80c04411500703005034080814800c52401d00100840600548079140c4254001140c465000c00e044c01200201c91034103558812010039088080d10304000202424008d404036525101a6201e20803c01290b442d5a041d2240503000e80c41403003150404002c1068641c402441d43c0a11005141159410300d140888000034013200040e030b0b58410040200070541107400e58105c2c0380c4c002d800f20f04550b115a101c0f9100e01955200c41042800c0000890 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 887988390 1250 887987140 887987167
    0x20304081009030e060415030e101a1003050105030307032a060b03070f050109050405090a14030a110d090e103b22031403180d03141302010311 63
    0x1015029a580103c4c0d13078008801c0007880e110743e102d2900410310404288001350b010350414840303418000107480c103400760725502030207444c6a090a050344030419140e000d1a45040007120301d8141e041c0c68201b1540d070402003c00d64a114503100a1700b03104450b80312000412242c08076098000340b0840c84c94202030503141c41400f404203846100c0c403074021a90f0104407548a03440304001c54005940d104002850642480000c22014000185074090082d1060100e0040c5a074440780c011094011a0b485141080081081c0e050380b05800d982d803c403050039044680d02984c4001602c4248034004020303112506030104020380ca51150240c0086100889100714180c0704600046070b008001100d540583d20030418411300483d0381c0501c19040301c100706a583e21002c034840001d0310904000707000741301e00c10050b083e40d00301b25a402412202c000c00344080341e800b40005004909142001c1c040d4880c040000d6009002c0100700111032102551810b041d60b1203a0403110040802d02001592050004240c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 887989640 1250 887988390 887988401
    0x1e09090b0109140907050d021309030c020306010605041203082203020607020f060c0d090302120706020a14130311010e060403050102030105150c1914060a05040204150f1202010203040810 82
    0x6041078501500105034403e5503251038429560000981040750800f420401c076042d01c01d0085c0d0708a1150b0040a0100001e0b11030050164000d8980d403802213102c3c030415191842c140c01007070400c8424082006008243c5085285559040c01c141116540744403d040001001d41e4080f030b840500c40c1c0110003410b4010881c14000c224aa00307450b826850801c3e0143d4580b01900c15560007141007203071103140b6003903074058a00f1034800d206440f400001c00c045040150455501074440c1580041c0a070880c5804c403d0820900540701c19090500010710b130705010940c01d84c4009408070200b0441c0ba0102c0c0e06c03550030b0341071901c0014025a240e0361241860340c000d4009004080c019201c0456200d6050000d4054410901c01c24004002c1114101081c140040c41e00e5030850340039150038000d04e1540c1060126070721902e074500001405140a00403c03041d0f0f601068003d42d044100320041c000e05285109210070758540d01d000d07002411480c40100d19501c9260302c592068040c51145100e001505c3d000b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 887990890 1250 887989640 887989649
    0x7080d0b0a060c0804030210020c03030403200108040b3103020a05070b0405060307270e070210050118020304021c2006030708161e050714010212011e09090b01 70
    0x31946070780d16140241c1d801000414098010344080c4410401403800400d0b913115030b0b01506c155a0201050800f0a00d550401e400480e2040101d80c00c14400c882000110003c2200c00d01c1c1c00701c1d250801d42c8130301c1d101c10b4005d071a84541038240d10160b9060038145803032440c041180894030a0051003820001d4542d000390710308841a0150440c0000c001c9050416907054440040c500c9183d61074800040c0d034a20b071484100e01c925004480040c0c40001034400c01d5005041d0060604521b250034407000b400d100900c80303900c444510307000040c01044244440000c441900700001680d90301c95000080c103e008490940040c0420300e1429400c201050003803107600b03641c00f800ba0303414050800422071280811121390740007540307080014990040000380e0303224109150404c40d5045080d0850401e401e02550a10310214200040311020403100c80c03840b00e00000d180f8000c6090003240105806090018447c4100303548018000c1850130400c03c00100051200c10820050f04241d49001c0c040e00c41c00b40314 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 887992140 1250 887990890 887990899
    0x3030109060509010e0c09060d060803040312120507020c010e0f04050103080909071e1b1401020322050a02040203100902030906060108060f0d080a21050405010c050f03070c02040207080d0b 83
    0x1170031a81d40656140650300840c070460500e25a8401d00030035400585601e0151900c9000c00107001c4018030086c40618001e007000d0b008441c52043c0900f0300340045060880262a005c104030641c0d601240221801100b440d01030741715400030002401000b2400c0100e40e0081c5402d0002082110140085c01c200303405940200c5943ea6116007541d106d50022615000344500b180034028651040c0d044011488950001c1142e801c000d40392040062607508402880d40e60000a0195814010381c002c4000c40d8043c0c1600351001040d60380c2c80d114442c0440c0240201d40210204909441101da80d0b000380015502c11074807442c00c40003940d0380300000d85420740429641e0020a1603801c2c55460002e1194014002e6841d01030540e6801d07250fa0b02280e9040f081081e41d11030649901040d1540c4118484010400302e81803c1030706006007140c0041c2c80c543c3c1446020403c110100c0100802d40c0c1d80881da0b41410340c180f030401e0022401900c100c0307000410710a0009030310b220b01c0c00030b6485501007030700944 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 887993390 1250 887992140 887992159
    0xf02030d240e0c22030501140402040e030702240417100605010e060a080619030516061107091a04050a091103030901050d020c07050a060503040614010f03060c11030301090605 77
    0x1e002c0001d12043d503000c8240c0008001400310115a031103045080c20116900c003815035540d888190031121040114407519103c54203100a610b424090901020700401c040d41c540f01343d613800078480d007104841c000980c840c6038481307051032484176040d10014085403407544405490500e640341c40b203c2c01c11412000d00e160800128a551007810700080361540074000501e84600140142da80c0303100149070592281100c80f00c220124400c4120f0b00043d445640100030209584803a80809100c5400c240704000c0c003001c03403140d52000017450004880c1811000030303511001000280401b007001c251250002d04060a00521280b40d13840000030364082c0d59454000c20f62001003541700d00c6000c08290004105210030100d80714180d004200480a041c12a00740982e204040342d400402030784450042600442003009103e1180600c2c1c59450000c10b1401031503060215a07015800c4501005e0040d40c2e441341e107411040c0c028004000505c042ea01102e0b01c0e90703528190034000e49031034082d26001d000c042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 887994640 1250 887993390 887993399
    0x3150807060c1707020a03060b0a030606080d020105090c030304120c080a210e01050927040f0318150f020f060910060602011107060908040321110f07060f02030d24 72
    0x40090394200d45c2d004001101240c41c41c2c03900e8000e010189030040d4000b08580d03000000440501c9088000e0001c3d00140424124100c0c2c0a402c403003000386040403903004100c0c41d221540c2c01100b1102a1111042e280c05111454141541d0b01d001c5034000d100e241c4580301d41482031100c0300d610000c002d1100d4406c0c01e11341d178200c01c0c111400402c0b44511408160b0900c015910740c6080f03070750800b60000103401070100d000001103111032054152820b981c5000c14920078424141c1c0100111640c5185420102600303150154440c03462108642c0e440c20805080545d00d030540c0309101e20150b85580204030b4945040c0420069180c2012a007035044551505100044003070040c0103000311070862504850174080342c3c0e142c030000b0303001d80030f01100d90b008108400302c00241c100da0480400c0c81d5072720b51034030100e60007000985240e07603159085169501c42d42c03100c443c5c00c00014945050f21924901040c034032140c40b0090340b0f180070740e590204041d410320910a20078000002450a5441c200c0a5046030580c0d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 887995890 1250 887994640 887994683
    0x90a060612020907140c01140103020414040f0201050d090f06050718030c0b03070c150606230702040f021312060c030c0507110a230306220303150807060c 68
    0x200400039000881000004d0807180200703040a2a025501041c1d4075001d2400015421901c90780c07000950f14010400600a50500d48190300b2040e80302e0040841608140d04e80b443c5405039103c00904204000801e040142c105400c105c106541c007100002c800e44051608030040d14044550b000042e040d05c0f100801d00403043c501c0000c891b0010110601c2c2410100110850342c40144854103110985030740e500010010400c035681040d1600001500904004000709405043c51100c42910f40280c400104402248100c480c42581201c0004029003403d003098042c0c041d194042c101d95040c4000050442c610556404040344030305010840c080600800b64100c404106184000400521035080081c034020b00c010b0100d000108034898080e900c03808500c002da560f40d0003101d140c10301020303030300c85003001c002c440c1c0c0050b88100e03401460b40203520502c0300304244d2a800780c00c15840b04080280840d00c0101000a071000034265120b490302c881d0041c1105612420403180044a003905150783e250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 887997140 1250 887995890 887995919
    0x2030411040c0504030f020f030f03190c08040509060409120302070302010e0f06070503040c0e0c3705090612040302010e0f1912030e010507110d0302040f050d1a090a0606 75
    0x9a41c4a0509081c00d6441d00110300800c007000f08c0e00054124030002140c0d0b4100035404401e030400d80210358031803202051300140b0000354040d009003c41501060000344840c000c1d00c056034070079100007800f640e40000080190a200c28041c10b54041601070504d01e0358150000e281e40b41c080c1d0024015120150317081e23603a41c1a019808000b9801c8900841c0341344cc8158029a000b078003070b0701d80d42c041c02c1d1100c000e40c540220541c0d40c490780c5031000507001210b0000740004014070280c1c55103c2004c0300302c01c0747c010010000f00304507000c0081c0000c0b040301e00d9491a00340c8003000c41e03041134044649860700d0f002e4002d1050094149103446031140e480c0d001791380040d40d20210072607401000c030a020700751343c1c401010707020040e0081815103070080b4002116091042610460842c0e840848900040c00c08a0514000f854414101401004203000724010081d411088503420b54544580c4030080c20013410400ca014450010880500244000010b000a4403001c0f180960003c000c0f45d90348500d00c0c440b000703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 887998390 1250 887997140 887997161
    0x3082409070c02030a14010603110108100905130b0f07080c0a0c03121407200f070506070311070e0a060608090d11010e12040306061a1206010513090203041104 70
    0xc000001a1400e00c80c071500500300e44064111441c442e0302e0350362501030780c0c00c501c3c2c1c03202d06a40d5214200140301000030314800c0c100302802d281c0150304111a458a80031514010760a0498950010510740840401680d0382070380c101c01200000d05001007400412401030310307554000b806400203c0c1c1140e042c5000c440b440282c2e44c0b1a01d10320141d542e0b00b80d03080d810b62003911300101c1c1d5911260300d100c2c01c4c00040d144680240c0e690000c00d1000280402c6107515002c03480030f425840704280c07024200000581d80b0036280112a101d031940b110303250807285c00b8038501c0642e03c0b5001d031660001e650340540700e6250103240c60003000c1c09420703100c0004950317401c0c2c1201c0968a1764404083e80190900808030300c250181c6080000c9623224041c040c0915101c0200300d0010800030018080041c007440703100fa400502503480b03d00218005094524065002e109481c0750101d5040c0041240c50303026108030303070030207425403100c40101e940e841d200d1000f0b400456041e6000da0700d608020300c40345058458207600c0c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 887999640 1250 887998390 887998399
    0x10f0b040e0c090907031b0216060e0607050d05030405010f0c0813020a09110d050f0c190504050d030917060709090e0703080d0b011e0206040303180f030824 69
    0x41c68018591481d141c00750480b10542c0c1d041100b1502c0e0384903012854402d204a44000c640e0000002a2680c580119002841190400001c07400444401845101111403034034040e80c0213070f19803001692512510000400c0d600c2a80340031031030aa0000042d500c2240203000030006c1042c0e6113440001d9501e8a411040000c0c203041c006101c640781240f14010700ca0000c0d007081540c0707446102c1c48003140d47c07410148402c43e502040348040f01646020b40c3c2e61001a4801c8641c160038400c0c6500d03801d00074100518101213920340030200a40c803030341c2603400914005121950311002410050a00420340c06410401188016000880c030400601d4078081c03121b940c0c454210031301d01840e000c0101314000312007000e0f014100300040403072813941c083c0080c0494600c1c00100c00341010005008883c8e09800c0c90000860030f049030040d02d0300451065806a01802e000c41d0394990740e2a501d140c45071609000300782c110542c68041c249584128014400c03500d41c45a8988244602004a20820340c403030942e600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 888000890 1250 887999640 887999647
    0x301150f1e080c070609060605040608011802120f070b030708010b0901020d030e0f1209121216061b021506030106050303041202030a020a32031b030309030706080f010f0b 75
    0x1c40c0b092195070f0340022200b04440c200720303240e81e4100c156003960313405450494803200240027500c1c0074400e0000906178030000300051000c00008038600c03140d40c0303406881070409400343d2020103c2440366060700716400c02603c080d582c540c2600c4030340343c1086c1e80700d0b030000f0b05c44400032519002c80c800b1076129402c142c00070300034148104011800781840d250030f0b0710340d0301038100c0001c250301c820081602c0e032031159110319440700c5041052126444803103c0d003030925440100d0000901d0148000c82e06012184c0030180045c2c04542019000703081550301c00e0b0450500c60005000c42940450040203401441c220030000741c0f41c81003014262a024041c20754140c000b04400c00024058243d49a4442d1010b015205a022290001000c5217403951122000000c4610640101114448206992008041004072407940d410100356078800305942507200010600b00045281e40070010f41c4c011002c000c0c100c50540303450b07038802008800c3c2070b0303040c056032031000b070001c00d03140d40c08a201d0003603c807200340c4a401d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 888002140 1250 888000890 888000947
    0xf030a1b050a0c1103010f110712171f0b0414130506031926130b04031a090715030c0305102d080102040b030415060b0a050a02030f0301150f 62
    0x1c040c0413451569415035135060f031100000c6650261a08000035021806c3c2c0707800c01e900700030a444521214550030030200c3c004580940d8000d800403504003510440c4180c54003803e00303000c5008601c03500224030701d00002c200085c188400404140840401340c4803c6082c103003030038003141039400940d200741c1e0540081000201500c89403c0c480700103030041e12220415030200703940b8049441e450070824089100001c50191000002c95580020a0f40b51310140c0b6040c91900d0b10780c20040070003200c59441ca07058010070762008040010102414107580071070780c1030080b0700d800740040110070361120209080030001802c2c034600880c9001210030342e02056401203105032010340104c00a83d0040b0a2000110380415400c000f4070140c0007520103005410355a04140c2003111110f041100601d642606280060040007030100a84101480d18206940c69040038042a0b040d4000c0b446c820758130740800b000000d800d482103550f404243c91603485045410000b03a0080320104400445e1611030841840b0218 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 888003390 1250 888002140 888002153
    0x306050a1a0307061d0a170f06010b090d03180f05180405060601050901170103240902150903011805061503161406070209040c14030d020703060b060f030a1b050a0c 72
    0x1c4441c0304071002c0c000050328403070006d589075401c0d03007126145168040c410310000c0000c010220034000342c0c400500081d850f0100b107207894807411101901030400c510034002050701844040c0c00412080200c0704009480b84200103208400b4800c1e42d200d20f03440c0c210072000d0540901c0c010700a5800001400080ea94030005496507807052000380c2c100302c2c031095000704011964803c00e0280d8461100350446a0181144001500080541b0480360745084844170060b074482034002070040904440e19150200f40001a0040954042c1c0106c0c0303207240c030300c040c04000300840c2481c41484402c4425860340c21020034965104145038900324031003407101090080406d0303140b010503141d03c01000d051401046602246036118203440417255840d48400510175421300c10760f44588403c0c190020101d1580c10b0a00947d124800d21014000c80d642c0d020707881c20f80c6c840e00c0c1214016031460090543da8204418001c0052100f8400a1030000c0a1040d0450b0a44124100e80780d481403035a91160004098403100f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 888004640 1250 888003390 888003407
    0x10b010f03141f030c080a0302010b10080a050703060909210912080c010b060c010212010e060d112110061d06310b0f0901082a0a0306050a1a030706 65
    0x40c2c2c0c40f21090b150000000c2c02c14191180501800000340441d201d15240180c251000341c106580720706404c50204003030039400708602e60702c10303800d45020980341c44420f0180c004006582280141c1402c18072914103001003070344e511020242400c450420205210001c0b0b035500c0450048161004200001a01090030480600b20505c4402c00000d042c0030060006580c43d03016000015440e50085100303804001000d482138014880468514600e01d00300b0000b070f2220380e501034001c1c0010f05003601107815894110744914038400280a01c001c3da90f040c1c000c21355800c4c1b41c407c903080c0182440008030762001c8c941c13482c0103041401b003104009a25018100f1009050440784101090414840ea90407000c011508900c40d1840700000240001c0c580b00340650507070f00000c0b4a0198007030781d0041001801c00141200003081c10700210301c041321543c5a40360030010713400c4c4903580540b0304a00801480a95401341c1d001d100ba2240800148001070f07851ba900d810007a14407a4150014001001903c0c00f84c2c00c071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 888005890 1250 888004640 888004681
    0xc070605070615030b0a0506030c0609060c1c02061006020a150209010516061a042306061608030712090309141507080703030e150c1303080a02010b010f0314 69
    0x800c6010080f99a6a10603d00b80d200344c4400c4648424010a410544215a040403094010327210b01c10250003c00c085100701012a4015540003580d505110f600b4006060a9250103403015901c40000200a50307c103400c0d07928254aa80519000505a0000400040050344900d802130b40c48200900c0f1002504100d5009c1d040c81410419805035400070140d01440610903480001e070300404d404c13003541c4031b200e8010680c0613a280144c070342581c1b04000c204118005d000d03440c2492607920707040407841c41d010b100401c00f40c54042c0781d0190100000c0c3c1002e184251041e80d0713584800341e0300e03200120543d1084600640841c0d0004002d024100710716909584140001e000c0030200c503c91304110b070b8294043c85090300e106e880401c10004055243c064001d00441d4200203104403403510810a48034200a4692910352000003512440000182c888200441e0013074901501c90307075130650180c06400c070304c210a4000b42c41c03102c2203c650341c040d02c1080c0803030010b05204400d40d502c00c00ca00c80d4070340c7d00382e18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 888007140 1250 888005890 888005903
    0x80f07020108064f14090a0c030b070507050307030c0605070e400504110a180e0c060d051f1419050402040308040f1d0402100c0b0c0702090c0c07060507 67
    0x401d000080d518074013401500b8000c40e000903a80b4854a01026540700071b8131002076600003511100100b00399110721410389410411468940d20380e26401d40c3c9034491950000c0450002080500a051b0032036101081980100710038000c660b00e504040f07514000c02d1001c607500c0300048044a041001807002c12207211001c04407010701c031004c1140c0809080b142101d05801035240c1e82003000304a521001e4841882060792212449428003e401c00e4140c091198080e1290356031040c10309501c03041003492500c140183c40031ba90b03584075421a0001d008101c4020099820010010715038942e145903090440e03190441e80c40e441c0c000d82042020100790b000e56465076141c00711021416586510040008500c900102c40d07885141049500c4440c84c15444085060781c0d00040003810816006003584c05641100d0038080b50742001800c0e40e007010000e001500d0000c0d00c80800c500c1421039001042114021100118a995140c030208024841c2c010171103030b1074210050800030b02e402a800b070a0294410030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 888008390 1250 888007140 888007249
    0x120c030b03070b2203030905060309030f0310030317160e03100204151e050702130207171804020429120c03011412060408030a0207080f0702010806 65
    0xd0010b803601070282c0040003102800180c0e95028000c1a01025810441d00030309003500745540c42c09045000d4510401e80039000000c0003950000e13003803085610780707824075448503243d0a1498450020100c1404110b02040a011158007079901c0b810307400b44101030500d10342c21000e100c8042100c082e0024407003181c042c850189540d8190358280007500103020010030004e50400001c0000b4102c207d032180703800b940515012034086003507005044803201d0b50145d07801d8a408410b802940000c1c4034a03c80a04610280c081890168204100824036500d030140b01c0c1c0040e603035600030401288224401ca445000381d404841214110300b80c001901b10340200d500c0350404044403044c0f12404d80443c2d820018080000043c0400c09840d0200c1c40705210030b44d12000c80d0b2101540300c5680d0721016101411418002c40015580c08081e01242c0a19900078011a00da46001400400f01d410422040b804501400001901130510303803580c0707010004024a441c0780580012440080089500c4528035200500c0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 888009640 1250 888008390 888008411
    0x3010506031812310b0c0f0a15050c12070503150415050a091533020105010503061602030901031d030708071a0702071e030210020d080a020301050a0320090c0c120901120c03 76
    0xc8c80302e12002806441d642d200301161a071580300f25030f802409011040002d010720048590840455940040c550910594a4a841c0084031160518041107913000b03051241c05448540c0041d00a401c440080e2000b003205a220a03030790082d654030500001306484d00300c6042010204540c04070100301d510000b90401c6003144500b44562400c03010741040940e44800040000e070508004a541c403c522854038580300680000080d264891505903504142d2a030b450f42114135500010700a00004002c101c1c0d555820b14070b0301e109150010322042d9a0007540007000700388040d80c128030074406d0200e83d0252150500700711f401c2089110b180c00801c400c10420070f0103c0140c8824011009110040d0000c03c0805903c89004040b00e034000c1c40703095031074014030041016440d00e000c0b810a42e03500107030a204203110000880000401c0313212042d8400020018404090100030040c00804c007140d05650ac81900d6a203584141c1c8a100100d600156080d000041e0805c080e50240c4220b8145103004a905c0100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 888010890 1250 888009640 888009643
    0x1120215070c170c040203160305060a05090a0c0201112b0618060e090a12050c16090b030f0624040b10031e060b03010506031812310b0c0f 61
    0x83d084850380c00000000f0b40b0810340c0800c2140c03400c1c40200c07010b500e1440c0c03900c1c130009040100040da9091613100c1000c600540c0d40c800485019000142c0410058030740401620003500c2c00e00030740c00142d440c22110b0b12852460608031601c201540c02c20031105400101802224000101c0190501f47d40710000b03d5104032040b034203403110070070120120301c050a09007665001e0001030b2900c0440e40c000030382100080c00c48807101201c00c8583c1055030301e0f0601c2d0502c4905005041d03541603103000e201000814995035990008035040c400340d04a6001c0050810301a650b4403065850742985151070b0100080481d10003080a29201c002c2c201250071418100407445200150202c0e42c040b907200d0b100441c050b1110081e29100440c0090203200c500e02d8102c1d030025501c4180503c50141400000103001d00c83d5001c043c40001108078102c0d006640c41d03141d1585950404201c1c1015280c2002d6402264400000e0031b58110944001072102c4502d03281c81c040c11907215109041440c0944030303851350507070030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 888012140 1250 888010890 888010913
    0xa060e0f041b170a4d0d060e4c02030709170a080304023007030201141207030905010f021c1d0d0c1e060c170112021507 53
    0x54000280303d900c00e14504460160130b0794100307011004200c0a21950007408103c044101403a100d417080c200c90b80300180c041000d00c840315090300203000001400c10400310764070004031081c554050f540d250f03044003400c1c1109540807089200303018401948003000c030910fa903400161014603c5c0c00c14000100c030380c10300903a0011030320f0101241e4814001c10281d2080c00041c0030082400d03000c1c0103084229a02c1002c18040980068014a103039031050001e4010301480c1c44145460440354030840c1341c030601a0740e4903d01404100d0004030000c0b00c54420746400801e03a84403101c6d5141180c00c0ea030318050304400401c3d0600041e1034a64a0304001c03801c03140c0d544020728181401e10540e8001c0010171407200c056403040c00581d04452a14140e4580805011407080070300c0495241c00300407551182095800b201e18454000701c540700b00703490340d0304210043d0300c01c0d200c070f40054a600e04188124030003003496a40900c00e5200728007107800392000510b070105a4407200c080200010342070541075154044c0c41c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 888013390 1250 888012140 888012179
    0x91505030901050c040f0608060a090501030804031509110d05210c1b0307180212010b0304021e01020712060e0609010e060c0703050d0902060705010c02060a060e0f041b 74
    0x52002040c406001001e004141e4070040b030f91303070309881c052034100b448888185511030322040210b5140405d84a54890004800a0072000d80c288001c0d40c4a003091040c40c0c1c041c3c80100c4809654105d10400360381c460090075851500501001c020b404514180168016800421100c9004d0010039412142c51148d9401e81940d601101c29210101c00400521b4110104501c441c544404600104240c2d400100c07101503800314400078400b1010309222101a000754220322158840c0c46001046003c16400a94480c07070085841c0900c00340d5504078054908007100400f40182c11581091100008800d400020b01d4803031040041e2002456009070b082a81c15210400f040c1d46880d11006282c0342009896082a50035002524059080d0b0b80588284100046206095114014101556111401d88204941200003072000b2401c0e484004d480b54411101c00407458900700300440ea40011200080c0b262165800c0303e076080e00c1d640c840c0f00e965503000400142e0040d103400041a14040b1a0714412641d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 888014640 1250 888013390 888013397
    0x6040317210114040f0212091f02040305071a0d060303120614010804120e0316090e0d0813021305040606090f0b030c09091e031e0322110a180b0d020904030f0915 71
    0x2040381048401da803621279280a069240140014801700f88042050800c440301c0700c50046010b58824039050780350007641d120744800c502d0301034000141600b080410b001d0b041584010070245071202140a4100e001009181c001503203940002d000494070740d0240103580c0c40303081400c91000e003000064600301b006803042c948808807420420140203c6d003d042c0b042c511040140070f05407007070b680003040324030005c0c0f50f020300f190716201e00070940d11000380c0c9010f08001c091041c440b51600c0c0c00e1020281400d480303078001040ca0f2159403050b5082c24400c0441d850001401361141e0300c001000c00130302c1840944402c006004801c0c103000303445101380d80c20507034110034006141ca170304201852600781034086800e00c009060070000c00050002c00c0c00100491884183c125000d07a001e42082e1440f0141d0360350709508044200004514103307041035401c07a06d43c02d00d0062103002841c0e028020b050205c80f2000390030854010100300028022500e44403a0740181c42d000504943d6001008406402c4031980c42c0170 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 888015890 1250 888014640 888014653
    0x60602030409050a05070c0f021314150307060507150b0303030708040614010b0a0f0201060e07020a140d0c080307030b040915142406040317210114040f021209 70
    0x404103000b404e500000c400707030400481c0340160020300103400803000289a803101c040071038215901c9020311405c1e607043d65020007001802c0516502d0783d02080c0c40d0702180240d000380720000b91400040b0034050703d8640c2e6556080c200c195407101c08280aa2030810199629104900016101000518400c034016929443c680c107183c2400c500b00c949003010000b1001483c0700600c025541e40c01249c0e04221903150580c820900c0a004900404554004218150560040c0681203034006504801e082c05070542240c5000284600356480c0b00e0750320310304041143c41d1101e6010450000145074040304a003004108440b4a90010701140c1441d0300483e101039210803c0e607003812440c410302c15819200c0e500b100750b0742407141485241d55605124a151030304140016096a02c0301d0040d0780003950b0094022201083c9a0078031002074100c000888601d00c4c408504500c100001d586243c12100601c60540c40600400c2c24007016144103492045855000c203c2d4043c0100d1103150284240c8140010304071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 888017140 1250 888015890 888015899
    0x20c0a0803040c031506050d0809040209030d0e01171308090105040e04081903051e060f06030406061a281b0f0309080d05041202011106091b0d1a0411040606020304 72
    0x28040c900d2039a0030b1817245009010f001c0e03900e4941c0301d8a0299049090a9241c00260300007034081e1050070007060709401188c0c6039200c3da540100802110300d400346c03145404c004a00f4814041d010040358a052001003114858001c50b4114009200181e010301d0098686611160504210802500c08072000540006d0403004e4400d1482610240e64261070107004508116030030703441c40000024585d8024039560007080b0250303945803a1950010b0040d10083d03d03803501e420068001c10307043c40f42d00c1110300d851024070b28250b0500c003220340010140140c0c017068504100f20120a40f242c1c6401800c1c01034981c1030021400c400d441075001c03a4450308103008141a02d190041211001d0b0b8070680c110750065440b422020b8010007a541580c40140c0180b80304181400101c50441c94903912040303900449042c018850000304c0d0424801800780384601d1103800c4202880404902154060071610180c110705207420b00e08542103402c035026040003001c80910000040480381e85900400259000160420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 888018390 1250 888017140 888017153
    0x503070e010c02010c030815150d0f1404060905150c070201031104180209040204030b070f02070b030c030109020c010e24060f18040312060e060108060a03050d03020c0a0803040c03 79
    0x5465550038a40403a002e455540060a8a01c2506005044c040319100055058958a03241d00300800000d0a03614064078011130855281d04c0005c130940142d041c4401e42a44241c0d500600c10888040721000c401541d4a0f15800000c048403581103599004810142149180d01854180909203000c1c4d56a95080705200140c100c40c015070486480400500040240441c003000400b1814402840176035a8070312000080d0003071050b80c10003050040c040c41440301c407691020401513151065022070700b50640340c01c1603071580d00003100c100c20200000c0006129408464025015182440001190551000c010390741000340c1c044d09020200003c1c81006043c5c0d10926010390040001d8500001c9100d006001c1400700340030645041501200c0404101014404c80c0700e400b410a641e202000015110f1254031400b030800e644880c0069200c40c045000c2d13140c62490701c0d049070352100081800404042e402c0e030113500072046042150080c0744c000350124113040c0055110b1407241c419802814118079249 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 888019640 1250 888018390 888018407
    0xe030c0307180e06330112020c07050306040b10091103071209170307020d2313030609080403110102510f01290922090210030b011b050a12050307 64
    0x17549400c000410441080e6000ba04016210740c403c800541e9500c021712080d85030001551010b0342600c2940d0810051040e100710190044400142000540b540c454250b070903130b82c6100d1410700812080010564103401041120407140c06000301040126039504c1e007455007641041d500303612400000422124030b9050100d0460130300d540c00e14070320310494102003540040309014011641303c0006080030720250105c0184000b140d0050040c0281030840c5010f103500d0300716210451b90b5512001d00010650300100d51030040f60f4900003003a005803080c9000848040500804202d00021500c81ca608000d114945030b032548640b0552105604141c100842c22220590014041d030855690f621407581141003140c10000c03100c01c0301521780140c040000d4609070088801c0200600b80c034995050b42000780c108043e05402100c1481486008039130507001d907080410804d0004041f001c03644402c5031809480c8420500410441e50000c1650f82e504140d00800d0000d903000c81d00100170010481d40c00300d4803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 888020890 1250 888019640 888019711
    0x909032706030b22050f070c050705060a031107050d14040b030a090c17010204050a080a03021002030903041211240a0302030c09120f100c090608340e030c0307180e06 73
    0x488e0b146070ba8603100c1c3c55414070301440d44034480014110401d20703c0b03070700914042c052403149103680f10586d140440e5200b0940100b40041261060809900c1581c0000d0303804450034030203260720b140e0300d0710f10381402090604811590340d401568003080c4032540084103845001100001640c1f541010300700102d54a0907440050a503101580030b000003503021848024008281ca8003584030b84484410b94158015604030048080030760000c2c00c184040c0450074001004c00390754610954684040b84049508002b5003607205000400c4500307400d9109a005680c025200d000b8241009042c030002030b40302168a102240aa00c1312200c00d109070001d010f00d81c0300c003402820070440b0807001030014210a03847d10524061200040000707008404014198010044200b10072503143c0a00030074545080f840b03451000083d002070b40c004554100020440c0042d00010000c1070214a00003110b00310019448414100302e44900c81102d00e00d80c1008000d000d4200c414462007840c50714616045030303802c5a5032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 888022140 1250 888020890 888020897
    0xc010e0f0a0801381f110d09030308100302010918090602030f10060e0a121b06110d260612032a061b0309030f040909032706030b22050f07 61
    0x3500c0f5859845040803d0620481d1a400d0305c2c0080a00050305c041c01c5990038204c0500405494021003984071001c4c10940384a900d540801343c6a0350380041c1e240303006010080c042a00d115042c007554010740b4000e1082c001c00c07013002c25450710540e104000d03070b00144c9151513680c20090602031a01c2d996200c00307002d0110341c036240e000144080005072548643e80304001c0782c03a403038141c110188680e001000d14007010032104040c000343c0d1098001c00d0070003d0681080d490107826101000369104504e07007400305080921105102900200c041500d40005d4055580302840340344202002d94184050403412440c407040002c04000c0c18901c2c0e5081e128403466101c1034115a08015a00c51221003c0c10b0310440000180d449a44903000a4618400c4030140141035801190006d11140740707400640200d8466940d00080c48507900c03a04035200d0181d0030580d442c6140c02030902005109510280c49020700500b603007071409514a5283d665030184000152641c0c0724420407190207000f0803881e0300013000340b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 888023390 1250 888022140 888022241
    0x501020c150711060409150801200f0309010603021203030108010f111603030b181501111b011b111f05090603130b09030a030e0c010e0f0a0801 63
    0x11441d80521800000030303d10320103810654210b032a140c064078040c0c90745603070070041e580942010302e82d048524450001e441d802e025040e0789202e10012030354813141031009038501309800d4100150058000501c420400d40da98040080943e07150400341180c400640701559495050141003805d581d215007001406034240b0b4504060065214212001c000034618540b010108038035048024103031908129910646451801c1c8140041500e040d000f01c000140d411881b46015005441c82104558081080c0c2c111110282d0312808404404002400500d00b0600900c592052100c8815521009864900041000f40c030281080b0612044480c0d90340340b0442c4804c12001c006002d4841d80716028094140400031501f001400d05025083d16441403480c05686844102290780e0341050382c45172700083c00c001c5007861459000c074104800000603980c222000c0d0080b0240401d4890941c0c40301e17007110300b1800002e0110020310812000317803001551329454600020018509400341400540c1d10100390 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 888024640 1250 888023390 888023419
    0x4060f1805010519030f24121a09150a0507080934180504030810143d0215090a02040e1501080303240907360501020c 52
    0x14041c0e4000c644042c4502090084e815412000b0b00b6844202103207160500740d101e02d00c0c484080d5060381c00007a4003840e03040e0503601c0c0c007040b03288889079402030807207080b0002d1040ba5036034210b0403560190211044506072180c20030903040c5140c00302c1380c40700d000c0d990300d051240e0280d005400e2900301120b88000c00a0104003c00c0a9110803081180b89a000001c000e003281054070f000c5080003409010020a4506413410307400e00501f400700d404600180800c0d0000d0028600a2951410b44048041418004081c3c0b0148611915400076800c82c1307404116198205004a06002428180c006454a001040214013901c1e100c85c4900c61038522824804002d00800e00042030803083e501118003250002c85800b250341885a500324051761110b021001180f8000004000c3d402603072115071403203195425030001c031641d540e00b410746903010100c9400b01300e070350748207804c03c0c02017105101035002e6070a041500c9405c054044800d42c40c2039440e40340100b007590b805020346021204246c40009114200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 888025890 1250 888024640 888024647
    0xd0b090613020c0a0c0b0403060b06030103050705150c1e060702010c020c0409020a0503030307080f010b0304120e0f03011518020309211207030911060a0c0803150604060f180501 78
    0x1501202031801d50301040f04090508104040c002858129419125894032001340440903442800f00341da2490600703c0b8040c032070030702c1421203048903008070181c01e0080c1000208031000761411101450042d040c0605030191200740001512884070225000103d01090a4139041c008000c00c1c11055915003082400c500c0c3e000714614008034400c8400142d405444c1c4001000c000c0207421507601444003004004c4070503005000309020300e103103c1c0300c000e650380d0f01d180c40b043c60700c0110b034001c10100441c40d40b001c3d0107008001c0d107101850003d04d195069040c00d40440d0841d00d032940300c1c002074614600104517824280e4440c41c031142501805600d140b40049601713075202610400518100650142303150700c9400c0000340c800c103841004190810b0f0400c80030040c0904501074040d101c00901c1c0341e40000c5071410702d0407106003202d02d44503c00c0d60013054807000e01e5600002e107220503078800f04407400d42598441000b0009030a4903110078490600c1076400500c1700b05121290b13403101d1502903040c88942c1c1c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 888027140 1250 888025890 888025909
    0x41e200d0b0307030b010f170d0903080a090803030903070b0c030702070303050c010905070e180d1b0f020312070c12080403020d06240501030b01031a09070c14030d0b0906 75
    0xd29501107901c0e07400c5030200340341a1599002a0080100e00000b040354407540400404035120b61403e10b82c0082d8541c42252502845505000807801e500300800000e1003080141203d0202400c00b240f90170f60f121015429984125a02107a070742000600c1d40401c401c4800380da03000404101301e542541781c6024003950b21141d50002406101001c070300028098025080f062125a122003a40c0741a60707580b240b49031104d02a12903916a0004466111501c0400540864105115170320381204100d00c1e90032003103440d00d0090603100030010410300b8000d618200801541c80b04900101c80e91006542030071141c86400e9000f40c5000c5003c0c0740484045040501a6400c0c0c031740499004c1d41002c802c0c5031810042a5680e0040003200107810000c079414010b110403003c50341c1c2078806000f0b40a40c9001181141d900503400c0c1034070782c101c4003902c24500b0404440e6a012025090109150041e9114a2000710301100d1001c1c0c41e03440018141c00d902d03c60b000c0c4030b081da4400c0c5c880c0205400d04d800011a00354 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 888028390 1250 888027140 888027157
    0x120f1f021c0b060d1a010e032d010f09050303010303201b1206100801060b04050108011a210604060501050406080a0911220e2e0b041e20 60
    0x6071581c1070b003451070f6210001c035a04001412410010041c0f1074040501c03090364016051301042031608501000d00340800d40c00301d10512803985180ba50003041c81401d0703c056004a103003282d13581e4500c654000840348140207049000307100850b01c0307614600d0020f0001c40715004080c8011404003561600150010b400c09040308030304007400a40c107418000c200c40c1c41080900030118400c2d10103101071145842220030944090600900030035455022023001c0d4440c9224085c001007a20004019000e0514081c26114206640f5186441d42500726101c003500402082c41e46040103406110301403a1030701c2180c1c0200000e00300345060615109018084810041903210f0721034070b5020711420400700e0344046244441c0107205c9030b2006180b4005c0c0b900f020b090b022180155184c000146620180010030035595203141200c05850340254441e4040400801880c0c51019181d440079000e90707035039026030841e424002038164400000c690345102902c001c00e0421401404100d00100803803030240032240a507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 888029640 1250 888028390 888028447
    0x120302071208070c03030e040b04051b07050109080418060602060f22080c0114010e040b070c030e040c0507020913080d090c08031305091f03030e120f1f02 68
    0x54082c2012603452290503002003900c4600c08000c000c16030415080d0405034000d0701c040115405c984103120444900f0b40740d01c0c80c0d52a0502a000d440701c071450007032000f00c1c0705d8000418900e455650309801c542040d0850180d0210801c0c020060f402c0510a03000100700d0ba200070480c40c01d14501c21500048060607268008469501001000140704034114029904c012415500d504180e4050300a00c1e00700c1200c142960000000111881d0344620540116003180d03800516481d40d000660301c1d2a5041c50490a02810030760140159940e8802c0f4120782400b070701d996944017a244104052840000d000c00240c400c0c3e00041000300741319605462a64001d104005008915410a6100d0b0611a400128a40b0000800c2600003d000440707604543c1d09031800d14060b02c07001c0e083da00310850440c80c107800038051071082000c64422405840c020a01610341106804e00400f22420114421100d5140d41d00503e88010500e4483e05103420341c0e071600c03000b10b041c01030075049005000702090000c07509 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 888030890 1250 888029640 888029669
    0x30c0a08250e0f0301021309050601092103080f0709050609030304030b2e0b0901080406060b0d0c1112040b0c0c090f040201030b0d02011b0c080706050301050a12030207 74
    0x26100210080150304110444200c0484610700300200000241c0070454001c03800c0790400700c800d080500076a40d0411110384504495420202c41800802d0001e150904000007540d00168040c1c134140c2c8030143ca80360711b0366043d0150450a014021a20140c1803407925040301041040e401d80c8441600281c2c0c80031111165604403071030005c1e1842c011a04040d020560342024007000c3c0c4007080005e00e414030104802c443c24107165002c00b981c4c1c3c4282c8105001010700f002040c109611079803045038058400c8600040340c0d6219a6081c8441d00001001c0002558810b100804035070818000340344040c0c00b500a0041040795414280710b07001c1c2c5d104d19960303c54042071b20100340c0002d02c0142d507081d10140a602e0301707103001c40810301f0008003900d0036070104e032401c51050701508012400c05031850701038403009504101c0b01d180700000a1494001d84109103100c070045031130581840307d0b1004200c03a40d6a56225410001081a03c003542d80c0040900c035401c00700440000c0d00030400c0802c070307900010305060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 888032140 1250 888030890 888030901
    0xd060e0d0f0c1122090c09050f07140409050a09020108091204032907180501020c0a030803070c080315010314010521030702060a030f050a050103050c0d030c300203030c0a08 76
    0x10010a02001c418250200300a005a0706440f0380c80070010a000e4180b1b003048a99441c2d1401c01c80303106440000e6a07804c1940000c4210f4058180320181588134801c2030301c0c0c180c0e10003102c802c88600b600c140000541f2544490150b6901000350b581002c1200040c3c001d00320310240540c080e12480c03000415102c20815403100d40600e803034615414282d1a5484401450050300080070304203201c04900c9804039004001ca0703903500c000b580c00320360030000d4a400c0c4114115103c0c001540c00050801003046044840040003601c082c019500804600e4108000814140009810340c0c082910802c400d4024000400c12303944c4410403040340101c400f181c3d081d10540b0300c4000303043d0301c1080700c0a0341154000074400c0d2811f5040d131080107441d050141c20021522180700390815124280b00c0035082d9030040c1d440c0c8101c0d00d401c0c0209052107109003002d2851315002c1d40e800460541c1c180d0895880d0400c60f145948461039a00008203810040c07000d94a14601031184980c9030103044244010000e01000190 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 888033390 1250 888032140 888032149
    0x1401120807050105100302030d02030405010207091107051203100e06300a150b030a0f060f0b150c0706050a1205040312090b09010c030b030c100302090d060e0d0f0c11 73
    0xe072140c0c1c1220081c821440d00306907a0381444198803081380280b04135481100820b01c0031091b5011b884050340940f440ca0714242801014000d803034810b00300d05000700101e10008a0400c11050703150202c01d41d0b1034580c039250040101d0211150302040502c010380381001019500c045440310074641d003914004c81c0b4500c0004401146400f40c0c0b20108501c1412810f80603c0303864424108111110741050043c49607801c01d240c3c544024078001403041c1201280c4030001030994000c0700151170030b000001101c5090780c0016480c1035181c0c801080c01400066451b50003082408190081d00c440d0074850f00d800e9114400401a00e140d4107840c003159a180c02040816215081d2450192056807050001901ca4108540c082805450301e02e0158038100e640b0090034081c0c02409440d240050141480140901c2840051015111080b040580c20444000742e03617100109040014010140041c003940701da6401883c003616131080b40180014011641c507031560000c00c44a049074040015450304038100c0208 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 888034640 1250 888033390 888033397
    0x1205071a0c0702031902190501050304020405190c120e0a0c14031c05130e06060a03150b120109051005060f0a020f032b051005090405160e07030e0114011208 69
    0x35450b00130000710040305c08001c14403921090080310703e100c0d030540c904094280c41c00c103842058007290b0b082c00010007601e03203039100c0c5030300903000448140640d4411984104594a5a03000001f041e00c00030000e4402c071092050b2000041540000c008200307190b00c0b20411101584120000441c680c0c0d443c15254506008041240c10442542d0329400543d04001d805901b281170802c040c408004070004d007014038a00507074001c090140000c0e1034500c1c22041100503240340c1d10201002d444034000095840c1542c8010b0880384a003000003055035043c034814a043d2000540205000f10f1038880910455443d141181c0b0f40b50100c600321035880031096010ba0a01014800e04480e6000102e1503c0031011015040100d089030400c400300110460f016007021200150348070700300740c00000400c1c09141009000290001d00440440c1e014032102e150410100b913040d000319050f03204120510000c0d9425014021210b500d5000a01125092240c3c100050105216030007441b0610362221040c0450082213 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 888035890 1250 888034640 888034643
    0x1e051309060203010609030254041a0f070e1314010f1508040c062607030f0b030a11040b1516050f0313050d0309091401031205071a0c07 60
    0x30b64882da5600c1001d0f01c02c02d45840164015081d0f9440b02d60034105a012004103603030740303051208404007814541c1c0521000401c006030440e002c030415100715401c0050740303032040780704940c4070391000f000342803800c0000805003080c2c50407080401401421508840c030021b58100590b00001802403000410000c0e0808026021850700b03820004980103100c1ea062a0030fa99401c18840080713822802c00311103084040758007900444010302d040c000c05105a440c80b01400c0a584c100400514840b030f07011002c6025580c0101280e80c85c450302c860038080e8002d4820008049002c0e122481ca20b03240e0070888021030f01c119103d50b940e10a040c290340d48403002000c00903c80840d20b07803100e009503001031120022003030954846c410611402c02c5003d000040304c81c0b5107030000c2d00301a01403a040902c1803100d04040d0440c03c3c0310010401041150031413207024203144d605003140e00207501d103040011940f0950081c0e01c040050401c0703004003143d80303801007619051260794140455500ca844000d003a0080100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 888037140 1250 888035890 888035903
    0x90824041e110103150e01050607081c06210510200a050913050105031903140304060b010f0914060904020904060e07030b06250c0305010e161e051309 66
    0x1015051000201c0b04068402081c0c90801000c00c2181800000804501c50700c0e600b40e841c0801071100b4200030016101051240018a04198070f0a070004000c003040304010b9030083c2da6802c104022520825a1021180109134203c0021456100c15072504191901000000d40702c60524040440c0040203243c001d20032602a616003040c4507000b0b249520140b0342c14419032010541111601031403090f14100d903030050040111400900c1228611406d5520581c10f2200740780715a14901e10010007188610b208400000f000d4110f0b10001d050720b020b800d490380c1004000b0a0a00c40440b210344081d040c40411a40300b03403503c03003c80c00600a80300b00c9200030381003410030500060803a01b650f005401040152428000032151400f0701c2614014500c1e000c0754414072a08078440c94101030030640310300340035554401c81291640c480500b510902003c010003640701100c0211084065130802c1c02a21121860784005c80d40e01c0b0459144c3c1042e405224480c0c80040c1a61030010980d074020002d242d840103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 888038390 1250 888037140 888037193
    0x8060d080d0905070b18151324020c0306180709020d1b0e06030406050c0c0105010605090310060807030b06131109100503040203061b1c05060109082404 67
    0x4844000b070102c1880466044c070075040301088032403050041c2e560400307603104001e0000d203c1c01c0410072500d074690703202c241c81841002100d00d0402c1d0518004060a560650041001d0040440e040341c0350046084100315040250448030790b640110b175060300075104000000c2560112111103041010380c2d48050103a610005224031195159005103407201c1c45095401c401c0e250b10300d82551040c42440c14950300100400c000b07000100c5644c0f00b282c114000307002460030000348820031800c48e0342c2030b04004d012075404622038949107010461000c00344c039262130500403107141070803980e9200c01ba03000c000d0588502d080050003d0703c54880101c85d0b111600014406100060a101610343c00900321902980310403859400881c06841104d014542c06801400c00e07598a01442681d206a00c840341a9400708000016640c1c0c6881e40701410980400c00c0003a082c01c010b4005050840c05500c40c18440e00842d035207070280e045103403110903554229101c4c01c2d082c0c0e44920f00003c4801180c041d4441605036034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 888039640 1250 888038390 888038407
    0x10170f0609060a0506010203160305030c070f060902040501090b060f030402030a02031b03060f0f07030903030204150302251e0c05041406040c020c0d03111c0c1506051008060d08 78
    0x7482d039002e06840c1c181000552200001241c5074410b1044130159504003041103000648100000c0d507001c8e1404200c1c41c1000429914200c07919100d441c2030310215100c818803815850148212801480e1941c42081154180008201c5600581803818640c80e4044005415510300340310300200e040c0d0041c280c900e17080381d06001240109410803218060311a900020b889051184403641c06460310541c00217036603030f954008501809180000700c0c10140c007480001419110200200f07101d8110b500d000d40c0b1120404401d05601300311141c40b4619880c1c0c1d5910744040f5032241c0c1400d900f0b104601032030300d402529080002d91030301194002a0081d19092603401c00703003007006289008010444040c041c4022800f02240ea0740d0311941d6060703100380c60021250010b07000310b14078000c905c0118192003c8500c0f0004002075032402c00c2c20741010550b12281c0c1c40410080040d10710520030350690800c19581040041148050007107600410320a00340041401d0b80e0340c8100c0c01c4107580d400302020341e0711008da = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 888040890 1250 888039640 888039643
    0xf03040506240d0f0c03021e011101060e040b0c130e010611010902150c071a0703020d05070f020f040906050a0209010e0a0302151b010e0715030510170f0609 69
    0x1160800c00c0e101c1c500c1c011008194a00c42d420104140082824a0300080d0b40c8804441c01c40c0303c01d044412407049140000180c9a0340140008c0d8041e41c102e0101c2840c80c40000742090140d0000890241d240c90414004080d13603c0e04240c010380c002d003e961040da100b120f09115442014001002c0c3d0410800c00284081500021030680b8191342c0c511450b4005001e40324240c03111164020740c0300c3e102820096100b0344030005000851281012549000c0ea01c0807400c900b001c040c1500d203407840b000030318042455010010680600c6440c608a840c04105480d086034490803001c000b40f01c1c0e10000085a90342d80c07650003e56910741c000303800300001e0500c40f00c014000d41c02038042c2404200c20b0704802c025880c01d040007804407600901020320703040f00301009800a522610900480d80003804070040079842c2403150200610016001340740540c1001c4003e00c0040045003200201400c00007044070301d5002c426000300f01c403540408200800d0341c0107030003424501d6500c803403005445107800700f200030301c1c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 888042140 1250 888040890 888040903
    0xd060603050c010323060f0d1505010f06090e1f03240506040204060210021315090e010b04240908030a050310060e010f050304111c050601050406180b04020f030405 72
    0x70240c07403c20441710b0b00d004402c00d08042036691702c40c0c2e12070440080c04a0610303001215428000920071000740c01d0070341c4c60040c034084011202190580c1c5800600101c980241201d002c3c0016080ca0321a4901e0f144080c000c43e0001000c2c03003c4410050b0f01d40d000c010f1400350b11b002031580403000f0b11030220068071116112029402c84d10341c25051001050240c2001d1086409584240d400b0380000c13400b0160002c0a540032100c0d0104502c0c0b90900092a005042160180300d001c070b03512200400d00d041c0c1c02c3d11344108180c02000c0000c40030403040000c001054a0305999000903410340f0008900310320142c0302d0181036803040c00d8130302000405030320695204004503c51118904040b0a603a00c500c4102c03041200c1d49805d81c046074110f6003103441240190003031507015104103221580e600c04100420110034003000354542d0204030100d0300b0200f20f0305102842c05000245d44c10800c107803900030300e6a40c142050807014900f40d0380b08181d524540300c5404035070000b00300d060011360b80d0070030345069071343c0380c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 888043390 1250 888042140 888042163
    0x18070c1721010506040f3f14011a010e0a0e07030606110d020703080c0102040503030d050a14190f02131401120b0d0b090f06160314060901090b0d06060305 68
    0x70007240c008200c602d0154155025540e41c0510070f03030b507282030500c1e0030640c0351200079076054041e0890054400c0c18118268040c030038400c55054000d850070f844c00780c44031801c1c440030700002d9040200c0ca0280d40040c0c690680f09150919103130065461510205280003a0b9410080c0d0561400c820054003507010b1b006241100c04942d00c10040c4031203401c0c0c2c5612083c008060100680010f8002c101007021240034110b6140d02d84001843e0607500c0380081d18540c490100039510640ba941001440c031013130302c01d001311105280c1c541e50b8686000000440311034440441802800e503501c0d074200d5082000d9040c0c2d94203941c2d248054a00303d44234986035116030b5140e00d015000400e0440010400400c60144e598200009003041da0300f0700d16aa140d600a00000300701480030303c2043c0a100307c0c0a0200084c2e405035000102c00c1d0003002510000405450661440301400840b1800307008854441101c40e50440e80d40100c00516210403030000384a00026000c0581a242880000700c20300070701040700305105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 888044640 1250 888043390 888043447
    0x906010509030d263601020304120801090209090c0a0c060e030d05071d1e03010216020a060c0809060309011409031207091809020621010e010518070c17 67
    0x405a0240b00b419840c02200d260340c603040820300050380401d0788000c0342001907400d0382c0103645c500fa0381542070880c4c01c01c8030306441100800c081800d607281c005140c5c034094003821b1400d520b880005000f01718402c00140516030130751400a1a603102620a242c0c400502c0e50100301803108815a6100302d540390060001c110701e070352601000c181d42a016280007221600141d0468035001c440382c08100d502ea2a803080014004200c0c50107400c699000c0c40141520002060300d10407008060050140088903038002c44180b1400c0100c0780045502001611103078030b41154040e549030340b0180000e01400e4000d55402003808908240310700ca06000c070250850100407078410b40c0683c0c8440086801c01000d00c103c4220201c003400b080390701c140541000e0740c140d00150031036203080712401207142c0b5251880c81004540303981c0e40c01030008944207104103004180c101c452603425940c042d01a8042c20014050384144541d102040040011610010010004030b451464880c0d600b10040341c0c041e10b000340d003403101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 888045890 1250 888044640 888044687
    0x10906090b0610020715051908092a060304050f011b080a0501030c050105070c05031b011b0206030f04110d0303060e1305070b0901031b2105090c0906010509030d 71
    0x301d0919004011400c0d03c543c1c000c00c51945060315600c210800014640104081081000342003c20b80d003003203483c0401941ca44541e4600480391a00b40404c0c140310749e41414180d6200c003103c10602c80b15110b00c0404442d200e94a03201d6107041840c00300c8460102a0310b500340048024080184210706d00440e9298981c0d0305240c0e914503483c1e08641090200038803610504a050010754810340103007034094030821592030303007940740c20002e403800701c035584107141700700c0c907140c0480071075a00480f001d450305a801482580381d1020b500145280c007000380150002101540042d050000e0504004600540540050b4007919203050050140505001d40001002e01801117000d040740502c401d019203410002030701c3c0e0242071404801c4e144d406071114038101602c0d07410440c5a41c01ca24503002c4050000c0c0c0780d480801c8a014860620260b0b44410b1840c06031034030041010026020540c402444c4045481e600640e480800580b0039001c2c1c1400203030544509d500841c942600000e4500090781c0040a0740803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 888047140 1250 888045890 888045901
    0x91309020a0807060908012a02030706241a031b220302040c0806130506150c070e07110304060305310c0803131217030c03060f01092301090503010906090b 68
    0xe94200d4003055141d2006408100412030404007803031a166050710580345031a00c15160310040e1401e00221301c08030061010110141d54a4015033700081c840c614440700d41403440c0040124600009241e0042040181540c540119803442203c88010011040d0090380e5000c602d140c0c1d03119500d01049004500d001c862a4003e409041c940f0b10400000304108a203078156441c940103000090701070368001c69402c41030320102500c0d802030404412814010810303189044417000107080701038000014001c81190780c0d80c003181c0100c2286d0969146007000b168a4403441c400c0b41501980e24401680000820110035864020b1320020401d603001d602c507200c6041d22114507946900c200302d80700c255840140003c000d0306104455004405009840c0303218440310814180c0541d0340700321a010080600001081994501911001d2051030203291800340c56080c281d010170f4100080501c04008010019003040d9688211182005404007400030700513080d00e45803400250aa25004444a1310054000b0300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 888048390 1250 888047140 888047143
    0x40b030a0c1b020913080c010603060b0a120819090e010b0a02060a0c0c110307050603090f010513030c110d0816060f0207050607050f0c030304030801061112091309020a0807060908 79
    0x40d800380d0000e0103035556443c2c40304481745004808004488410040c03200081c0d00d0000c0c40380500440c00b0b5680800d2030340000b001c00940c00d9294000118544180c0740d20008145103005031412118400000355001d0b600c0042540c1c40c6036107901100038510748030004100088004054016807170140c00300c1c1c2c029200e4507640e80540e02c02031103150018000401c0340d0041002d00780e01c0740d45a1005016103100c1c945890100b0401c2c0e10489000c40b480d03001842010200400b4843c2540c855022009001d801c421981c2c000e096070002a0041c01ca5507010040c202e0b1503580315640600c4507449480309554524540300d04640c0210180141d41062400d03c00b0904003410740201c0d260154890007409140ea0303003640940e2580c0113102d02c01610310040c4074500d09000d0400007980158082d480302c0c92290b04d007510042581c03c2d2a07070005c2c1240c1100314901707608480401a18588a0202c03403410b024652401c028005143d04032000c4e50109800310300080c0300301c010441c0d109485d050b41c0c03090881a2540d843c107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 888049640 1250 888048390 888048437
    0x13050d02010c231606140f0402010804060b0102390306100611070308070f020f060a0c020f06270f01021c120b1e041b17060402040b030a0c 61
    0x100814091101c0c2d8129404030b00c282d10800c00c0f040342003402d00194480e440d0304a54070400071503149a6607070780c1c0d411454a0110f1554026415910f040491070a58002009200c3c0034100a00c03043e10744051000607802031290000440800c03c24800c920310a44501c0c103811090440103200028000d0480080c0c2400716181d031003100d400d032452441d80e00e03101c800c903050b1596400002940c000e6140200005810400a0400710300910840d80b40044074010000c1505500c034182c0e01c0303040100a000c00d140d40160603c0b000d140c040b47d5807084c112180020508034031034032403401c0c8945203020400104100000c61404070860649402040d501c00d6001665141016483c0c00c080c2d084c0313841402205446410b0700e4888008522012944005420124880000005c0c0060214002040c018251309151003206461000071008a0200c3c1004901910120100c1c4541414418002c005481515540c0480740184403140c20103642e450603400c01e40003002e5010760080040d07411070783c10f207003d1325000c0350 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 888050890 1250 888049640 888049661
    0x170d0305071b020d0812131203050106121a030114090111070b16020106170a05060c0906090d1b0323010c050301120203010624140a080f04030309060513050d0201 71
    0x4402c8841043c1c0801440b1039042030112410f44040013001500c40010003041c1c0607a00030341c42c41d80400341c14500010307d1340742e0369407110030146044010403845900c0b580c800e0034400304d440002480843c0d1404060007000c0d5880aa82543c00c0039103a4181500c40b440c0c10b440340703c004000f00b0030301ca01140c04102a210b10342000d00901c3c40304c00411500308504203c01c6d5124128000080c24940c2c2d000c07104c0c910100c030009150290031080825007400401e100751035102d0a907210a61410b4504000039559004032405103004503110340e2000200301036415008400c003002505450303520750b28508000c01c5904002503842c0c040c2c07042d030054100a4140103100600800d07840d9a42180c7c01d2a8101205c4168140180da241d07489020005004d09569417544040107161070741104c030004881c0140c4980501801c1c0c00c0c00c60703030801ca014044d45d88284020303008941c42400385040e450f1170034224050200840c4c09403125240c03405110150003400d2414136554480c074140d58242c07501040036402c0f00e610142 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 888052140 1250 888050890 888050927
    0x91a0f0609100503090a050a030305090f06010b041806090f0603021e01020604021c060c023f2d0901030509030c0c06090103060e0108010209040e061e10170d030507 72
    0xd04582c41400781d006144c3c0400400216402a40306032100d915002010005802184d501c3c400d00080d07820910203e208982c0020040c80194984040c02803240314920075540da031b00b46100b120200d1240303900038100800080d43d0600c901e408210b905401442d507444124444d0f001c440303024141050301c240308503000304160040c00040c1c1e42c1d5003e0003582e1041c1c2c040c8002c0180c0051341040000d9580c032500c100741c036007640104001c5420000340c240e0340d504c00c1044084000b01c0114844070303410010250314035045030900540c4901d5441110513240c074451031304851a010003ca0703140d182d00c414002e0940010300760ba060106807034141d20962a885054955002d5422080302d0307076200c3c2481e5000380921081890000342e065600d42d105110034401380c00c0910141d4000038689198074242c058540701300c0201029282d03e06004000303d006881414503680303c100641c001482d0b0340c10420040e001404412580344250a001206645855140e400c1c080403a24090100340411321031910014030008840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 888053390 1250 888052140 888052159
    0xd0b060603040204061d010302010206072c030304050a03050102090f0a03020906100516060504051c051206040204050604120605010807080a02041a04111c021806070507091a0f0609 79
    0x505001155100402c01c2e608183c46850024402a0300c9045c00c0007001103900d02c69041d411440028208400644103500304440fa407081c03800700e84822a0000d40080855003084520a200082401c40c0519488254004410b03503002050220640050021803021510150005400c0c1d003003090810071800065001060800050b0f0203040001440d8110441c41c10b1017821f0a61000f00901d00750304e1241c04850b8a500e0728140410028208084146420600c0b2089a001ca0300700000b040c90080014041c2203500350b601080140d11182c0c11600508070203004030381d0302e680381d007101141c0c1354002100300c480c0340c41e0000006a00502142c1c040582d08180c0150080545c56001c000240000240406071056580c68010f0240c1d0396200d022000d01e0b200c2440c540b0741180c07941101443c41442000b070317070050040142440007805140b82c002c50000071038907107031180d4031030a10500d0a225908180f003564a0308281040001002903000070100301198a00400d40c00070050041c980507071072090781c01601a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 888054640 1250 888053390 888053401
    0x2031b070b040e0a0b09102102011707090b0d02310605071106030f01180204061707030906050903250209010b1c050c1207030e1c030204320d0b 63
    0x440c943d40d00304900801c04258001205c00103400e842d0240c40051003203200400810001101980316914850f400d8045040d146031600041d00c0a0502a401d640c01e901240000b1101801058150003820149034075039160204851b00701c0080d400b8000d8102c0c41050b1507180c500034001c2d01402030369405001810a452031030040292070a070000307841101d02000c4046804410740b0303002e0146220b003001440d42005075160900d46490680c0c0d0001c030781240d071300410050011a41101e9120600c0032220280180b95443d0b00301100104248040117011900b0903042c03000705000040a008444a091410f118104946002658080c42260700a4200c2c1181d00100865001040505440c0c0c00c4a8000f64100c0011450481110300840389182c50600101e401c56480d03246103005540036080d4181001060088800f59a030340041ea40030416211140300d01000c414460340644005240c9980b45100200354500100c210303c4540e030fa43c1c40d460052100301a25072074034000100c605a000300c920700480c0c891 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 888055890 1250 888054640 888054659
    0x5061f0c06021c180204060b040e041e0501020d090309150e06030c0c030708041d0c16020f0a180c2307050109120302180301061a030a060b030702031b070b04 69
    0x1510700ca048110302200c0d00015028580241401c413280e0300c0d00c888840c4424070420080f50a603412030f01600d84140401e000d00b1030040c03820360f0000d8019010180c2d00d15406040c030b001440d03244005060394004220840f04461581103c40d44c02d00c0f80c0c0315850000c6c2c0b614003c0680703800c9280c00300c000601d07440421540e4100400150340100381c0d80b125038a0007007105c01e11442c0d6441201c044803015000a02002245400ca419514441008221841504000c003400c0114004e07200c00000c06141500c80b80d045682d0501306100294029284201030f55454400d05030750b4402e18000c60202c1c0c140314203c88443c0c807815141c02c0031240c5112070f103089801c3c0103015034a6004120700b1507803590384070324917404942e0040d0f03000d4020002e85d902594911018044803001c200d0600800c4c0030368100030082c0088c035854181c68124503204401140c8a95420f00d2103000f070203459100111040780082840b40b9140c0c080000d00201c0d0000a89031804000c0c2e010b425039649a62040c01c0c02c40c81b0902052002c0b481 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 888057140 1250 888055890 888055897
    0x403030309170c0f190809040b0a180b041a0109061404260f0601080607120f0f0e1b06030705030403120608030a03060501090e0c0c070905040605061f0c0602 69
    0x241508109480381401500015800040c0d120b4003580304144c0c4200e840c408000f1a001c0400c0c0c08001704079040c0699503a4054024020720500c1030782c40d152640120f884441040d00140003080f40d50604a00c0c08100100910303841100e01c2c01030741020715030020103076041010103401806a407110b802134907066046a400d014101d111454460030000055041482d040d0380032650f500200381c4c0d40300011599642e140c01d00003204c141c81a0000801048444400318019a01c01c42600309810701d0354440051000070003144145001403480e0020100445103181c0c880b0400751840c1d0111a029808400010b5407a4100e0004075031210040002404403403147c40616089032090600c80a4000c450b49400b094440c00e401850150348007185440c0c0a5615005910040000382000705505040070004188284000d2004036000c500041490800b43c00f048040e004182c00041000309081c245450700c060300003555014424400140c4c3c00001c001c10390442d085507007407038840c40301c44030311540c4e064003075003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 888058390 1250 888057140 888057143
    0x3030402040c11010c081e040309060f03021308030310080708030307030c0329091b07060e0a05070611010606141210170102040f060903020d030503130f06020d0b04110403030309 78
    0x103070f0910302914980309020324040d00c802901c9142040c501000d0341986410761290340c0a480070594140000f10b03811800400c19144c191900006c0c120226000f43c01074442d02d03240d07188007010f0407400580b290300440a140100e0b00d52201e90459139540c08185d607550064003910899410030004541d440740668401c001c2c0302221700300072070a10311030007840f0100c806641482030780c5d14400002d0b8286241400d04281d002c181c60117441c200301a45110a00d55001e103100c000d200958070007034403143c00020441a87d80c0d0b41e0040c1140c20090700c0d0307400180002c5580c0030101c00366080c620081400c0740240305100321105001500b5081141c0213004555194015015000d08440c002c8041200c0200108010b100c074120000503aa691030144281c1c040442c0754000700c01c01051240520040e9920f00c2e030040e259070981380c0300741c880d04c9150341502c88009031000208040c0981c0020f80801071903402400d018801e80100b08050000300c0140000c0c1da081d0301070410b00e00c1e0104018000a400303a80107a1144c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 888059640 1250 888058390 888058397
    0x60e0c040b12060f040f0f0c110a021201021201080706030b0301020f09040506150c0d020f06130206030a060906090b03160f0522050711210414120d08160503010803030402040c 77
    0x1040800104089404070640341c0d64081d01c0d1042d00d582044d460107100c5544a48d40b400102882402014a844040d000002031081d071105100c0d418000003501510b48080c218012102e46594403400326988102912070080800d04000d60890b0070b140c1031003902e20b030140c148081c92600100004100083c0301c0100f00381d500000803e6041c0c0d104180d90040c107840740f828002858507160b10385000e40750441c90b4501882c10741c00882007051b030710740364000c8591203541640c2ca240c69403183c840700006045183c0000384401d14103140007440d1041608040d00f0b08000ba82a5142e141c1c0c01041d40850040070b004001401007a01d4040109060200e120b0300c502080e0b2008010b8800056000d5003a80d030207960b0480090501002108220303018456003140154060103080a02051140311a8600072841140d0304010074190358417142d124201924903500f5a48240c61242c0010359018148410645111402d10100c00d01040c0032802801200e050310f18800085055940360b500704405002015541001c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 888060890 1250 888059640 888059659
    0x105040b03150a06091109060412020d0b130c082b0905030109060204090e0307050c191805040b010b0405010c110f09090601031707032007051003060e0c040b1206 71
    0x3000c001042c072500501c04814041115454010700b00161202c03040710302e070455000c11204805035200c038111400c51306800307011440450315000041d10f9410001025020481c0c8004015008000a2441c05041d2041c20f02140c000d480e152035130ba56032560280d140c0c000882d4520300d00d02050001051507030a510b40342c040342e03043d141c1c0086400c0d2800c4800c1144d60030307001f080502c034103da00d000740401214550001c50402c4d0954a8460780c0c0c00718140700e2801a92810382c507405140d280320000025010b100c404000d59880043e10380001c20702154203031b8411182000210381181c00b0421202140d605a40ea03204103001526a03a03002c42c004500380c0e80c8a60380709030000c40c9484401d151032141d12448040c103225891400c0c464028600382500501044041000d180002c1d0046012401103e0b82c61401d05d1070012120300a2400703080c0e03006a035000c40b90048240000703a240d0001d1080e9010107418071550f0711440346550030360040e4080c2d40480d00040c4824058034242e02e03c015800500207182102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 888062140 1250 888060890 888060913
    0x21c020a02131d1b01050c030f0d090209070c030905040b0f220504030f03050915040f02030a050322050f0a061809020412050c150a1407120f02060f09060105040b03 72
    0x4444102c111120356000313401c1c1ea52111091044030400400203091180c40c0403441001d0903200d04c03035402d0001c001c44002c107401e152000c550340400c040c19400b50240140d410441405421421161012000200040c001141c20f08013401600f410090241030401c20414180802c0404004074444581080d0000c014804024aa018860180d4001e440f00f40c2d42c900d03194002415544000c1024465500c04800c5410007000e400d955580180c0190f00100e00b0715441c800a402c240c90108050306030b10000c00d100911604422081c4000302180e1305a40c2526074a5091126000800c0310a580c0301c1403000d81081528003854480681c20140e1301c1d01c00590351a085520102d802c00c1c0c01c0b10a24808a46001003041402c010700140018122140c07915246101034840c0c0b244594480081041441c4203d800c0e20001001601d03141c0740e0083ea0750400c0064010300800e0541d00c0400c20300107200360130100b02c440704202c00c45030054005401a14290382044103020107091100500e81d0544940e494880 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 888063390 1250 888062140 888062171
    0x2d0307031817030601081b0703050c240a0b0a0b0304060b180c040f060203190e2b0209010e0405070501180302040207031d04020f07061112040503030106021c020a0213 73
    0x508040c0400701c2c1903d13030038940c00041180800400d05170040004800d90040501e50030f050b9112290705241440d6200c00c03480e81c00b4100300c2c400ca540e54160307031455889049818a0b185081c0308601d40201041010818400c121003507c551140004081c002c2022902240c0309801c45001e241025003102594100c0e885070498042003121350004ca45800700e01800b9803504100d0140c0140142d200540c28000703080401c1c0c100a200c800c0d104184074a03146501a95140d840042c084685042031841c07081c925485802c4065000300c400308d110780002e40010405540c40060f01d03000d01c1d000001004103e00780f10055500c6105a00c01c6482d000e080d06000006a40e42c1c00203043c1ea40c401d645680092030070b850751015000c44080e00714451801808009050400c1e1429202000d80040c00480c80701c05140c1c5800e80c502c1030290f40032a00800408000c148000000114129262030382165000d01c0e0010042d07455152280808006030003640c1c80c1400352501110714517150003d014000703000b119050260 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 888064640 1250 888063390 888063413
    0x9080418050406051e0f070e04020403060b1005040e01090b0d0b0a090506090d050d050c09060f030f010e0412050315060a02010603140a230f010609022d03070318 71
    0x40391541d08000400915018940c1c100070342005950700140744c01c40c52090342d00300425229065441200150341c0a1050344902c00854001c2d01c00c650382c0340c490401001401054003550700500c0c442215410340c511170780440341124140d41d001051a4281941b1401402540c40102c0d4811003010244000c01c8010b05101c2c002c1c0c05c1800001404015454454100100100040c13002d40002d030444074615040401c0740c428050140f00010a6540d800c2c0840d894011948101d8100e0404201c0350340d4005030710010360054100740d0000da070aa90b41c00c20340f006480102c800078440700554a0448071240510047c5420040340c2c03621076092041071011824a81055141d02d0050391142c00810034083d580c5142c08040501c5009824501519112050343d5190002c0d07402d424920807400301e00d0745100f480400b03840d445801c0280102030703032040200007030340090a98a8030003940131034400d641c2508041c08004000761850302400c60b91348040a030000c1440900e0610705d85002174407580060f0560308031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 888065890 1250 888064640 888064679
    0x30f060d2a0e100605030c0c0a0b09031210060e040902130f020a09090e150403021014010f0503010b010f05090d0b0f180f0a0809060415091a120a090804 67
    0x180710300a1610002c0c102800c80605030a9440c03854810900c18580d201044030345c03100040c2c0c03101c2d40e95044504032500d8405201c10243c402c0d50070106001c1c5110000c001031a20720740000d034045143e02d4282c1d0f074118213041445844040380488c1141001e41c00c158200d0440c8600050a00c18a10b46c1105810203076a01c42000c2590341d035001591081003508003603443c02904801d14200305074046240d407070b66240d062025049209002000117010144204940e104a10004a007030145a2210200c4400d00300f080c0112445021481c030701240751300f0144580322680405a4419154420325801a5550350048001c1d5801c000ca0f038181030046a00031002d40e008242c0c40700700c00074601d0700c01881d140216007a0b9581070381d50006d042c818000c1200050040301c0c1c0d90800c01c02c1c0c0d900c81058000070301c10700c101da01412106200f030080700e240035080791100040700e82200ca4030340704a2451011252501c1000c480280440d400c4000c00c2c499000f540c40108007a215103405881e25449182c400c0c034444204a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 888067140 1250 888065890 888065963
    0x5090a020d020a020c011209020105092b15060b032e0503070612110910030209031609050f1803040b22033f0f02070915050312030f060d 60
    0x5e40030b19568801c1140040d002002c030100310351445c81c3e000804a00c10030450724031075010a0040400c14016018056118000001e020301e18038281c6030482860031501c0808a00c01d02d4020001506603000d000c40748074031800100f405000200321030401388030b5000510012901040000800c2c20f40742040406c001d401641c41c3d01031070410050707546058a9040941d111040020701c030303078216a290f00c0207107022a6007900703005d41c44441240110780307040400e00704495000b880c1d080005001da00342e400580580711030000c0041c035a0b04e10302041c0340d03101c0a51812101e5402044200002202c200240600b8038107030702c1d1004600444100a8444078080d0010389491091070b545821080002240c0e80038042029080c02c100d54005000c82080c0c0244010351051040c014404141e0b94400d00844d80035020f1581c00f0410281d2040309560034151600440d4041e2048041c0071084640c0d500a880c840e010b098840f013595910107050103000301400c2400c842c450382c0d109601d0201c0c8418210100424a51203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 888068390 1250 888067140 888067153
    0x15090207060e0109020f0907121109040c020a0b130c05040504060219020c01020d0311270f06090f0f01110105132001020c0108100b1902060601090f05090a020d020a02 73
    0x70054100c40481a91425981c0350610a0006032030f003101031100d0080844540c101940d40900558408030364088034404a4035100403100840c0c5a030307001d415000815202000150504041a61741d00c90300d490140612402d280021007051401c0c4400704024419400309070b070b040e03450300070074241c64041d1340858001c0d0700800d0008408409540d00e1001082510007040c0c1001c031040040e40b00d090b0440c003101011707110401200e0f15441d276002c88502c00c00c04442c1c04040440c010301081c4c0c600d1501c6a079803203180b8802c1c480c41549170000a5844041d001810817200300b2101c000c00000c0f00d0b4840c0401d05101400200f55840c400170710500d44500030850550103a044a03180880c401030070b008041c0a40da280f071030a0007070790360b000608800842c000e0908040075240c0480c10300121041e60301c5034206000028098415421001c04001c04c40401c0d0201c1d038198841200645e80300140b80500003030b0040201c81080507182c500780c113541084071403070300518106104c2a12421307a84030103000e0015034802c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 888069640 1250 888068390 888068393
    0x120f060609061009030b0705040b0705060f1302180601020f062401140d0b24041703030714070602091002241b070c0b130e070e0d031215090207 63
    0x101503030380d1142d4211003400160503108805800442140001742a40f04003000080b05940200106d0f8040c081481c01c0c1510781125140c9599079900444908140000c100d000c0340103007a86481c83c500056004181e15214040104a05210900107080c1411442a42c07241c17a107250381032284a00030308030b145100c0680d0f00c0b01180f07a64080741c4664402d04218103100d200161884180c1a5416015146004501208070400141ca040e04a4904c500190032040c040a409440000100201c034a400d800c18202d01c00c201c10305881c0d0004845250215400d003503210300245002005000e01d51141d50018103041040c80444d00f03040c5802e0494000d0b0340314905200101800500d041c0030040504011440d80c03920140e800e10b81c19440b5171a2000070b501003550000c02c00c692640c0700103005604641a158100309002148000303252054200c10b94480000c900024803034a04c0d108000f00c050076201c1c17000712a503011202c0c0f54001c1454102d181c3c0c0e038000102c207042c098400d14001c05490398090703141c8515 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 888070890 1250 888069640 888069649
    0x60f03050607021c0c030827010b0f0d020d240f050406050906070e01181703210c0a05030402030a060c050c2803110f010203091c030c0903020f120f0606 67
    0x40707000300da420000307142c0804045d07011200c0b40b00e683c2d161400b410300351500c00154140c0d402d0808101e106034504039004500110543c4004041901210824500344d041c405000e01d403842d161740039410805000410700031544110812446117850030340e800c1d90986402040e0115144049094040d94658040c003043c41003a014081e08100c401c0080d0080b0f04000d030000c1c1c10480924100c2e03041c0703d0281d01003c00542044c41400042c0004c1e042c000300800710350b5015440703a010000308000000224070391801c0c11021010648210341540b25545018600401900c45800041c0300300e9040c4a06480d4500141090198028007000740e1a42600d81100138041410a02d082c601d500080414014000501400b0b00c085d0a0070758140c10400308181d44001600d08100e50f6a80c1c0d120950700000c00c0c408950f000082c01c5901030088015807002c1c1009020407010790352801251800070303190403801d1015140c40d62042d0011840100070420f844003150303a0301d092040384001c4201070b40050f0104012401c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 888072140 1250 888070890 888070903
    0x11040f0e060f0603060a170a021206010314030f040608060609030d0309060605040905060f0606190c0c06170a0f15170d14070303050405070302210d0f2001060f0305060702 75
    0x11100f8504624002c1c0128101d030405205006095182000f00601c800741440200c403659005800400e036004040380040d0388940c05e20044139103c10f48607c040d140ba402005681d04014039202040c9024a403080c2264250700c0a451164028410402403185903801c102d40c050312015030301d02145d40440c1d03040c202e013101c1c16584a14041d80c01d010800380001d40c0810116800403022228040c01c0d01c810002c941c0074050520504c501e204100350500c0f1070f03508020039408441c070411031074000341c0e00c8410489840d10440c2c04911007800800128107101c605402c85c0425a80c0d800001400c0310107140e0611031a4019440400e111031090200e0b01480000d120080c0410a00c1c02c0155000d41800e00c0e0350039034450030300040c0401d03643d0b2002c141009814000e0308001e58000300044249508010525040682000c41c018039108001a10b07003424029901c00c4000d00d2592100d0854508803400c42401c56800c0104c581d5039540c8281c085065151030f06100059406640108280c0c40c1900e4003a15020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 888073390 1250 888072140 888072169
    0x101517101202091005030619050601030903090e1b2b021204021926010b1503010909030908030703230711060a0302090433051311040f0e06 61
    0x2100c0e540600810900a0390322003441d50684184040341d40311040c6200002540c2c00950b0701d0b014640512103000c0e400d113030302c040c014550f01c01001603490320001034040383c05405004000c0b8108000030002403600441041d804100c1d41d4044068040208071070150368402c8100d500c00e26520a8801c429401c0d52079002c60746e0301c004a00714070f41140c415501c048000010030007440f6030000480031440124407640d41004140301c1d10507003034110000e260900c1d0070402241c460740c50743c6841c01428a514010505544014910135860303c1c3da402c21080c2c0c401f4041c4084142c0500900c0301c0d001800d503030104000c004d0a402a43c40d03982203140e513500400300e2180c3c58258800c0000500c001d4021500001c07010201200c116155991003d05c1b1310158040d00070700300016846480c00350b007821015031425003502400e1420405550346135034002590358140312802103903046420042c1d41c40c140480c0798481800021040344142c103240da20002401015090781000c00c1449003482446080d007010b82c41c89900c0c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 888074640 1250 888073390 888073411
    0x80f010908040504230a06030311150601030c030e0a050f0609070f2913080c0109230d12030e1612241103040506070e0105070605101517 60
    0x1411940381d001d054003650180c03510842c0c3d84ca01c201c0001040144011000d201c903040345442c1c0c504020004010601ca20065010901403c004504601d000c41c2c1601045540d049031141c0d40c5039580110014030501d45080c2c107150b81c0b10301c2100701c0001040360300c5890384500700801080001c200440c1c1000c1c40988500c81940c0099402e0080350381109003c029540140303981c0280d000e00d410b200e0b400d0003145e180901343d120700003154140d4840c10210041907900010031101c10102003001110703a03640d00c1c0700385d0405444480c0661800700c00022003403002074008000984050558650014101165070481c000c43c0d0f461101e1149442c0034803100d202d0008503a40542100d183c00e08440810001c00c0e00208801201c8500c0040b40e86402100d10300034480c030504015520b44d1504011159100382c5c0c0994040c030550307001401a51050702003955425040c0d49250400300140d5500e4041c010281641c16900d000f498007141c003080028171040c080700b5644e82d81c8852080d84402e0340b00000c006d08441c074407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 888075890 1250 888074640 888074651
    0x1a1915030b03060f060a1a1801050c0a060908190518100807111c17010b04030816080408011803201c020c0607050601080613050a020f1c0c080f01 64
    0x11a90b0204100e41e00511121856203681e84010000e14142c1d081d0300b10f501e0250701078004022024101c000b03051102c2448402c2100b070b9064900650790780c00703007090024040d8045180e100009105400c0752800d2481400e242d424003041502c1c01e010807030b1140031900065008130b121310380fa104500d001d000050059928103800c2440c00700003040c4240040280c07003480103100562108907020041141800042e00041c1080c4c907020720010076010255107a404120740010003c9040c800b6002202c044070707803008225162801c01401c1e180b1150b0b0b254415039440323200b0700c40003540082c2030042c0b4851403e2500e040d5080d40032071030301500b101301c4001911690b1981c0300300c2200c0c0c881d00160440100c11400c501c504c80785040d401c2246007922010ba260303082070010030314400b007290005005040e224800e003074030301d5907403000003040050300c2840025055038442e04401d00541410b4010191810300504801c3c0c81100000f1072502803030080c0411907080b19800802c00900710705010440c0c61241c424000e001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 888077140 1250 888075890 888075911
    0x902070206030403030b03030c0604050f0f011503030c03051c0b18190b040e070b130602060702120a14120906010519140a0f060e040b040b010807031a191503 69
    0x1c8901000f00000d0034140e032580c0107a010b54040096031481b0708010100d031f00916142c0780142d1940722000da00f0580740704518000441c0c0c4030600a00900148a4041c006082d15540301124285c2030084180c05010017080b00e0300c913000c1c00700d134982203691b070358080801d08000c4201805074400450320340414500001c000e2050505c0d00184d175400c0300c04080004980c00b04c075400054004d01c40c0a502100074450b01d4000200c401015000e4192655050314500a160382d40b041640c607103600f241c206005805c6620115100704008000d02842c0c0003c4c42c045003002d129030a407124991010b18221000a1100c003005283c1c0000c110309805094103462011030f02c0e02d0510110b00c01c88050007103c21034081202c115010b038884000d43e10080a40701c940540c00391740c450003c0d04200e01449114005c4d404d105884000e400d083c01040000d0360181d41c1c04003d0380d1003050440082801c0c080300e0100844c84a101101c95540e10855008540d584a042900503d40a492201c40c50740e0b15600b0f041c14105904181c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 888078390 1250 888077140 888077149
    0x30e04021602010e040b060406081f060909050c0913020c1b0a030b0a090503030c070308010b070b0727180f0612140309041b08091f020904060513090b0109020702 71
    0x74010750a00f8045401114000010050000410000d41069004c140001c0c20769014920601603210b04615000d0000c00b000b040d41e400f8803502820022a860341000c002c14041940803075440070300912418140180c1d00005241f403041c0c04c112461064020030004081c3c00280300d403914050a034451000f444104e0000f0075044420f600c0080e024454000c000390800c5d5484d001180301e240c3c48000d490743d0789000c24110711a504000415000103804000100c0d8004910341100c14064006071650500d6842842c00c661b503e01100703001c180300001d900404540085804140c000e000312500d1304010001c400905000c50725203071680c806203420500100807511701c3c1108500481d030404404131000c1c2d00121807500e94810400e14940261610501b07030024440280400d03811541c96807a0001c039201e440b60b0390344e203003020388885505607010007880000d40030650040c1100c800107003011400315a680c001440c11941e6604103462562070340c02c0d039010001e06503010340c054000c0306011424403400c0e80108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 888079640 1250 888078390 888078427
    0x8040f084005010801180b18160203250f050a060204170a0f0809220516080610110a02210c0109030503030c0d06050607050a06050a0b010c08090a0f12030e0402 70
    0x101c04086010043c0c40a80809810440307e46030050320310200c45200001c07034003828000322485071078080c041d85080400d0f0320210848883c0c90b201202409080b500c0d101076980c51401040031103425144040c41800243e0510002da400c900503080142c41c0c0385032240c02070494000040c0b04240350800300d00c2c9800100c010044005031303500204003645038014200442c0f408525400e1704030018120345501d0050108035004140700c0c40708071601000700107a00f04169200942960101d600108455a0011061107207d00c079240c51403000803600401c602ea0042542c0e40310400d0340c201103801158de1460210420800e407021b0700401c2c41d107079141e140ba5443d0580c807408060442400c140d0000b0708c8080701841c3d80c0041c0c000d4000101410350780c214518000e961403002d040200d50035428400040c8202c8064803820a5449042e1102070742c0c4d60103540d603806654411401c095000e500c40c0310118040054090100140510284107030140c041400c0103000103900c00c0360240301d40d004001c519520316880011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 888080890 1250 888079640 888079649
    0xf060307060839041505070809040c12020c030403050f07030201020303010303080a090606090e1e0309010806120703030f02070b0414090702070e1e0a02040608040f084005010801 78
    0x409000842041e9034200c81204480280d40141029007075001c030481c3d090040c001c94500203a0b468a10b505150241c8141c0203000001e048158280100081420282c0051503a146d0901c0c04406d000030541186040783c01041c0540340c01e27440864244100b2004000d41591059003800a1071000d141d0381c0003d5891005000050030001700a020440003242904100525035004105100c4c07180c070f40b030906008182c43e0a00c403046129060341d83d081c2d15501950b4202004c00480914a01800385005542c2101d02801160704070114a8052102e0340c800d12609025510903910020340c0b105403d0700030300d400380f19006078034207007020002000301541c600c0b812403540358280c1e1201015540d814060b403e013481980850004905101000a0b8420740b07000e0700441c918203a242a03081c2c40c0e99400d5000ca0055001301004501d8141c085030224070220500c80c0e038644119944c500d814400300540301c06642c9500500c400d115500d00c503032001a002d8860002c0d100000c601c800d28103180c0800204802c00600c10b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 888082140 1250 888080890 888080911
    0x7110105010b03011a0a020f0a030c03020c010e0f0415050916080106030507020312190e0609160e3c07080903070f08031306020f04051002060702100b0a080a05060f0603070608 77
    0x40c41b001c020300038000102c00341034042c181e68104560f07090240004601460417401801200341c1c0f40105e602401103401c608101030111881c800c1030109000007010301140c00441c3d582002d100160607640d86d64044c0c850400541c5640c0030f40c507490805000341c441030308070405143c05c2c40c040004260740002520041c5d5201045416680c6600d118081325801080c61000c0751414480c1c0b0000c0358800040c1c03035000e040c03c0000c4a4002d24a41030918940d0130380e0144a4442c0128030101c1c280903005121203401070350150741c3e2165003032440100c1c85c0400070200740d0710456500c2d00400c00240d421489280d8400b0709003016620306041e80d0364600b040c4410b940001c10914001c4041400f421003440c04103145544040c0840d6912101c8051407150f0b0810703c5268032480c5152103900c00b051010505600500d1981c0007054200d4401d118080038120035840140c003c5614103000503d942c080084950a60040e406428181400303c4810b0728800001d00190095100030b030308004046e445182140d10454405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 888083390 1250 888082140 888082147
    0xb04090807211b0f05030706050103020a08070302031c110f06100e01080303070f02100f06050a050a0e0c0a140301230307050f040b0409020d1a0906010f0303180306020307110105010b03011a 83
    0x603241910a07440c081c0175009100204810081044a500c841d068a000319004030711180d4456400b681c801702c902000350150000000f0036040b075076002002070702c051681001004410a82e08043c81d010443c025980c40f03a110b1010701c5010700002520902800d03845000010341c5d030520390340981d680300c0680040100009604a11201842400a4000c09211880c140008000901c03118041c0510b0700445218088500c0002414984804500100c0300c0701c0c09203035802d40c0d40120158280d000800c002c1b090000c00074110301c2106210b03000b1030103864078622400d800a61a1424404c4031004601d0134043e030300c6000d050005650300c2d28144070301e0204840204a4980310340c00706000d02a0908000e4128010300c0383c0204000741103e9800421070024440b9240340d590844c11565243d0078400c06542211000003800481c1c8212814801031124480c0300c001e482d52551000104c0e8000ca8a4030001504140a080304200a004860061040301205810f550402c404440001419130404d20700c0107000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 888084640 1250 888083390 888083393
    0x41106070f060f02040303080a2708090d0b01092d0c030204090504050102030403021501030210050f0705060106210506060d02211501030f0e0607120b04090807211b 72
    0x610704500115802101401041d281d1820180a03403c1800102d0200385040c001413a1300304c86224980d043e403402c000780f0302425204299007451410001e4182c4010a0402010705a03480b141e409031300c12403158503800c101d50302d05440c01084560302141c2074041d0b84492603464211024404400322020f22800000c1d0707101c0d9050b0150b0082c0300e150b024440d014181010030040c400706501861145000340c090302d80c5120b80f0003402400c1d4200b404006e41c001c0d401400c01c04075500c5180980080c225484480d450719600b610f0b1340e0701d48078003640b0032400500320a2142201ca40a01f10421b04064905024091820507000180c85070081840381b1280d164040b88060851802076031112130f43c15101d500c52114140a011395402c60401d00c116804a424180d1007040141c50f0b00c24009182895000307011591a04a030031141e480c100040c10700841c1d00c5002120721a640c81c0309140c44c02c0d00c07849809544030400d10b4003000d9499114081c5520810210341c0ca440103800c114a54008500e6014a40003005107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 888085890 1250 888084640 888084653
    0x30c030f2102250f032003030109110c0610180c090e0702011e0506041d0a0609030203091e040518070306022209020c010509010b151305100206160804110607 69
    0x40c043c00790701120700c65a035482402001110298120f002e42c2c0c5161074010403612120640c0d0038900c0c0d05038103500c10001005005016448060301c0506140894a00010034105519041d003d45440c007160300f0200040000a0040c40d4840382080d0071003050042c3c43c0440710181650420740300f124140c0c0440800904818402e5014201c07400c01d030090030350441e0070205c0303280042ca01110744900440c60711025441100c3c012120380311142d1007500800e6203d001c2c1d0b03101d5000e006010303000c41c11741c801070194480035510300341004190901c0990414500820320b00b040140d420140200e00b0b400300c03200c4801809a0085620b0080c0d030741040300543c0c0d80c9031f150000402442800c0b0080d01000301c0c5900882c072212a41c0040600c403184000030300040c0c40380820607003294040743e04a80d0014205450460080218016140040c41c0d4500185400c1c3d0341d9010074140d9440701600c00c0141c12030300811081ba400080904c6c01c0003070380d291200d020702c0e00755a00d10f0030541d0310520070700c14880428540c04100c00f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 888087140 1250 888085890 888085927
    0x3130b09421302040e0f010b310902060d0905100204150c03050d0614040c021c1b02040e0a0b090f0303060402070809120106141504030b04080d0504030c030f2102 71
    0x38060f01c1009035041e100b903110346412030349003048655402c144854810345050b0035030107440c030142048088500072035001d00040100882e03052000c252560250802f503aa40000340101004102000c59074402c28034101c0e04010040c000101400e105001c20b115801c044d0010140d21505418110b100344c189040a5a0500502c17100170b0016017011000302d4083c3c0452402d40903000d00391014000c030b148d041400d03a10b400c14428003081d0003507036440741403005102d129802c0e082c8015074140f001585207074010809442c80c2516060485d400b80c0750b040204118184410b52060f506c10250400301d1900341d00548070320002d41a54400d035000302d0940c0500100301c080301c4141a00801101045491105007406091507100d9000c0c0407c0915660b215400c0511620010000340041c05152900b141e8440d6540c00003d041580c4d40c4606204019500440307104c2d1b0fa00850090325081c984001920b00100301c00d04e003096010420802040100741450400240805012240300240c1c5450010001310700c42039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 888088390 1250 888087140 888087143
    0x70c0302100e0114090d0f080606090d050309091b07020105031012050606030d11100f06150c0c1413051810063803130b094213 56
    0x185400c0300048558070551140904001002e481c0805540d2151442d46549400d80303203c001c90024102001f501d44607200c210340c881c40040003141000d0040b030100c0d0215281d083c046890354400124461a03181c0092001c0e4040d5030f03102c910300c2010301c500d41800c0318002c009009052050110110b2000da1a40e545c01000e805e54501440350310160341000340c1e4642c02940c12031701074003400d400030103000c3c415004034400e41810401410b00703c8500e03100d880100076240305286c1c4540d0b02d01c000704402c0807a001800c958181ca130380f0f450000405044c50288200b4542c040000250b4400c1e800b10300e0307101c220011103186045e4400203505d54031003081280549044440c4156401484840c40003410181e0200d000d548895402d514410380351000301c5141c901c070110091a0940c2452912803007000c44000f160b100c072180054060000c0d42d1341c1d80c0351103900c069882c0701241e00035684910200c41d01100324229401070112014423a10052003949240d4a00413003280140241c0c8002000c2d07120b000f1103000f00c030303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 888089640 1250 888088390 888088423
    0x7060807032a0f091d0405100e07080d0206070f0c020f1f020105090c0105031b1603030c021902010905040e120a0503071b02100e010c021306050a0b03010e070c0302 72
    0x56070716510030703031000d4001c00c100b80422003201c6101d104a101d4240c1d001a030307110b0340321805030b0f036500701228a48801c02002141c8030700c980d00e44881d000d28140545400700c1900b4001b002203904001807981000d401540c070b6400c41d4080700410564660003441c21140c5266400d00540c1460709002049000e2724803070040750441100c13203001c8510016040c0c8034081c1d00d03507a40204038030348554500c60303210540000e50303e0002e841400407a01c01003218000119601d10915002c0c984100550700b03002c6002412819004607544071940080580c062043c00c21101d20001c440c000220b40c0d074000380900d60a401011b009076620703600f04810000400c90102c117040c0b5400f003140c4032400d41c00c2c020000d9200301c4445001489000380755005420886860711010f40c000c003950401107000d24100c654a610300416410440c1080004015841f815889001e5681d94200401d54600b00010700c0b01e94000d82c0d00c5803940f032608200412190420a09180c0c000201e4542000400c8807810102d103000310091618921 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 888090890 1250 888089640 888089681
    0x20c01090b0411211e070305150a060b030907030602090d0204090f060b01050403050d0507061b0c0605180307060b06071704050f1c0f03022401140d050706080703 71
    0x10f2188504051442c0740e0101c1c0c50002095180542028658450340100e69507403188205140305080030342030840da400c1081c11100e46035500d80382d030ba14050407070f41c040c00030040807810711080d442207000e40d02c080c0207443e020700d243d420260f04c4565188818400503001950110f20b00040b5501c1240c4508000d800038818030501c0403d0400440d8842165000c86046142500c200c80f154015401e07681141c0e0800e003d41028010003d00355056880441c00710744081c3d83c0c41d0034000d1202a0701c0a1040d15915540f00384c845a180d103400c2040320400741a10962000c1c65040c012481400002c9465095100d0401f0411001c4c1c032011560602072260011f020384507071040f0010b641c140001400440d0000c40e0481c03400c2d0f0b25003041c0512510004881d4004d024141400c601080912090820103403003407044580d5688609241c040d101e03d203911a418521540004008440e2641e80010500310200c920034854062507888503034035030407803080030f0621103100001200d40e4003a62100700d01215640e0310030305 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 888092140 1250 888090890 888090893
    0x1050c0706050c10111e250b0718050415050d030f08061c0609020d0b07030c030605311b030c0f1404170f010608160e150103020c01090b04 61
    0xb590304007201c004090311451240c0c0400c02003500072401e190300344024039440c011039120042004504000e2140303a03040104060440800240300c2d0010b012140302c01d244a02e10303079241c605a010405414541006450080c0d00b21141c26072402c10111002241e00261155078a490f03140b5070096070780f00f03951014a003089001810303044102c02c441c0410540e988107641da914810841c0c4022004914440c003d44d1050110002d40c013540100c034030b0b900041506410b4241e664402e080004100e175080006500c80641100c019050300588000d042d00b1140c41c490009031401302c0384900e0811140c0c240c207151103021314420040c0ca90000a07021070f030003107a1040388102640540608500070001d00003e64946211600d135200d600c0e004208115005124070382231808024140250044a05105a0241503500041c0701401d201d50001000c0503000f40c0034000d000d16140702c0d540013540c441a0084562002c218240c0d03404030b90180c1c04442402d0040c0c80300e180f40c0010340103003054200280360710481010f000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 888093390 1250 888092140 888092147
    0x9240103200406090e090a291009060602060408220f060216211709090f040b011d061e0402030a050a0608010b0d02040c11070b030105041a09070e01050c0706 69
    0x42a2080c44d260241e003a41e4a01e144016500704646094982c1c00a4980700b000034101ea460b00840c0148103240311903414100d440c2486103034250744d13068900100700000c1184001a0080704000e041c2e50010701454500783d251212580f20b040e9000b0060703021b0943c0b64118920002a04001d010504035050600f0340b170b0701000e03560782442c43d14030325508107241000039054603034024140004100d85d4200784000f0250703100c42b00e40190501d5030116007800c0c0000703810303034590f5101d440c8500c00c4080903e00d83d050034100624001010b8000310f140303038440900d075000804a04003058100310103035200103400b03401d56100000c0359a500031480d4000d00010038015403401c0350b08520300030301d8282d9007040b60030703625800d0320300700c07807042d0b00302e03a00a1103604903130700036190039400010704132154185410301c29250b02926060500c10b4010489152002c4018031050425100c1e031510401c03000c81002c1d404800500103444088002e008000b080211032580c065039100b902038910203844171003280e05050325210b014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 888094640 1250 888093390 888093397
    0x33207030e180106020c10020717011b14040b090409120f0305060f0a0308180a030b0411041a130f0c0e0310020a140703090b0415030b0924010320 64
    0x961249042c0e02108003951042a08039040b921150005d088100400c0c09010b001c00786102114291300800c071001601c180400c01b41020024298000110641c0301d00b18032007040e031072031030f08010084900031720005002074204540c140c4c1d14010600c3c0e01c0301d204a0004000e44403482004041c044641c50400010781c1007612204000c1c02a14184565541d260174404003c034900348a540c8440990820404101c03079100070038103843c101c26820a0407541001090b40c84859601c00c48040f14130350100710900036030040d800c4042101f25400d02111450100340c5402038001183d051244200e03410701c0c0700000f60344c1d100ca030840540f01c07400d00240340f860710094910b400000c4894024051100b100a2410462003100c0354007200c1d40300c451144040c20181c4e8007541201800b01c061142e120300100e18a0700f000c020303200801000070074010440c03440b4030080c241c40c400760b0f5a50080c0c16001c1808182051541402007440c0c1c02105041c01c4107000004801400c2c1203002c001780380d1196550040e400241c20b004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 888095890 1250 888094640 888094667
    0x100c080c0d0801171513061104060c03090f0b1206010c02040f1506030228091205030d0e03070b0a020d060515030105010e010c1101231b0d020a03320703 67
    0x18a811540c02c10405841c1e95171020740750380001c01e8400044042c2c1e18019400d9485000340000034007840002200d01d51030344260411408141d5560b242002c06030310203003c4010b00703a10f410b8030800c6031030007007120320501071100241506a104000100141d100e074148070245034008209000002c841400740005000401003030343d000a000c00041449802402103d80780411803a41d0001c2209086940608448991183c4108004400c2c0000c5c000e0160510140103130007080656030340c01e419030608007151034507040801ca6810070b02202c00400c08018005600140888001d42d68410050180c0000d0015400003030384880081c43c0c40da0399108903405507050b11001e0322505040c110141c010b40300c11003280401466007084490a103c25403207480741384100d081d00c003101c81c1d4016070004000a59044406910000121040c035410001e104024421031403205001900c0584001d4030010307d020b061128480310b544021100c1d5030300c0032a0301d41c01e10000c10030b03080040d01c40c0c100385002000100d40e03001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 888097140 1250 888095890 888095909
    0x370e0d060f051f052b0f02060c012906190e13050a0b01030213150c0605011401020610061d0604080601030b070806040b09010611010b09070c140c100c080c0d0801 71
    0x2040c2401c100045d64615860b00403009509000b40d0440c141404030094104c941ca0014007283c001a00d460000c2c040100460f8008648152941500700c09465014468032081860901c4a803483d15840c0440f0b200100620012507042041507095504003500920580c000078418003090000300d05500550003442800c20a200001d100001142a0b008400c0d400796000f0152004201c540040012100c2d0342800c2c1c201810008a00e0f1182c100301d902c240c0c00640c01d201c00c0035510f0756544c0d05001d2a60700504264005409905211000781219a00a00c2048030031842c800d000444d42c4410a42d001811100e080b1a8950784900d41408200000e4525034086814500481d21602d0035000f141041e68024210100f1a860700104440080660040c04040c0d581c03582002100c1d280e20744c049100f410380b03484500015442d4586144800b01c0660140b1660300315142280c01540d41390445c85445c2618681a100750640f410004440c0c8601140e4501a12500c030001d1240b60700007032854100c815182 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 888098390 1250 888097140 888097201
    0x216021c0506090f1b0a060804050c0901030c0e060118170a05030a03060501140a05090f041404050102030610031505060a0917071706060901051212370e0d060f05 71
    0x1c03041c50305c0016850841c1c0c82050900705004041c4502e00d600c2d03000c0d015404032782481340c14401003040c0381c05c02e810549074400c1e254030074452000e80d032a000d40c11840a2030000109031034050100070315100c5008000d08a500d130051080c10040c100a41c03c005070f080f105a0340d50700800c410190013030400d41700b00c5000c5009060084000c0389507006907511405140c42e010310b40a1088100301c3d02c0c260403603001d68000d035608107003152004402c81d40b52080348282c0005a490070074404000700702d86581d050000b014100046000010000201c0d00c08603081a2006602e03806103100903110318141e40c0010620081801ca8000c40c22000101501143c0c8810b44c3c0e05903032040c0e11041512044115039503a084480540100090304144200300c84d00007401056070300b0303007216100c0c1180503800049894954880845141c101100da5041c4901005100010b030080c0406810702404021140d020540700b0340c2c030300c0f10b0a020701030203402c00d00720b02207035000400240c90302684609040003104410001c640c0c884 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 888099640 1250 888098390 888098413
    0x2b1b0e010806070203041401050d0c0f03181106030406110304030e010e04091a0604020f041d010518220c03050a030201050f07020705130b06030106050c0c040216021c0506090f 77
    0x1099442c007842041d406141b8240c02d00c4404000319410416030750400600f000480682c0040f441820703007528550303942c200198520382c0000e080e0342900f03048000c6901102d500e14000b0b592058000c2074128180d6150b5280d542d00d0600c00c00030003034059104490b102c0007003080f04140d0b01031100060366009881c2c9424450001c1d06000c100c84200c0001007500030301017500e031120115055881c0e07200e40010030251405084000004107030b0015401b00404e10000e801541034030341c0496100e070250506903481e810310b0101c40d820000000e0080c0c4444a07801003041c00c00b0020b107407000344141d0f079a041500100301d1962854895034030414108260015481d010216101d4858010110b01818259004005082c200010866001d00d075254100307850390745600c00500343d11101c020318002c11964440540300e01c6010344090070a2100180903110398410000310844040e001e841c0205031380c041e50302940a1509899298681d00901400303400c80c4079100400015803000540d1241c070320261400d5070b402c803081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 888100890 1250 888099640 888099643
    0x703021908090f032a040e030f0901140f042d0e16020f01050a021309060f06140d051906090612060504081201030c0f142b1b0e0108 58
    0xe84000c0080100700040d010900d00b4589040d2161801070543c0d11200102d0000c030140c03024a50401e01000034400c1d160000d00d01840741180f08001300c000f45160000a14000000c0e103e43c14449041c0410a401c843e20343d0000c505556542d2408a052a622502c1d0300301074590b14500c403480c09406064a424000001043c0010401c441d5490050140c1e51100403601e2420b0082441207801c511a03401d042d01c03140c500b4007405014940b090070041c0c0e0b410002c00794541d81036190304803060060503c0c40400a0481ca465600308407109860103d14000d8400300d810010b100b62003507a00c00380d0a181c140440881880d1440d0007003480c45008100710359136654114140c418a01c681e201020441d080c802c0412010b81005511078030614401d4a440082d0740110f46412081e0010749802c0c00c00603044c0704400b04d01c017081000d800c0c00804100c7e415080f40008180a041c000c0344d02d000c0b180144110a003031420000012500d610465040c003032a2802d580f6401c0c03500130300c0340100c86501c0c0c0c030000490900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 888102140 1250 888100890 888100933
    0x310050f0d02060d0f06030b041a0906060904020a0306051f0510080a181709090f060d11011809020904050f01033504031b0501050c190f02060f070302 66
    0x1030141058648004035001c00c40140c2011a4a44400380c0f01c103000c075803003038491003540003440c0728011a2000b81460305003026051414a9684401103682040c40503d4038002100c0350311034811108081d442d80c071403003c509654415400200014248810300c0010403810944c1c1c1034072581c0031020f1444d00e588104011201c500481400003080940000c42c1410365580c0040352100801c2403404030848499540e2609846418181010b00c280032580342c2e8107140c00c0c846a83c05c94442ca461001d00e00340180040c40101c806800141084007103d1110000d90080c9040804244844500424590354540e0b842c0a98082c02c0224410761901001a00d500b0b000e003480c5050343c3d00300c46c02c40506c1c5415030701d4840305030018110025500b00c101100c2e500d10080c1000b40081c0d441400540411440e4181c42c1000c40c65a80009060010a02c0034242ca480005102803410350400b103010f61560403410300807450b00b8084c0d00603401a100240220706a582030009000d039521a50172181d071034000404000180b003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 888103390 1250 888102140 888102169
    0x2180a0e031309021b030a08070e0a1d040201111b04061d070507080706020720041b050d020409020c0c03160b09100e12100e060903071403130605031005 67
    0x8030703520014021000b00303601410b903203204217240500054512210030300d10b400501c21403001851080c00c006441d50300003000803000100741c0c0c0c40c966481c20025003551040038018a8425840030342c0000d01507a204800d144010750224058818008004002e00449041190024069410030340005149003120381c0b00103418890071040c503010f48824030304503030342c0c0e00c805402e80f1000824403001c03000c50401d100820780144107007145a40400305810381d85150040d020658865458800c1d1000043c1400b41d00c40c2c16081249846a52032020403060781c000c1c040ea401c00128940701292040000c140001d00c100080022000c9a50312145a1b030202c0ba08a0345024070602010140505012824504498180f580050401c40e600c15045404654034489510130184107034041d5400c03c10080f0103201e440c0e49252880054820751a050742207560380d1050041c0105103451040c401c00b0510414416512035907840c400c04040300303503a9034005000d500305543e03451400c24500000074183c40c06404007000c09 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 888104640 1250 888103390 888103417
    0x705030a1214040b1305040e01020a02121b120406030e070b090402090a15170c4e04030206130f020d02030118060207050105010e0c120c0702180a0e03 66
    0x1c09100c001114041c2e0400814000228240070108002200c42c015011a28a0b0042c00000c2440e1404000a0342c030081120340c05030340f041141a203941d6011544001240b142d80103d035a030319241c1c0319440e4002650212030703024010040c9071014904003e00a0003118000c0c1c2e400c0c44008415a5110785503406e038464600302910400800100b0b04107a0090301d19540000c2101c440169102282d910b8440c0300d60340500003c0b02d26111401203c3c40804d000d41100300c0c1d446207818070110304101d0820710154120f11a1000681c81c5200004484414240000045c0d954a1100c8050030000c0083d2010584086016000c0c3c0e6000901c1464030112803624503821501d50301c4084001e400340030203001d40110a0343c242d5251011448904da004019903010f40c03043d2001640c504041c02c1490031948113070041d07003480800b4000d1090b885041002c2d1100020240340303890301507c9514450505100b41000250810500c1c4a044400000c032801184138014903c41030100034100a0103d40364071038401054950f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 888105890 1250 888104640 888104663
    0x30f0106210203010f02030f2a09060c0708031204030e030a0c15020c030102041403160e010b03070c0f0b0619081e0f0a080a090e010b030c0f090904140705030a 70
    0x5031070074800d5101e1850000c1d000003031400b010080103041c0d9104541d091010003009051151250803034032960b10305480b059110b020301c1c604007000700c6240314880e0080c0c0303e01c101080c504214601030105400404040c002ca07982c0712841d0740035940e110003c4409401188003243c5406c8c3d02d0902081d5420301070b52001c10f44030712604014a4200c141d01180448045110f0304040081540302440104007425010f280100412070303c501305407422034284014041d501130b20710208403a00507103004034196894404400d407030b50b54050003100e01e140c441d4070141640000c1d00d610390070b108868075a40d000c2c8000351a240400c074180341040701d82c9140e610034000b0030387c01141003500034144140d800e00c650202006669000302010360840c604901d44c001510f05d00700020384004941c3e080040c80c0700401148a5600c40341d0316014045010b804001c0c10003d08042c0000e80c8000c0d1103000c801c0b1400d10304000c01503a40703400c00d42030160300400d840c1084015482030280c0881d15250000b203a4890b41e034861140c508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 888107140 1250 888105890 888105929
    0x1e0c020a0b0c060a0f1b020c0307230d0813030303060f0b0c0c060315150301090b0a080c01030c0309060e010c0e030109020609150c0a0b15011103030423070b09030f0106 74
    0x901681e00c03c4170445640b80b00355203002010142c3c881d80e15205034014200d800200e800c050030413045512050803809081e5015003084ea280259518144003203c9808480f14142000c20182c465510200310003407001401008042d0168003500540d15200c0e448400d154813030125508601c81da064420341caa104503188141c9240090007140d103c3c1114100c081c02e11001e4006c0380712047c20b1115a20000710100040c80003181c0341c030070a000c80c1401c81c0d0001c18a1300c2e0141550700c0f551500751030350400d5120101003102da8001c1e000a504a80d00002c02c05c501141d902101e402001c0d215540c600041c0c1a0a117034890749014052010401c0d00100405c1c81d0402983c20050040100110403400d07480521140038018000e003d866400e030300840101d1242d10f41910780c00b103240c8000e0072030781c1803120901f03080d080325000005699000780d0203140d00b070b06011550070341c40c1790703210901080d07a4034480c030304d404035101c1d074640054801c0c00d4045c0d04851441b0070400500b0300343c40d0f1602510b0b1249940302c07003150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 888108390 1250 888107140 888107161
    0x5011202190f080a35070c05280812090f03011d06040308010b0f1803070f0f030b01090501030209040b07030f050717060109030c12031e0c020a0b0c06 66
    0x2280c0740225039410080e15a91620340031002d4040e0710a481c1034014035081020300c80882c5a1441c214600c481500c0b0410460504550002010440074090780010800c9030400c0013007200380010700710041160701001d000c100707021035214040c3c603500504030b81000c1c002074002d00080e907410a548481e009608012000041c480704c909103040c0d40e607156403036030303200c0c09080c200707841c0d441c200064100505a1403400b4203020b000004c0690110071520f03001c02c042d103400f0a42030191040054600c0c02120500000d030700027442c2030700303603045442ea0290740c010004d403045c0401c029a080306e00c01c1480c003210381c0e03850b07007500304a0b02c00f44000381d04121841c00040000b2110a40c042e8050041c1c100020203001040d40c00b4102c4004030355981c0840c03524000d02422180c4581d400b0f074400400d00c0e003891198115a10440500c00f14881d0f03070180c046000740d20302050b009645c100b14081c4000901c9592400c00c06005101c0b600301c0310107a004907900d01020900c04000c5044803084900c44000303144680360461002c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 888109640 1250 888108390 888108409
    0x10180605090604150521040209150324090115030c0b1e0301030b151c060b061608030f06060414010c0305040801050f0106023313120f02070905011202 66
    0x2641d0010b0204004100c8404214803003441c0340c3d5a03903e5035141c080b503904059080d070040030443d003000d081c00200030044e40c0352403000d60b1201c0a00ca0184800e03d82c0400f081c03030418107840c80000c000c41d40c0a803080c4000103151040c0300d040040000c0c0a4031207245a04900c800181c04083c010380a80c0c00148008100c040042030b03401d000401034850070922800d0103403990020703001103845440c120107010002c0001070b003403010305200300d031a41080352220100404418038400001c0c00302d80c0340c41d01c000c51550390205568010381c00c146802c13610401842d1251040d40120398400010101e003010849500702001550151107440b101e0f201e0207110030006640c9820a03a00c01c60030070008010100d0341c444c080c000c2c117000c1c0d03600c013001106c00c0d414088080d044c45542c040c4040e85400e602da00d110706c900285204c1c4441401aa0300791191740b540c3e0208116500f0180010b44290300c0030040c402103513400032025103800b18550039200d5003502e0399001c0054980c284125146280900c50740009450404010b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 888110890 1250 888109640 888109657
    0x3090c090601030b03031e1209010b0301050105101d03010204050607050a0b0723090a0f0e090c0906030c04020f0c0a03020609070b0307080106050a031d0c012703120207081204030210180605 83
    0x1543c101424610f023012596401c132580020f99459140d40001c5040034000c40340904021208400f50707101030f040c0101484000740e461021603440c00d984900545080d411540604400390841d540c4203803a05001e40d459014070350407101c00c80039034000b0382214802c28160b406880c50001e82c110700000c041803200590000c1001550041c2110340020f070400c00a00043d0050440b600241a00d282c001d200a0034100784101490080105204105043c0c0d8003080283c0104c0003210011b0300e444203101405c0301400760340621540c9110780c4580c84140364000481d184110985412074000f40d4032628818002e00042e0b0300500883c409100501403107008802803c1111880d00d0300240340d10815403140400004c03c03a818140d03420201e445406540e00c000e107849030707881200380c170946105c1044030f2190007140383c480684168000710071028014801c6c8081c1c4001d180200440f0000c00400c03a009420380d10070f00c4103c3c800c0e401d0740d40030619140500301c8014406a08200c1e010308601d040010ba496521001c00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 888112140 1250 888110890 888110947
    0x501052205030703140f0c0a0915050d051c030b03070603180b101701090b0f07050c0703050607120c0806060a050f0c010905010b06120118090803090c090601030b0303 73
    0x7140640b4100721000080d80650040d42c0d000050540441c201403407001e01c101c0e00e8210407420002915200c40306421202200310000b0000c9410011500c107001e20303003003194050424100d070703402e00400003600e21b100544654642c0001c0c6c041e410039030455800343d0321541c1540005804002083c044d034000031a43c101d101e0800800121a900c2081d481c40c1200c4540e070540c13280d4414000700c07003110310750041c018059008202c035003290b032910785c00600014100c4a0b17200071800010b0070144140181c404002080e0219a0780075100c2c0740c0503440d00d8045420000048407805007041a50903406107130010242c5803101c1d08240c80780c0d0244505940310b00011000c1c0481040540c1100b841c03040100b10103900100001806e0ac3c0c546407042c25101d2000e913851040c1801d001044484900882e5241103844003140c8100c41e0141d10000c030054500254090f10b500c1d800b00801c0507504000c2549400c801044901d050030360740707072801075080741d901e244025015841070000300c0244600d6034103e55000b52881 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 888113390 1250 888112140 888112207
    0x1e011404020c010f1b020f060a05101d01081212070c0219060e0307050307080304090b0102120a020109210914060d0617070603020915130306060b120a06050105 70
    0x14011030944104400d00c2c2e858583e0343c00303441c0007840307104403403a5a5685440a800c0c801c4140347c0c03490303550300045c10000c1d070b540d034410201d170601d00810030a800a040401c801a146546140e442d1504802486400518060003070340c4528903000c0011501c41e9807407010200d200361a020b804071040341091008903004040d000101220041c20444440207001b0380c0c1c0d510b48280d1010301803508001d090390045000380d01c09441800b51090120603034099402d00d0400007454000e9000403807030011a600c2c15100508002980c44000b0ba040d04030385401d5004104649100c25000c8040c00e00025042101c2c000401e02841400140c0d1401ca0740001520028452410201041c40b007a0803105254007039803004e00215281d4811000a0000400034100340c1021418840e02101040c1c024500c41b0507a4420200012110000049058113030b01a40d0010006c21100c1d4481160004682c40a41c048100c84465030000d880601140a0f01c0c0c03d4175010b075112420300304842d007844180b00200c00b101100c0700002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 888114640 1250 888113390 888113407
    0x7050304080a1125090b0910050111030d02030a0e011b021009020604081009030f0c0506010608090102070507060f020c0a0b04050118090e01020a08181203090118050a0b1e01140402 79
    0x1385081c1e07481d842e80b20318403020745808428811607860094040c0141800f60820080000a840d060110780080c02c004039058502d00700d443c15803040100e801d451a20100900c05070307a40a60081d0880c9022000811403080010006440309484c1d20040c00140e02036140303c01c4600a541000c001ca903c0076112a04140c0c4a000301c80c14000c41c02d8203006c010765a01166000d16500c07803420b1108104900b82000c15035240d48680e9242e4405002e42d4081c00103a001003911180300758110745a036134001e41030304c003216102c0300010062a00000d40f500148141416180586412011b01e4111035905401a150a10346001074610501d12008034440b50903440f00041e0a01d9603009014491a80300001079a4509950010741400809094802c03a5550078065000c2480700052402c0f20103504114540c4a54a2001da5805885241e040003014074500d03007900c042140004424003a00c3c03040c4407500da10b944040043c5006618034900c000d0071301314500100b10550140720303014000d50740508050703e440c2c600c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 888115890 1250 888114640 888114673
    0xa03110d0221060717040305071406040f11040e03032403070602030304230c0d080c150f01140d060905010633030e1b18070c050607050304080a11 64
    0xb070082403a5800c09890b01d9000b00702050103500d41c0004542004401d002648001a116400082004080c01000150401441281c04c10300d42e105040000711080e5203001d2030310880780c00c0d0900c0120391900400d10700030f460b442e00d40100401c00c40300320011030030741c0d541c81244c82202c040c03070607200e0a9041402034440c00d503c0074003102c0f0141601c0c1c0c004607501e080618050703000d030988025005654000d0856000f0000c0c1c042580e04100030229023000805030582009030451050700502100352003030b648040301060400c480144520f5030102c40031542e80c0d0350707503003101da9915070051150700c0b4429900030400202c9a0307000c1c6107200d0040000241c1d094540903c181c880034808560f03480344c81c0592045603a1a46490000741265003454241725680c4041070490b595a54842406111000301039503c0c1c258851490b0180f8800c44855034640300d0524120140132840210720a484038011440010055030007841280c3c096644040303254a803680c00b66080b80c40141640c0f00118a0066641c190720004c9c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 888117140 1250 888115890 888115909
    0xb1801084203010507050406081b0d02030415020a0309020102120a0807140c0706080411041506230f0306030d03060e010b2d040501260c0a0c0f0503091005090a03110d02 74
    0x41d15114075a03500e06101009d000514002c02c0d034950190100d140f14480e41d207002c2564460b0075001005602d94445207801c03c000500b02440584140c4007040c00403080341d050b0001c0008038000e8099828806000d107003e0810700c2500b450703002040248000c0340c8014803a64078100d23400c82d80078055050864450701c4a013080003942c03040000400660500040c84002d01c0300d0420004126000c2010040242100140d420680b0841091080d1120031290399101c5020b07618400d040f400d0015500e41c40da4030294460340064603414001d200e014400c0d086c55019100c0c0109031034110422041683ca400005074442e0b202c0001440e142810840c0c116580102d075441400c0c3c0c454803840c040d215420a8001440c82990403140841900000044541041801c1c1c000342c21330810700d6010795924408405403a5040303030500080014040b518027405019011014103e031800840c1c60344020800407000300e5460040a00c0158000071652040000507120344005280c031b00b024207a010001c849400040c200340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 888118390 1250 888117140 888117151
    0x30d0f1215170616030b010c05030c01051008031c020f070506180115051f0e131e0e150a0e070e0109060909080f0901090b18010842030105 61
    0x184030007001e018444001c0340c1411010307850341c01041e25260420b0881ea01c00c034001c061006040d41c4a050f000c069114501526000b90044100e13666502c4420f4110700800c0704445c52220302d03540319030210700c0d54400700403500c00702c8281c210107451000d640003801c005e520140310040c0c201e00401542e8002441404060304c90544030840b103c181c1c0c08621240c0c00e45400001401c9140d815170021f100702d80c2e4000c000503a02030071003202c80d00500350f80030549002d8100d07000c41c0e51010104000e05481078290b0824030715a030440d002441031000344152001554121a0340540c0b039000040c00c1d01d48041000501540040c819501084020f881c007031860910000746c00108203800703100010b00058003140541001443c007a0401c000078616a00c5020b01d50003904d9070000840e00000701c1d00d40c00d0b807040303943e14060010604080c3e0789180003c00c0c0124800007001e1b240c049450107001641c43e54642909100311103003240d40f05c3d10100315400320b148405110003110301610710560800016202485900e1154 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 888119640 1250 888118390 888118421
    0x3080c1b0319030204210525090e010b150313080d0209030c190308180301020318010e0607050d020d1d0c01080f0108030a050903010b0d060b0a0501030b030d0f12 71
    0x5040c0d028070201d0100303000b021030042c10300400c404c101d4021200c03860080d02001c054401401090780c82c0c000c1c103260900c02091000d1aaa1000880320200001d1000480300a40d2041041c041000c8005003030703903020850650b22400221180007210009001140d02c001c4c0c0a05c4c0c6128030105680d072264a401425050402c00d50103e400c0f0b0b00d030306080041000003036003103540c1140340154a03040c4211c0310072400f0044c0b1903036011911580c01842004001444d003c01402551a454441845004280a80d0b40849e0540c01c160b04085e00c14030109106007c0c61455640794940011300009a0180d80600c4650a0b665510510700301c510202d48010100400c0140207000390005000005040c6000901000c044911a00040007001300c00411a401c42509003409070b05e4070b0104002900620990f03080716080b0f694074802c0c00400c40540e10058052030200c400494140c0c480c0011400c4071401d640898041e400307540340415441c0240302d0092204210314050b000da40d444400c04090780c02e91194403284 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 888120890 1250 888119640 888119647
    0xd090b0612011b0c150c3605062a0a2001090519091503050f0f0a030e120a12030c030b0a230d0506070e041e24030b06120c060703080c1b03 61
    0x106c4111055540344030820248110887c00030b003038440b0035814a109141c841c1000042c000c07080402194a0000c00c04d0484030241040d681910b00364440c41845800c0b60740d500121700130642c2d00b0b030b8454a042c800c081a50b9510b4001c1c2080300340101029024560b142c0c00140000010328181c05025501160224002034404a491031411601d0070304a0300d000541d9421102c1201e8115400044940405405142c40c00140524002151a841c0b40c9000c0941500810015005008021141c40300c584e21542e010040c081a84408500701c403842111580c0c440c01488042000080313080003090b005000b40280500360f1f0701d030300004445008034807045440343c0150040100f0070390046120680c8003001e44052140640030319030541690044103a0161840d520410090307840750380d00b401c00854003031074800824240c4a00b00042d42481c119140d41c4540b9000d00c051140c14000b0030380707446401c00580490309140d11660266403449005198103a880f005100e41c01e000f0710451405900f44841da00503565 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 888122140 1250 888120890 888120917
    0x40224041a03040201051c090606090c0e010206060a0315061e030b0c0306090402060c150709140a0f0b03130503040312030f1406010c0201050d090b0612011b0c150c 72
    0x100e0201035007404000c10207000700800b50f6000780c12039540a110240c3c01b206441c000d08080018205000003a00d01441c00c58040ba40075005d42c0108031020b140d803201560400390000490b52250b04490751034010902c05400c00005104c403408141401c82c0e071101203034243e250780c00556403400740c00d806815544002c00c10401c1c4908a812207405c0a0700c01882e9241d40380550118101240291000380500800500c3c00300000c405c6c0712581c10a071403010100d5660800400040005d5294040c0101c20340c44148620901d1800f4000c250444001210310f0078140c1c0f0300100d80c1041d0704010b2031010458410550240000c000740000c0029521801d05400d00e081d0740b00c401011203034200c0d100701501e440c04020946030030340c6101c00e45d80030800346410140c80020b403004171010b000c3e42c12080c0d00a420811030100304403e0341007161250704c0966550314203a20900c085420b8400314810003070b242d11030a0319032507064401d81039a14494001c281d101ca0142c00024181e003154000e03141040001d91005600a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 888123390 1250 888122140 888122159
    0x9011b0f030f1709030f2206090f0e0906040605090a052401060c0512030603010605090a0b030d0521180a14070506090a150c08030412030b0406061704022404 69
    0x24007210710308448900e615120807130603980d1280c40d140c0003555501042580102c0b083d22000c2840461003110454a29910070014141d408640507051000c071100c64085282c0c9001c0c40403911980309200100070644a5480306c034024800a001c2c440c00d4042c3c941c0c680003054040003c0c4640002c991080715409061011210b150081a000001000b0101524401040c800100c400001a5500038a540ca4588a00080c0148801e40c0642e4014400108100c0e80190036808034001c40800c0e42034072820001100b084034030388501d4030210142020b00d026141c2c041100c203801c07035000f06540c84c003851540409611a01d8107058040444103000404543c4ec0300c00d4081c003940b80102029111181000a103900181e060701c2c460140c81815111400b592400f98410340403522070715003140c961076403420030307040010094030304101d424086410190400702c9400d2a00c103440c21581503940340547c100780d040a030f20302c4034006802682e104071105070701101c8849070840c0340400094040395a540b54940300007103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 888124640 1250 888123390 888123407
    0xb0c2a031018030f030e0106140306010b070c030f0809130b0a0b040501090611010209040c080901180b040303020a0c12031a090c0901080a0225150e0309011b0f030f 72
    0xc00071401c201c1c012107210201504060381943c1030409a4a0b41d1407488110b0090204075070150300c1c0e60038000001415810440142d10341c04058080d26400d0782c80781c4121260f0b2055010051100b02074000c10004600122000c901c03d9210303225403840d00101000080794071581c0746052206540d182c05441551600000e80001041201807603800c0914210001c2e0526280384590400e10540d10401c100c01c140a60460303200d48001001000038509004000380382c001c00b2074000846604e4170582c42c031208003201c2402880d6a1140b49034050b503540e542c04501a411050107542400074015011001840444001104d4440c0c0e56001400b00e680b0040862004034150340c881c040c0600b98180a05051024102c031500c01003824416607549442c958030000b8802c0354a4174140d503400c28484820003c082006101e07041c0601d90034071085076411001c90881c0c01c035501500700b070f900402c04403032035500074080c49404070f000b603502c44d6001560340c440d1055600c0102c82140002c00c64070403c1800e50704010314 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 888125890 1250 888124640 888124663
    0x2031501230f040b040e15190b0a15021e0609150405100c0c050d0221090904060c090306021305181006050f0c030a08010315090c0b0c2a03 61
    0x20406806000010074100815010143d0165868100c859080d80344c942110000c0e040107021620310042c48202c8004201007036580074862500d038020030420980a009244001100a00c605045450164003030a041d00300745001d400d50042402c0c8601c142030034040c050901c9850300140840d1300e050441681454000324020b0310b400341c3c0c0b00a04c0702080300010007891a07140d849000070982035112096070400021a0001d00620891810080983e40030881c40d400f00a0b0091480e06600c11251001040c051211215003040e000000100842d074030750030070490551507003401442c154807a101c07142030764482d0100c0300e80b03451400302c00c02940c200000074107110a020325090710300d030806242c8042d201c15188560b0b400c0100104070403500703950800446040460f031800302c9554003100c900280c00e1603800d1000380c07950903404400040224176802042042540135030090000d13800c09c001e2136181d400c644a420780610402e0001d81019210140d10386250516192064640b070420080510b465800c480c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 888127140 1250 888125890 888125939
    0x3091502070c1e0b0a0c0506060d0201020307171902070e0718230a17160617180303091005060d03121a040629030c1c0902031501 57
    0x34010115000b072080c60b06075a04100c04042140070a44010f00714110343d041806080f000107105440310f43c21006420015101e24195445a03540004100324440300b1a03000e805038204022500004452040c050020ba001c04a000d0608009a03410358400d041d01d01e00801607400000c05020400a4070841035104400d071820101c20081079a40e200c4226072031140c001d1320302d500a000d01d58a00000907043d00124042c3c120f0044680e101400f40780e40209a003034209034040c02c860007500111115800b025540301d80c0b142508000042048862400000c3c150090704000c3c0003c5500301a0500065018002860081170348442000f10768040b2034015000900c00c9090340803400000c5d400085a20003c604040d00062542c0c612a0181c02d9040c54000154813a103001d50105d0188044403031407000808100310001c082e54001c001180f07511050700c912a02d0712080c04a80c5c4005403100000e1540804840003281e061a00d502103441d1a101c9074101c14200390a50040c4402240030309010030750b00c685003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 888128390 1250 888127140 888127147
    0x3060117190e0c03190302030d02030c030403031a030316030e09090610060c0209010504050a09050609011d06010e040f0f05011104090c05071203050c0c100c0f140409090c0b03040303091502 83
    0x40005d9451000fa81c000c600c4240070b62086007418028010340708100240b03101035507640342001108095510460b0304a01003441c00d02c02c41c6000a00300f00004181c2d10180044d40380c07414401c102c0d02c0c0150000ca084082103510b201150311600c13400202030007806c02c03000910351404d2012a0031040d4a4641110042058600014016076101001c0c1070440c1d000b5a0700007040c1d107803044128060007403d0b2019201d4800c020034130141c1d0b44154040c4c000070700302040f444102101c0000e41c94a80000784103035180052800003040105d070780a4461110140310f9040b582e0154115a034607401c0d80c288c1107402141e95404201000214440d015540c408640d5142580c50400c10781e407000c0d21001981c03450b104250341e41001038849201c401c1102c1c0d014101c0012101d20321106040400984082e18180000480006054240c64050544094a80549190541000d00327040c1c4210090440c06c0d400d0703d141c28042000110b004104e4000d44c007690190341d021590750341c181000100d07000b40c01d448180c2c440c41003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 888129496 1106 888128390 888128413
    0x40302070618150c06051008120f1b0c1c03020d11030f16060e0706050a080720030909010f150c0503130612200d0203060117190e 57
    0xd0300248610b580e24995200109024888c0813100d601500829142942d11000f4100c003121110b40b0906042c96062982c00c01c9003074004100c2e05802c0901c40d82210700300101043c0e03001115140341003c501460354000e544034072002410041140600140903882818000c403800c001e4200c1015407554006c92281a1207800c003034080f500e10f4a45031140c1d1420102144000485120b501c2e4141070080059003500c041d10010049010019440410781c481e1000d00c149a000070300050081d51118012028080148010380009031814524a01048a501c250400ca901c5440900d803204080742c003032405138914090001d4450a0028000d4082007099001000c0030043c291460700340714880c114180c0501c0c00101d070951490020003041440c400114580003544c0020041c500060040051150290b00e014184d17640d101c000003030040c072201c010040c0258014041c1d8940138000c403a001 = true := by decide +kernel

theorem cover : BRFrame.Cov 887949640 888129496 := by
  have h0 := BRFrame.cov_init 887949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 887949640 ≤ n) (h2 : n < 888129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
