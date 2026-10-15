-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5435
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:51:48.920389+00:00
-- url     : https://prove2.me/submissions/9e3eccbc-611f-4ef3-b616-a3e00d393234

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 977338129 ≤ n < 977517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 977339379 1250 977338129 977338133
    0x60e1305070603060503031204020a030b01081b0d0b15060927060307061e1202031905150a050f041b050406140a0c06050901094103030103140705040513 67
    0x612030180c2100b010306080c00d600300015280002141e540c2e56412880d0425a1280c2c030010711400c035580d00c05090380c9070170300001c10040408204015050040070f8082e030f180060405000400d10308246c040c2800c540240060700555409081240d24840140541e14004010340002c0c03401e0008030707001c2e511040380d10700190500d24003d226070704a070703080b4024031007030f031070160018400d004082049564895014440c1050f0b0b0048110403c0910302220554407450142080082d812002d543d2002071420140130501010780f01003245040007018050045032030400c803d03c20b000d130071a2040d5070003595411880442804810790290285125035540c2d03502c030b15029000b0441ca81c642000b541c01c074001c0103418a0a60004450301b16640d1040000c916580c845035014018004c180014007135840e51010300c41107041881d8024100e5250001c1e910603150520300c0800003410b1100d00c00001c3d401000140046101000703103c80310743c0c40908841c1d4aa40300d02c0810f00392031003590405c02c101c08861020701 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 977340629 1250 977339379 977339383
    0x70203010b0a0b0f0f090d030f0e0103050c0301170307020d0b0f0a020307080609040822091107020a0501140705070b07060501080102431b061b03080703060e1305 71
    0x102141c100c890340000c5041ca07070400c12900c036911404c11908400900301008004a900761841000c0c020700b9060b5050300c9040c0a0510640c1440c0103002404540548240f1360291003400e00a409100c00c450560f07081040030209100028080103c51006208032001070b510784d6658480310380b04240d50740107420200394000000b0406442c051105005008101406500500541e44544216040b8031292120b040c207900d02c0c820411404540c50405600718001141c180e40c5404a0754012400c0200c00500031000d070480c0240300c0002d52005444108005561244004048503031504000c03925201c1d007541d880307140030242c2d4441000d80801007844010300c106803103540d00400101c8029440d290010380301c440b400c3c9030b0140e0b42c458160011744806103005e03070b00c45010000904c007250300311580715400d0074125a6031640a03141c01c1c40941d0408109070703208040341c8a0b141c0f03448040400c02901560b0660780c0380d100804840030180c0c1d138000060341c5e400c2000d42501030b55284012114420b01418018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 977341879 1250 977340629 977340641
    0xb0c0d0e03061302040504030c021e030c1e0603041e0f020915010c0308090f0708070311030703020904080715020a0302090307090510090203100902070302160806010509010b0a0c0506090307020301 86
    0x303440398001c035041040030303004441007105440c2e040ba000100c60340c841c9010368103013554000203900002030403800c5901016031254040010022011682d404003080c080040e01c00c41c1c070200d03108102c5041c1141c0f4050810760041c5401600c1003400c1012130490b41610240022412003c3d1555140304078030800707604201c03d100760000001e0540c04900c03222032002900709503010760024208140c450020741c190006010000c080b4110406036900c1c140c0d2a05203550f505004d0005031005070104034800c40614000035844112035016240b500c0a60783c40d19030010325002040d0643d40400c44e00e0b0f1060910f50584000c05948429880040c0c0700c44150060501c0d0103200c3d088880f5903440d003010310585100c8525038108403042803030056681d40e43c0c1c500d08c07401070f07449074840e617615800401c1103803c06d5000310345164101207480d2451400c5aa51036695a103220030300c503150b00610b480c030060000e22185030007403040086a0501a42450301c645d1194a02070301141c1e942d4440c1c0001c95200e0840ca420b0040e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 977343129 1250 977341879 977341907
    0x1202090d05160b120105011b05070f1d100b0d0b0904060617010b0102070909020d020a0308030f070503011404020d24090e0705030607030917070f0314070309050907090b0c0d 76
    0x840c14000f000010616804d0103010b82414060500400c00354103011200060003103601000740c940386a0340f04940c80c01c40106000d50301c42412608241a40100d074801a40d2103070388184811080d0750701c0c01480d446940d020450ba2880c0c41e4403500220515100c1c1e5410070300841c850f400007d40c1c3c9241c0211110301c41c600303550401036039040100510107607900050107400d5546040700056a0100c520000d403031541c418030b0003900403007018000414004e244000d107120744d0103c520702005640740751080b144c82c4003d000d052035003071250b0307038070039841c1002d5016103110156040300092040600382c442c20010146004880c2886070700b50144000da070b03207000c2d030b003000050140108200d42c00c20b00003e4468800400582c101541c17001c0764014010004141d600c000f0f1503201c03056542d10941041041c4200c006429404210f1140e000101c440101d8100d03088540c041da10140e00c00d041c03d00b0841c204001134000402c114a502001c5410001e61000700030b400304103c01060003600e8030030050324109086a613 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 977344379 1250 977343129 977343149
    0x705151914150a0e01090b03060606030f010e10030501022712150a1b02161202010804030f0905031b0f0301021e090301060e070503040b251202090d0516 67
    0x3031072641d0780c5001980e004040840a08050210350000c142100c41d564000040048040000940081d007079220a240c54800d0b4180c503001d969601c2802aa4881510307141a01a40e0304010040207440d407010340d821006c5101ca0001c159620344499099030018000a01501440d080340d20101c200d18614041090007540c850390a0101c0c2e41400c0c1c0c84000c071044400c8650b13105d400084550141e0313400b108902d403180003420b004819440d402550350344144400c0402c025296008905050a001c1e0410304550581d1401d400c1da40f6130f903040319000e4a82404d0307001c3c0448210041016502489849101d1443c02c0c103d4655410710000c10425948100205010f039104002400010320b00d00c91244903000c0c0e03d400b05640382d41580c04070340180300c154001060b0340000340074803008940c40b200460145000383d0020700241c031845a04500c80100c0ca039580301842c0546405146103018042c881d4241c110903100500300061480892286010404225410f070480324240d00108040c1b42054081d01c1e2041c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 977345629 1250 977344379 977344391
    0x1803340608401b450213030b0a05010f09090201180b070506101214071206020309010c14030a2406021e0109051b210c0a09090b07031107051519 63
    0x445050281120304440c801348440200226209000351220620102000e04550b00c92010341d40240c03182c00340c001140c0c0550070501090000c6001d000c0c440c142c811903170300714400a20707000805004082c003100403814002804584100d0b2030741030a484000b030002c000410340d034000a10300541009001000c0102c440700d040c400b405150303c2c0102400c20740d80d00403201300c460209002507914022580c1d2141c5108100784a45800300842500a1401b132070442000340300d41010058155840c500c4000742d00700703004080c07001070144c0340d041d0014294050908100b4a240206002407050390700b02d5041000036030300c0301440d00f400c28118501d000c0c40f0340452008101104075580d49030b03143e99000c00d6545020f110242a0080c940d80d881c24a48401d001c0c00040006c09140c040e200d0704d4810002c200c1c0e00c200798580c00003c02c40f1141c002e281001d0b071301805031280c554403400c041d0000d114031402c1d034550f51021700c40c010000c2d0080040381c00c00350320040845c40d01d00d0040745500d00100808080d199040c1006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 977346879 1250 977345629 977345669
    0x30711104508210f0d1b080915060402090d082a06011206060e090c010905040b090a020c0a30141803340608401b 50
    0x11880031183c002c903958012942001e03000324900b03070143c0d280c01c010440b800900e2900d1008254028242c0c92000090703100c0611034103c2c192524501142e0b01007090304018240c24041d560b4884940d40301d00b000740018285001440070031104040c8141c02c843d1100e0014580d124070710001202c040e160780d03808049842d22690000e65443d4001881a01415a121344561040000c16040000a090f21030b0048085141449450366944410703902070f40800e92000010031a414a030255400341d80010b400104030b43c4900d00510029484a12072042d1400350482c5880016009202201c1151240341d140840b051020b07220381e40b943e81d20010809002d01c1c281d0081000359240d0681e2088286149062403030b806c604042070030041d40840c801180c10039074030f0f1450f1208581c0c20203040301072644101854181c5502094588000c01c0c1e92929522244141c0810144040401026851038501c0181440c400c4002c0902000807030800c00c4074200b440c01650a01c0111209071280104680040400000e00300303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 977348129 1250 977346879 977346883
    0x90c050a0501050703110a2108010602070b04030f0f020301060e04110d030e090a06030b010602010911030115270213060206091b01030e0a1a1008030711104508 70
    0x10341d0008040c800d075015901040c890500410f24840e800c40c8c480d040d245e4194480c035400400019100300810b01020000c59110710000b403c5041e41d8528250514045c11911500c040d0768820000311400d0110f28000001a01d00380218001003038071642d050103904041c9842c1a040c140000b62500900b504450364020a41c842c06031802d440741a00c001d403068a4542c00380c000342003642c0000c0c240001d0f034400042c40e50b60540c40480d0b464040d000c5500059001420075081c2d0300480d500e28000500203905000c2441b0711000d0b4038813241c5481a080c0f4950885210034180d0300440c0c0c521043c9100c810040004035010f000c1c007540500f01e80003414081c401506c00300c04510007161894109036640b4050707090394404000e103c540380d4224070b4156010f4045c1100d451406403c8a80c41001c4940f0400000c2003170000040e02c07110b076070000649ca4200811414020150b0020311081c04100c00e80e0184940c0300c07102e40454408040029922405000030301201c0f00d2003d425040303602c04140c400c010031031b035440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 977349379 1250 977348129 977348137
    0x10206040f050f0d020f01060807050a0b2203030f080c0319050705041706060328060f0605041e110711100c140a0c09060b0d0c0201020d090303090c050a050105 70
    0xc0607036962400d903924107100c2d03c0e02c40b410b24a400e80c0e00c1a40703580092030b40c0000d0151800800032000780b02007616095a65250304c035501c02c840d00302143c40f009002c06842c5801400c2c810700c520b0030603100b10310418013902a11445502c1036000c81c402c1413102140603445031641340e0010b50403190900d981444d0348142040e041c04500e1080c41c3d0ba4440102d21081d00c544115402094403411a4007400e181c0115180c445200795051880b80c071408a000d40e1881c8030b820645110202c6520a0640018584809024141b0001000d40d4180d071484c000c502c56480d44141c0841030a102c400340b104a026540e40b0080301d030815000c0d40115810300210001400b00840c03000151025500040052440034064803c0713900383c04028601c1c0f812400410343c030440010300380716050042d044040d50700ea803100d881003255540c3c001e01c0680ca408022600c03881c1d01a810038081070701140300052601c1c8980c014581104e049440490001c2c1c0c44540110500244200000103010304a41441c6220301e482d00203403403441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 977350629 1250 977349379 977349383
    0xb060703030903210f05070903050a03121b050703020f010b030c0d02040f09051b0609010503041101090b2718190207060c0504151e0c0602130609150e01020604 70
    0xb03220811001018424180141d04110f10110102c001210a103001c0103407000c844c0d0000a0744c42c210010704451f228100d03030300450740c010001d8007902000b51021141c207a0b0603e00b4542c0c454480b185007011074200300c610071020b07034155981754903003005150007410040300c280144400e03814082c1000c071030303030300402c500202100444264002c4101480840e02401e1928080303104036150242d01014000301107154101030806415015015a410041000c40d00443c810140050b205000103400502c0402105801c8203050601c5111942d032103029400701e40c0000c102041283c01640303019071180b90207114199420007210005018100605c03660b104990041112102c24090034407880380c0b003007507030442d41116000039003031050945541003d413032a44613104684c00d82c2c9424040e4800c09102e4041091030340d0108141100d10a44580704503150fa280803003e58421b40e00b04544400c0815140440b001452180c50b0407450700d282c034800100e030032641d0a80000303000c15062140c1c60380e030b070216100ea8025 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 977351879 1250 977350629 977350631
    0x20d020c10030b031009021804170a0e09090d090b040b0f1b0f0a030f0c11040b15071101090e010303050a0c030c0501180215091f0527130b06070303 65
    0x6100035804030050310000d0011a014003640004042c00402034120002e403e000390b88024042c0c8d8901d8158030300410480b0090b110300c4c8018400d03081c8040c07110081c0341c022018070f0224900001d0700c0014018010a44003881c0913440f1004800d440c47c0c0044402004008603482c00741484e103070070403c0182e03102e41c1c0c0384200e00c2d280009050000d01e40c0711206a010070070007011115050290004c03659212038842003a804100483c05442c00c1910800c4501c00082e4040101c0ba82242c00c10b0511005e404c1074250743d680f00049890b001c1c0c0c44025040130b000040d019030380c0020700b142950005020364a01c3e411020700c0d410719400610100390401d00f08e550b00c1c0b540386010341c2801200d040403920051300d100000d219508240008241161170107401c065240201c4100040304070035101f1504601c5082c40860300500c600d50030b480200390f80802041c1880d01814180d107040c2c25103c50b410303407548800e0b468008000540c0ea100c1981003210a50740301101c142000c111107068500010103900907690010205 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 977353129 1250 977351879 977351899
    0x5060903031b0f0a0c03050114130609030302160503040315090c230d0b0610091d0c13030308040b060906010804020d1a07020304170a12112a030607020d020c 69
    0x31000802c07202c9884a0003e042d030340184e000d880c0001045541d8071050f9419820300d8000b445010401c13040500030406012700d100c00c01510790301c190207045211030030390900d9802d200800340709000d030030b116203181e1003200590794a608600c0c0218500000c071000801152411241e007001500144608098613114030040c824541070907040d0a50413204022180c20243e0908840308010030010304c0d50088108a4401c140b04034440001c842c03100c160b104624008412008800400803030f206c4041d08519006a62460408200c0d51900b0031130301c651003100003603220000c110520801c042601c2d00000e003101c08050a0601c0c02c0002c3c06000c0241c40030740b0542d200d071290820030003400d28035520104070243c4074026140405c4041c2d101d40282c4120f40141100521900010070045070034400583d0002c0756412002004108480040303041c2c15100141c41846a14800d07501414580e0311012084607240d07422050210505040010181c500800d662200700510007a580105c0d07041c0002d0300a4642d0050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 977354379 1250 977353129 977353177
    0x22060b2d1813020708122a03182104030506010b07020906091e04050706020d0206091902061b160803090306070f2604030801060212030c07080724060506090303 70
    0x74443d00c4d9001300b2080001403004a81690071424500c03030403d074000ca180e02e20780301d1100a00ca0380140c110039034111080000891076000d42c40d007081c3c1505003400b22222030906911148074130a0700304c50081140c00121f410400c02608000603409070010788221030500340c1550204180403006400e03035100c0c08110340050070f010844d440b59010b031101c01490400e2400c007400c05640b900a60f0103000014050038403011142130000805602800800d0b000b044401c08242248038181d5010000300c0c0c0c00107040160310180f01c800d8510104841d5480c01614103512501c203005000e240a40c40745140c0d030401d10440079203590200d441980040217050100c14080300303a0b030850f00c3c1103822003080011429600080020392038080000d00c2544640c40d103541a07600d541083e40c1e42c041c1c94200c50001041080081c0b80d030340010b405000c0c1d4901c1018000d041c07110507955559507407541c84800c0c030890409003000203c0c0b1524060040104801d0b51310302e18000040c80425100c1c45040508407107000e62800150f1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 977355629 1250 977354379 977354381
    0x40e1003032a2a0503160509090f1f0b0411070b060402090a03050303090d180311130507110715022d011e0c08010522060b2d1813 57
    0x2140b41c2e00400c4090500f840500f020940100d00d40c81c00d950303210600e40802c56090005400381040c46c140030400010385810208200000000e0040e5038600035000c00412500c41040400e8400c1010076001d2821b01c1c1c0102110200d6040300a01880740d814a80751a01522424046030221504108101403c0d69602d02280280c03161401243e0401c03605180001400340100c05140650f040e1001e9544600c04d0712000c94900c481106e001405090440c02000011001031711400d201402601403400403120601c41c00403210112050808070318014000200b1840622959001d0f041740310b807030190700c2ea9804000b0b50b00c0b601c0c0c15111220103448401c0c601d41c0070000c900c0d03010061214000b4010340c0c10a800e007003541d0081c00c0032520a01e0402c0f1141c40d9040c0540b000c541a00e9020740380d840c42100f503c604140b200f01e0301e130740202c0044d80c0e01800326041060100600d6001c4045c244500300c00a146d407042e400d03e00313481a242c81c3c0d00d400c1c09800b0343c503c5500032800f5030b100304503070382508030300e007144910 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 977356879 1250 977355629 977355707
    0x1b05030703200f04210210050703020c0306010e090f0708120a03020c010504060c11030403030e0d030302070204110a021006080a08090a080106060903060b030a44040e100303 76
    0x207030800b400441c1c07455480c11414000c00980315088061500481c1d5110070008000522200030750044600c1c0104241e248100041c0894502070310489101c0701148000c02d04040b002e80140c0003903800b034801c001d2440c0c402c03c0800c14820551005121040c540320710642c0701c0e00c0031298984071080c0005e40c2c02d8030912940649284200e118000c01550400d850020002c103071840da00030100d0f070003a032104140400803058030101c3e50140c803080202d201c00f200704144280e450104800789035083c099040543c480b4131a0a040c0680340120035900e41400314042e00c1e0600e14070040416600340b05043c00007110110741403041503804042d10303407250700120001d50b000d40c4a8026003e10342c0b800d0400120716900c0b280010840340100c2040000c00d05030001d00d502d13484507100c0035188130b0b080d101c012402d08200c210030050741045404409840f0303000d2140c0c0c017143c80c01044c03801640d40c082024070030603426880c02904038145a4a40540a285641c007801854101000040030414100c0d42d20310324204035180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 977358129 1250 977356879 977356931
    0x30a090620061e0c0c03160305040b120402131808090a0312090f050915010e030106090c080a1a09010902130e0405010f0e010b131a030a05070303031b05030703 70
    0x950360340c0c6051801d41002154603074440f01c1514480c4003003040d41d0f26680c201c40d54408840f01039840c1010b4800c07118103c0140203001c0f8200442004005805051200030300922440306d54500824200741c01008001451400041c1d07046103006040e00110300301c0d800d44001181e100c402c50380c03a52207250008104001d65400034140c0074a200c4285840e0b51b0004400081e03a00d00e0509890103038584040c8803800d00c048440d5641032650312000700c003d41c0500346d641c00780d01c0000d00214046855003108400e80b4940e482030070201e82d0320b00a001308080c40d400b40912a544c0d65404035007002c900300001307601d044180b041d5078444da400030701d4119201c8a44512030240200d800c01d81c2d070303504152410500070181c0c2a24054a549031400c14046072206000391400400020318059414503202042002444100f007900f405031035103607524141da00d043c041402c07502e00560150590364590706001d41981c032401ca0f00801b6072000d099401c84950802d0070703240c101c401450006210b1102c0b0001490051355414031f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 977359379 1250 977358129 977358133
    0xc0d050c091003050712080d020d0603080d02070218090601030201120e01090b0402100306060f0f050c012c010c08070c03030e070e0a0614060d051902030903041403030a090620 77
    0x1c100240c2c0311080504201d0340b180c02181c420076542d18003803a0b40440c40c03c009112131002c006154824503175401402522001ca640000d1041e41c03640c5c0c03886590b10041d6020748107070300070440600303510781000207400d200d075174090740e0100e85080191607417502c2e81404000e05018891418603c40201603211102407a1228000c00c42c401072420702280c0c010080b50304a1185820340f00c010b40c0240720f8010241100c85540b01d91034000d41d80e41040e10074505500030003081060504c0386444c401000d001e9500007102c2000264259221030208411103042c0282c18403075681008103c12038035038031038001540040c0b2840d02000c03601081c40c080b4040d01c281c51440f000c4e40704103100850a0f40b0400b011070700455840000704801940c9502104901c08441c0400354002c006001c0007501d002150056039000c1c1c80010254410b80c1c8000040d000c0340c1040d203200354075501c00b203000e018100c940c03d80c462114504400460908415250090030182c460041c00c0401221404a00840b4500c0700142038000034501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 977360629 1250 977359379 977359381
    0x30d0908040e0f16020a020307050105161a07020d09270204170d08101404090503160c0501022a0f040231120c06051813020307021e0c0d050c09 63
    0x1003c220300e030302c2a034000441400b00040d0110090000811181c00c40e17010b0094080503140c640150b9103900040011034a10441c4010500000e0043c14210344194030a100304a03907040800d0002d151503542c04d03c0005200809000b800b01d4004041590b24940d501c290034030400402d881800040d00555100e030b440422400b640180d500310100380c0d202070356600e9a402a541d07030383c00300030403c07a4074a1062402c446d0000340c41c0105070801d900b20000ca039005500b180d00d0701c002805080194094294169204801e1038414441d541c2e060210000c90300c44982da444180c4041001d500080d4840d01d6020321424290391b83c4a510784954050354644d1a10f000d10901c0f01c841c89914106100c0014050001803012085c0800c1780c0d03490007501c490140d0064150328000d070a1030010743c2c01e40d000754801440708180e000708070700036503812003003980c1017080140140e11390401200c0030b0b1506002c00181350002c03000082ca2900c40c0e100003204851110119241100e81405040490a011642c0942908141800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 977361879 1250 977360629 977360641
    0x21308030721170921031603021c18050304121a04081603090312050c1903120b2101020a0909110703032307020106060909060503030d0908040e 63
    0x88080c003069402044282c28001030452401c018488503181c090104007402aa85502001e6190365640040390700200c6801c0040c050303c04500901c540c840114902001041000300034000a0090040d01035090550512a1880420b0a080e00444445d4a040d80d204411404203007003032442c0f024940c000003a60740d00c0d92111010030101c80301140681b074594440c0c00d0340c0ac03c4401c1b10507080c0b040380c000840c01e04280c514100c01004100b01a025410802c5e660008404240f80b02c9007a540d450303450321295a10910001042d00b00307418030301500c2903040000e40d140042500720207000b43e10b043c1349c0400542000c48100003900414481d03007950718040e00c51140c05106005500030001006152200313001180d50b10821300680e020100013803201d200502c041030009002e40c0110007401d49980f41010500e0b4020303100c20b40c2d010104e0350940180e450348020090540c0109041c8054007104109210b09400c00010030341e2031041b1203400c03003015540d02c240800d00c02c0650075100907102c1590b141400341031030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 977363129 1250 977361879 977361883
    0x60c171207050a1112030708090a0b010b07210f180b0408010608160b0403060207020f040c080411060c031819060e0a170606100e0409260301030b19021308 68
    0x10070120f02160070080f92020302c0200140e0f4441c00c8048030540c0b80345554140b411643c406010700811514031880031071800040d01c40b040d0501802c2c0100005481e0851402d100c1c0c44001c0c810f0041881e08001680c0d01d2100c0d0384000601070150305070038140e1050b290f85d01440c5061000b0343c0b20003900000490042000c1e03c042d08070b20210345c403882c100e410780400d25080301901c1d80306114441c03c0700b200300401c000080a54024200550000703018000d108010000705055a00d4103009000081001007008100b0050000e01a80f00ca8103035209810071852946959aa2140310031b05015a103c01c1440358150385c4c3c1c09469414680080031075445965100e43c0902048a4848000c1c8030300304800000c940c11052003c10001d010194004080c0381d180d110500c5030301c0d41018020000c200045c0300310700c4d00e51118040c001c0700da48204420b1b0449000750340e5149000301030516070107040c04208010804204003096203900102c3c2950f109011401d030034440760003441071000410071784040b010700103410000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 977364379 1250 977363129 977363137
    0x6030819030507080a090302030909011409092a0a1a0705010b03011b1d040203010f1410020601170c18010905090106030b01090218120604140601060c17120705 70
    0x300d10040c00c021942a00a6003620703811180b460000315110005190401e058224090b0f0074040d00680c1d20b07051780d09010584040d8260440c4802c0c2c654042c0f03c42040c24100d051aa102103101c014008074010081b1440c442110418003840103200107030314550b69558000a28000e01c020b10240480e04041c1420151a4100d04015100740d46094104007107400c040c055007540c040d1048a00da60400050303401e480b4841c2030031220f0100c0b004500540e20725142c1c0d100542c06800c4c0030602d44042c61030300c05050800c401c1036004d01c0c01408440d201480c05900010303da419508000c21314001c0c044030400c46468455007682d0f440d40200d80030205c05204a213110351505880b03217540e0900c1659200000a4203032811844020314501844004022605142c1d0180c80103503a0f00070584d541c00036000004502c2c2c0d2814000105680000d400d010800400c580c41c440014803c0020340b100d0b40c941140030309074000c55003000c0c0208004035051075042e00e180c0101c80705407041030a00111402e18110080050b04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 977365629 1250 977364379 977364397
    0x906030b19090308064b06040315091e110439051b06010501030c080c18010c062307090803040918080c030706050c09061615060308 58
    0xc03072102100c00700115402004103458041d2112030150321108140145030402c0d01d1211a04040f07000300d2510b07038102e0390718072859001100c451184100c98524400d28900c16404403485550100310403c0061466414031082da842d0300d034001580d04035803d048034007004d00d00c04401079207201d99210040200b00305080c1ca01240c160340422007000c1c0481000341034580d200d820440040540126042005007000e2540c00540034544682005800b1720582c161191440d0401e407241c100200600c15542d0502c40d0404460180ca0034240340c0c2008848403d29200780051900300e1076601c0e075600407a9000344004500e0b50342c03202003040040e00310000d0400380700c0c14610407c5441c8402c004910b4040c80342c100c40040d0744074000998a010300d003104c4080101440c1501d501c800792540d2000d80030401a0002d494048104009540c1c7d4504030303c0e0603812190001c00740705900307030244000d0310b89413654421703507031107101e06d20b446042e4010ba4100036817030000c5940085540c03800d1000200400130369001820681d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 977366879 1250 977365629 977365651
    0x309010501060c031e020f0f07090b010903020d1403120a0507090b13171002040e090c1504030305180415050f060301051c150515030f0a08040b0705070906030b 70
    0x298840c002200d443c01002c4000c0d0010b0303080005c0241c1d0704070401c494000041640110b640e42c21284200381d04003035250b195000c090b08401410001d1701102d00488000c6482440c2c8060700b50b066600203415044d901e1000b4141200844000b1843c0c80c081003210200001404c0100780f51400f500e4802c0504001c807058000105800e00000f442050f0a00b5510000c0c4100f60301403905040c1280e001e200c1c214022091030600c10707000030170200700c2588020f101501009100340624034180380e03581d245c0340c110700049000308a02d450000c0300501b08002d0710280d9500d0300d441c40e44c8444050703061842420007201194428501420925031445060070317a01180c4c2d040e074160405601910401440d17010902c03420382c10800c804019811000c01b943c2514403030b81305102598160b40c8501500080b607034100d0b981d00010503000a10300462508005807400d18400600512500c08195144140350003548070302607100501040da40704016003845954013905250714200328056583c24411020241901c03c1c507504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 977368129 1250 977366879 977366881
    0xa0f18050f070b0313110d0302030903060f0705030a0c0201021306020106050a05180c0c0a08041520101e110d05090a17090f0414010e0c04060804081e070803090105 72
    0x1c030001c5020790888041e001c0043c115540d440305820403040700071084411400d16940300041b030765007401d007802c0d25010b603005507241c03400c080c14507140c0300d0091302071a042c0c0901c0e010000c500e940f241c1205d0f4030034030401c80401c4074030300da03082071780a401410030100c01380c185480041801681544908101c0300c007101c4500159580d907040c0400d000c0e00030039019150420b8000110341104190042441d030041c1c10841d070420b40c0c0e9880c0c6c60030035041a000851840c1c1040c41c1d034000c1903070140148194100300e22020200d00d000642081d81d03580c0050054442c1610f03030305c0c481548541c0e500d1800940b03018101c1401515070288200205034855400034034154074001c007103640e00e1800200d14034000d03809011080e4191140381401d1854100c0c0c0c1c00240e10841610f0150b89c95211405070340340d08440d110008100b5418245100991075000382074550406083c882081b15031f51003a8403d4202e900b1001b01a40c50401a441d2000079800d54010203141600185000401918030015441040c0c044020851 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 977369379 1250 977368129 977368153
    0x905060403030c02191a040f02090c0c0705060c1c0908032a0c09190902221d0c0111010e03030f100f0f140d05010f0c030510030206120a0f1805 63
    0x541c0c0e110005048003011001072031100d41c0c001c021580203402344010159a110650011303903034034400c46420b08001c00c04100060110010464072018020880305581410b004809943d0f44840d02c041c210601960146160159400744c00c180c40548200c10580e41e407400c91402b0120200c4010140e1005c040c14a03400000c6c0f44000319250301c118000900540c449c0d02c1c0c2e000040d900200d61228145210340c0c4002d0038005a0b101c4250425911004032122a9a0904001c450484003c0c2e03042d07542c038050040c0707100004000070604e2113800c0001d003014408020310200603801442c4078841b548040c44000103004100c907003000841d215041d18035240707030f90b41d455800c2c603540c1e42824411010065003000d001d002c024510b1744541078904019104004900707580d15181c2c2034981c6410240300b05541d0303200b0020074a40c94040c0700d50000420320f1886d1114919400704413107200d010b0b14188240102c4010030045105174110724600c82c095030085c80305088101420105607142c020407555072180100701a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 977370629 1250 977369379 977369413
    0x33b070303200106080312010936030507021008090d30090f0b0a0f020918070215091606030c0e0f0406090f050a0c0504030b06040c030905060403030c02 67
    0x1920341c5651403114500024081800000000e03094003881d54850340e004c54001c0041000c0c01c0184172030a69415030f5458002820203c43c1a005400c0c09400c40d2101c440c5018000d68000c40454400641000c0c1e040c068203040b0707000d01a00000a601c200c40641c0e191101c2d0740181124040c43c5808203507094152258010b42d1030b9031082003440503143c038003280f8100341c0e00080702030021003400e10b0740407840f8101a511241c003441c03500303011940c40410805022158449105104e21102c0340d031130440c0b41140e11800160322081c02010740d161250f0070400501840d00c28880c03c806001030500d22030791070030301190107612103c0480211146440001d03000078254400e0180d00b480208a40720b1240001d8540e00740050b1003c1500e40c66001130320b4220016944400d0320600242d02029000014076060090006059078500a0060100301d028042403010400c95403040350083d00072103001560144c000c40030390242807011070251482c01088104400c0c5509600007603150000c907800d03601140d40101c0354034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 977371879 1250 977370629 977370643
    0x191d130b0103110f030f0601060e01020f15180601090b01030c050301050d141c09090f051612091709040c03230a0605060f070c33033b 59
    0x10301031091410041021411603288141061400360510012105660129142040c4440b00b2400c990000004100f2039130702c040c0840703030724100340b01424003007000e42c400c903039601c0d851070030b040c0042c2050300810081403003145807001d114502801d443d419a59007050200420303d800f000c5d400f00f810329a90080b00d82c4207070220fa0503688002d10190105000e501d46001052414901e400235100f10700503c052102c00c1c086820f401e002ca692020025400c185455054500030658800100c1c1002c1c00d120f049180300300c00b0000020700345003850381000c000f119800600071440010308004d040c141c1d42500c0400001c020030313007010240e8081c41900c0c40014100c003224048014600c96840b000340e5003560322202c221464000d0f01c143d8001c40d600f0b0301c0c0e8000951a6020744403000403078000058040c10080011043e0004041551840c41c0c0907000b82c000b03002e440700d0194903001012220114000c0e030740c0a64029034202851145110b00000e108010030314403450481c8a494488501c6038200356640005844 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 977373129 1250 977371879 977371883
    0x40209010303120e1c12050c040506031b1c1d250f081614100c050a061109040b041a091003050f07060e0f0f0f191d13 52
    0x20100581c40e40d1421902e0401e501da11010090f29000c541820f404100003440e0407040d20b4006002c107180288001d00002c000c1107010010505100c10005440510800c0e58100e84080d10714558981d140b1051a11040b850008000c2c01c140225400502c054101c1c03040c0308409000004000d0101d5500c40c1401c2e4a81c0400400300550000503100c82001e0107a0964030300078600300040300c005440b03852102c0c04402e2604a41c00a5004c01010045000001440002480006114130610502d0800b00e6010210b018110060080e030707803424800c00100b04202d294080e004070040081884250362007400760f01c0b0300380b92841103023003010400c503030328040c490308030104454007010a48610003070074446404c00c010803002540483d50170000104d9014013440300e0343c04801010304041c5050600c058020064a80c015000c0c40002e0142c4085484201c0d030004080011102d42221a002000240000304099480510f502a900b00001c0300022018180100a215403000e00140d481071400c0058211210700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 977374379 1250 977373129 977373139
    0x204055e03121e050601140315101e020601030203120f3702151003151e09050304050a050d03080c0309070e0403050c0f0c03030a1d04151d0402 63
    0x900d000a80565001910303210005400305030820f410202d042001e440d0f01569080c2902c4400b000101c3d81d000741c1c460004110951040d007141460508008011014403115014000c50b01c80340014601034180c0b0001810f0300440c00c0e10086641000948400c1c1c20700c002c03406481031103489002c5070007a0050350341c00503913910441d00b001c500c040c404141000c25904003001c01304074210445254022144a079401c40250001c00e01c80b5049c400240301414010314074080e40b801e0b0031061002580d194100b507105040d1401c04140d0000724083c005010026214001403946022030443c20803401201600c1140c1088580c00e4000d42e945081c050000d81064008001401d584002030b0340a000c60051608500e41404442e000d94035100c03c440841c0c0280e034240d01141e4040f8212031071003000c001c001003491700000078150300400c0350042540c0b40542582c260a1198101c4a02c11494a40103a076100300c40013042031103118002c010700700d00340300503000f02c10080107010075040c440307940c81002c02e000707641c040c03c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 977375629 1250 977374379 977374561
    0x52b0e120d18030b0705031803071e1109090c2b02010f03060e07031b0306230f06031e07020c010f0e031f06090c030b0d020405 56
    0x2004407401c2c100700c280b2030321100b299040840459591411188241460780b541c6543e170801c243c82803142070590010002c01c1d030040001c440010290000ba0030387d5640802d000107003542500d0114041124008159041001035040111720716000458101d241c0083d59880d808540742c030400e031264084001407980c2914031055020055100d1025000040c0151800048090301d66002c96807521045c0c4400c0c00080e142e10354582494000b00b60540000810304040000358038140c82050503940c1041214400300c0200304215060300d0f41d4041c003c001c0d000a02e0b031581c2c3d2804030801c0315054103600d2640f280e80c500f600082e4a04d4000540c0c90135004050b114200c0032903060f030003112403c0e1100c0310550580178500819000c0c2c0144404131048180764000072881138180301200089511a025603c101810510082c0103038540e429442c0ca490340644002c9516a913828040c0c050140b01d607642c42100340b07603401080348107030798400104460400c3c2074402c040200c042c5248150b004c0c2c40d16080c0400103905 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 977376879 1250 977375629 977375653
    0xe0102040620150403090e0f0a110a090302010302030a0906050103061d0f1207060e0a0f030809030a0903122703050d05040e0a05090f0106080a0209062704052b0e12 72
    0x260560303104d03101c1e1034020078a07500d0341e0300021203850980310050a02d0f402428021218498000e034001d4000311158030b41400007598008188003110f11001e4141079001000c5110850140c00255500350410720902481d41d41b85019801400344042041034250407002c1e0400380c6802080c004800a01e00008208d4220394141c481b1051780b0201084800c55920100414405414088004003d00884442000740041d08014000d00801405200c080d0410440e800405030844540410b40e504075245001000f80d8440948000082b20b80c4180e070302d20740944800c60410400301401c1901c0c440c2c001c1e500710880d29201981c0a000e01d00070064001071b00710020721300315029803085034402c1805049a030520b042c82c015600f103a0441c3c00c550213540107983c00c48258144050380030b801c07440a032000c55484100150304442c4040410b00d5007444c2e0000400301d424808104400c11342502e05040f4040c185c825114000303c000c00d050310030130105000500b4444240303400550a4000d180802c040d05400e4145c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 977378129 1250 977376879 977376913
    0x60105040621090809010f110a0312092301060509040b0609060a033804050c09100324050708060303030a0b0a0e0a05010509090703020102030d1d010e0102040620 71
    0x210301c09040e54009240c0b1404980058018240c4041c01046010760b0b41100c3c90004000e4045e810044080c03100010810300300c01720014000c05001d400d840c1c203502c581c582d03a04150207001030b4103010380310b40c603440c2040c8501003400d002c44450041d841b00030083d0316070f01c206010100d04100e40162920340301900252443c01c020003081c9d0b0044004000d114070315141d03640c4143c2006003009c040502035a1400103a9000000d0342c800c20540c3d031301094820b25280543e500c0b541c03204401c090900030844803010803c0781001c4000c500103141c1c0305071000d866141c80d105c4100024424486405081e0414001c145c0f541e024903055800780c80040c010f50319568408403010040c000c0d1011080c0c0090400000040c5c4041c4401c846000e941d410350b0126040d45880104003201c20b01506820264001d52001c0005030b03000021031712007209110000c5207040103c20044440e11229003043e4a0313500f480f9519240c0d40d810360081c8280c0d0f81d1502c07081c694244140c00400c4408520f01090314607800410172060403404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 977379379 1250 977378129 977378147
    0x60a050a020c06010e0a0605040b0d12050f040603020a081f15050702040f0f0b030f1f0905030c070501030c0311030112211106010506070b06010f0302090402040e040c0506030601050406 81
    0x14440152070091000c51043c80d00c402640b0800104030310b50248080c1c0002809281c0051600320307018054a030b40c1d600080e01001c0301840040074445100e070403d003414028403d4808080e490819162503903542c1c00040c0196204e841d042c400124020300054030350154001340c81e0740c1c4103070010f1621203d003414010000c2c1c40400404e01c06010040c00181c0c0144d4550080c80c40580d0f0140300401c005010007100810f450a00182c140300303812140c90584010000550140d40c11514001c010b000500071410500134450b42d1409400b50000240a49245400207214401c0f00c5080c0da0801001800a4040342210f05c6107080d00c42031142040100030021070400d007a94214004e1943c10355055200e02303c5000c600c41c0d6400b0002090906d00f801c0070b03045007070000c0c50051030140d03031b80344c5818202e507544908948018909814803203080940055188246d06407510014060310440d03a843e11000780c00b200070411a004c41e0024052000842d40d810301c202a24080d00c0183c40e00c600b0709082c044140e54403c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 977380629 1250 977379379 977379391
    0x32105041503150902041e150203221a180907090e09011103040b010f091a190305030a030209030c030c0607150b03030703121503030206061201061d060120060a05 71
    0x90100401d00c2e48485c03005000a21345200b201040e0a84015149400401580a0540c82c185800c0c0d0418140d0088101c80c0501e0350340c0a8094140c0c08081900f0f034601039500005510300040c1e40b00d89240c5078100040101d1072070110364504814800c010084e1041044034644002892400b0410402e419407545580201c0017400124680c4408450120749810480781650303221600c4004206160200891801420103054248118482000d842c1104c1d9403000143c2d0184854203001305400e54040da9a8025607405000d0ba0741c1c8042c1d60300014080d400c200702c1c45d8440e02802c43c031007659160000b400b000100025104c40d0034080c854592400e2440c2000e12010a651030308090720407654144010f05540b840b9403614024013880b8441082160191141d08030303068581002031000c40c2d000905e840c1e110310100c5800646c081341c1075042d805046254403420382040103111055904810304e856034401d260a907595a001400421150b100c084c180d0408480c0350014000310f0034a01054220035070001d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 977381879 1250 977380629 977380661
    0x61b09010f02031e1209030930010f0b0f030a02090a0507020a0614070806040203040b0f060102030d020c151003080a0c113c0a0e100f032105041503 65
    0x3008420840da030001004244e5080c900c2c0041c4c00480d4580500039150424080c0340154181034200c000f0500407003e403014124502c2c8180090b00c14201c1e50003003000c1e0f054540d8001d002c06010b4004646c0a4110700c02d0031841a085110910481c0c1000284402c00a070004c0500c0c0e181d864030141d50700201303405881c1c00118001c2214440204103103014400000502800e800e1991030242002013030b00d24003811091040d8010000d100115068190080c1c121585198040c002d4542200503031451140300940d00e800713800072521503403501c40801c0400344c0100152910240d40d490540600d03200341a0b000040034100700744541e040842c400c0d101840d106110700d0441c0482c2e030316440026083c201c440074900c800041001000034106440d00c5440c130401000903c41054000f110019002012600901c42c80c8406400003844103820017403004000d0400340101907201c0c3e100c2c2010f45880303111801d1700501d40581c0c0851411340c1d2268045400300c2c2c01032410201141e8540c6c008601400c02d007a440c0301c0d00303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 977383129 1250 977381879 977381887
    0x501080f0c032a21010c0f020c0f030304050d0b040209090a051b06090901080f10020406050d05060a030b07050c010e031215011106070917280c081b03061b09010f0203 73
    0x2a1540c3e503441c02c0c5111041941d050144e064a92142520b00c42c4001404010300c2e0b4404041e4a40c00080b6820300710011144a8030003003201d000f0074594041c603400a6408404045c0c0c80041c0084180c4450089000f07547e071418a564844425a69000e0104028400c0c0d01c40d01c01564524608003812030b40d4030b0000d14484c03401c110000010302800080c3c010f07441c2c540001c1405168070380204895000150f07001c4089d0705081c035100c006486801680b10324603150740c44600003091652412441d07005540d106901065500340900010600d0308000c041d080da9600e00480f44400103400400e488900d0b00100802001c1c0da60320940340413110034ae040b05818000c096481d00d03014401404060720032086941c81c050120301c1c040646c2c06a000c4002e04d904c843e0003003441400f403840c11211020119444484110b0a143d9620f08661581110713400700e030407400b980d160290315100c0003e000e01d4051085044030030356242d506418a0340d240300c8002e500681c108000300d1400f94004d00c1d071011500010300643c3c0c24 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 977384379 1250 977383129 977383213
    0x604050913230c0a05061e13030b040c090b0a12061424060403050303010501140f070b0a0f0b010c020907020724020d050c03030604020f0d0f0501080f0c03 68
    0x81198064070314a28500210b1410001c40041068818258084a07401132031850040401c2d11441500c00501031f11030381044520225180c00115012141160f01c08100301c0d40d02d0901c1b4203010001e8030b013221444036441000901d51124064400d041000815020302c40b803800200000b12401075104442003a00d4804900816510868152103000b89440301400c81007441160701c030040072030310031601c00d500c10b10061000c02c20000544c0d040d11820301f002c0c2007000e81030440420502500c401808108000503c000402420788109406100b00c1a000d0003442c601400c50301c117a44000508038005000d0f0025400503180c01541d0603000744440c01a540c02e29100c185210f082c0e84580f0170b031150207044c2942011050345c1013240d40c43c0311243e4036003136040c100e00d425485d88902c40075040c1c0348926004240002c1c041ea40c402150305803108910200b142501c680b4207076015150901c9042e140c1e000c0d98540b4800c0c414013003541c00f81c0c0e03000240544108200c030701c4901c410800f8400c200700003100c80820f10f0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 977385629 1250 977384379 977384393
    0x406061205010c030e0a0c090b0109080304030809150708070b180102070c260a11060d1805010f0507050406120213180606090e010e040525060813020604050913 70
    0x40454060350011980141108011302560182c80c01484107620801e0746030049403c44131400c0540302c202c90082004482600121041511a08240000d00002a0000801550740c006049845040c0c03400801c203c0c1096071060f46000300c0070040d00705842080340710002144503c08c1e030f9110303803c60311707026a408013800c1d010b0032078104030b01c01c48030700c945d072070040c400b005804000158454a01c2c11544803500641446a22902c40078402030209502250440060f515682a5102049014001c20520600360000d90082110443c2591305510b010b485c0004412a0f01429114195944481d40740c18a00f20003200d10f00001810400220f50a110040c1880b01c1c0511354401000c080506040d008040c46060040750102d500883c05d100034080308201c8406926003250451350074004c5c85400d50f4440c240641040c40001c0c0041200791085901816120903000d100c0544006550384042070b07607101c1c4200143c2440410103580507006000400131403034401d825682c04101c018113544005840d50b9054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 977386879 1250 977385629 977385659
    0xc2107200309130516050f0904140415062601090204090c031e03090b0702060c0f03130f0e0a0b03070b032a03041106030612030c0a050106062303040606 67
    0x3150503000000e214480b40f4003da100305648003102c41c1002681031003000003080c801c00041010a21102055a9104d07001180a80310204000351040c400c0d0b140144203480c418400726000c98038050014070391840c404c45c80c440c0c00242c80e04040d032449559007280d81032403550030841566681e50748403003590005071280d00a08403c50300c1090704c4c00d50141180307004400c0c40c110701c50f1010703500108070301040400e91100c051011140c644164541c1e0f247c01c0d001007802d0307101d554166500780c42541e00c019200780c00013000707090070103020b05906941c940341c140c103031800100c80c0300c0d8a04084600d0302140342040154411060200c004003210351060390341c444046070360011542c0900541106088032070070016201c0700540d488403002d4032807551416070380700c1d04c140891210a602600021001600c1d40c0c03200144498450042c0c000c8030b4441c501c0f412001c0c0d80390301128080703030254241000020300901800749494001501c0307800c1e8600b6504140020001d400080c01560000c0c0c5130380002038001d020344c07101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 977388129 1250 977386879 977386937
    0xa0e0307140c010225030201121103190509010207020108180a051009120801060c060504050309030f0a060f1e0e010204090c020f070e01050d0b10030b090d080c2107 72
    0x3422034007200c0000039060003400c090b4440b0200c10380c005c1607604000e81c4842c80541c0d509090003000315905010340c4c001814186400d000150000062000c1d20240c0175041d190700d44007280621840c0d4445207450b09038020100003d0124100d503002c0303031031612407600d100780c0190700780112890303103400381c03152407419940102d42c0b0600c540e180060f4081c8a110740718640034041504100e801545050030040445504000c0603141c0c42d521404101000000c0c0129040c181c00181241c03001c03003150b00c0294aa00110394110f501c1e83c90000240048407150181000040000650301803402641c6150703c054600c414519010395400c01c03020581c82c40b0b51044040d81e140d503038020400161070f4040185008180d800155085200000400250741c43c0d050310581280e00440c21009611901480d900302e020355000107017141045020068041000120040c1044680c0e440c40100d4461251100361342c455411544444020a1354814031065010996500280d6601d803091091144220010b04807041c4918 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 977389379 1250 977388129 977388133
    0x3032e0b0d09020a33090e09070b0d1505041103040201052d0a030c3b030706052109120702010c0516140609060901110709090605190c080a0e030714 65
    0x400e411420000ca01000311030b90022035411145061100907051040b01d01c10245000c0401c400642028001e2101c1c1c002408049041a1907504a00d0242c001c4c0250041c0000c140780d338954009181d2829015615200c519051054a10741b61030300112000d610800c1044104004003a2506640e6000300448160f01200c1300c6481d00d444c03d03154000c05030b40c002d4215030b04201801e0003074100034030a2142901040c04249421351100340103220385e0290814a20b150303030305004032040001c41d00e030000000c01c48100384a91800c12001c600441d1815a0703016074201449a10000680701c0680e402001082038600504140d90100340380c3d03884c14a08010b810300202c100b0340c078281c208200619181b23400718140382120003d0070081ca030700100d900c0b8011042c545041002d407590000000c4d9080c0100c401504000e40c0a003c001d40c03a08010340585030942d0f485d501c0c080e001030b80255988152050014151681e03603604000d440340c050780360150000c68241c0c00140010005c1e100007500e448600c0c0240c0f489100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 977390629 1250 977389379 977389409
    0xb040605040614060306190f020301090f150803030601080c070f0f0201020c03070501051c0b030a0f021003050103030c020d020105040803131703040501050d0c020106031403032e0b0d09020a 83
    0x9001029200c43c0c040318001120000f0602c90a0303600424019449880b00b503448040703110301600c0d00060140c050198424910010000c035242425410504902024141c1440800c80f4801c140041201900c26903009800920110b4020361083c0c00703058000300000700b1541000f44540300d18002d0b4500369402c40319010100c841d0003c41d601030210903820b8804401a00c0e4a500c0c10002a02d10300c65540070200d0841d030803c2403d1a145030b0340c440110903038040e00b119603040322483d240c3c03104007074010305910580c40c14506011503480790040b141603d40c583d45180c0503803019403c1c8510005101800c0381031007001c0c0008140d69030100003825512040450041580b0b19181030f07204103900d1102c0558281d00200f00c10705c02c0e070742c20504540540e01c105e8400100b8800c400c070200e004007a640c000402803a5500141c2c030340c0c00c2002000d0b41c0a1451011105406e480b0380403015442d95582c0a4690780070b4a40e01d08006114240e406003000382c030134160100e00317424240d001030358012050300b00e00b03403000f4110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 977391879 1250 977390629 977390633
    0x4090c0306081f0506060c0d0203041e0f0506070f080d020403140a02181008030301060807020c0a080d0f02101401030c090c05090f130e060105041116030e0109030b04060504 76
    0x4010500144182d8000d4104a181e10070001c98030103030101c295501644500118000e9100d10b0b0449006d03204e1503040d101d5100100c80700070348030b82c030900c180144095035120b0343c1d03200c00fa80f04c1400c003102c1035007614841061500007032000a803c91801615480d046000c0000818015802451071036240c0d800166210700b1468048690070303280c4c41d8601550b205030346181c010b0315900b0248400f02c7c1016200340b1a551144076001074941d080d0005619030101000000c0c619400c401014014002c030b8003a540180005020311490401e18411418076901c00700e100c46c030301070094141ca0800716507481a40c00c135401c8107401d20143c4203020440d00e91009610010003e011021907000042c10051205200307098003210014510b0140040c80c900c10502d181950744596181c4d5040c47c240311306d0700d00a00c901100f50b00720b980c0b1110244540d600590415948007404004041195008080c003000003000070001e0720116000040b50b20900e040c410b08c10004000b1442849510380f150b8800c00d0003050a02e424 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 977393129 1250 977391879 977391881
    0xf0c0b10051905090103081309020409020d05070f0206010b1b0a0f02240904020901030e0a0b010501303b240f06220902180423030d0204090c03 63
    0x54482d07039580840c1a00280115910b1041c003038112031700f1400721511451350600049410b20300b41e00c01c541c03039440002d00155480032a005003070f4059424100f00982d5807002015504403200304085801a00100014801401c5001c003505075802c0030301e5207903502c40d0800071061901182e864155452010380072000110b01d881840c00c411400c100e5000f0380d0070748a84400e02220301500d14120b01c1103801040031445070b40b003a0b0101340d111202c0c5040341c4441000c1c0c01c148452110a0007160300045a06000001c0e079010003806d10140e100c964101c3d05a41796160380e01004010302003000550340040d421800110301c06103004000c10390000e002a00c00140c003040280381c9449214007480000069460601005141030650350011850383c96000d15601c9000145110f542a4070340f41c40300c1c0f20045081c005011952100715a1072007514042c82c00c4001c10610050240201d070000c00351207000b01c3c5010080c0c4000b041d0004403415000716810284841c282c5400c2c0d8216030031050303040350f4448a0706842649 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 977394379 1250 977393129 977393149
    0xf0303020c0f03190e010c1e0206041413020a121a03030a12060f0605040603150905010b0702210a14030d141501110c0d150204090203180114070f0c0b1005 68
    0x44e50034a40d68a4840600180a021040c80c000d4041ca8109400c01758035540a04085410341e0300419055545803500c00ba03100001020aa85000e41100017011000e88054800c41e0805c1c03100c0d894501003c80c2c011645005400b01140100403d00440088690358a04002a008200c41070b00c1d640c03800c0300c0345e104040c11588598440304107243c0f00304041110540240484043c1c882c3e500d404141840b480e000503084e244258480100316180c4400007880e1012000030b081860720840d071702040c80800744041203152780c0b9480390b03000c1c0d83c1254002c3d10004141c00c9000e00c820f070700e0381c003541d0400c420850b900b801c60341e1400284a40c0e008400410101a4425245080301d0009081a04041c5c44031050b40399a0400034900e00c0c02420718051300404e00c204541036081c60700010750150340c0c3e9030b2160441d80c0a50402d5071654004002c0d41c180b280701103c10f0041d0088501300340030058080d641d40004417243e110556000f4140100d250311180895030ba021614854020301040c49026840c140c01e114121007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 977395629 1250 977394379 977394427
    0x80708030f160c15020c070603020406110303041e0302150901060e0906131412070c0f12050d050306180708060306010906180e24041712040f0303020c0f03 68
    0x1c8200c40410982d030440040c103112500103913807505035003205102030000d224001c0081d400d40310780100010003541c590020310580701c03135a48490001c07043c05205540d038042510000d0010208040d1510f412120081182000d030003881103420b281c81c1d40b064600e4095007540d46410740d0351103103c1809500d40940c902508031f00d036100100202c1c50180c06540d206503080d2402810010417180e00420710408021307110300c54641003103155594215180c50042c44250f40309900d0780100c00c1c207000611b4210802d903500d620fa001170190200082500c01107500b64070062446034414655240e089520300040300b243c1c800c102c2038444000500304041050304d0150141c0c04403202a051200502c0680300e02d030b516028500d03c0c1c030000b140e441400c01c01207041640c2d1225080360807001900c59180700c02407009140c015409900300010350040480d11440c0d51240b12900040105110040340000d42300030103924009029140040c2082e201d01d89280c03d0001038400580c441d44042200190b40b010344050206403c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 977396879 1250 977395629 977395651
    0x50f060607030516061e06031a190c020a150c120b0a12020a080607021506061303121107120b0603030301050a0302060c16060507060b090702060a09050109080708030f 73
    0xa0000d60b0000d1151040c410755011200c02207950404101540d00000c4030084204c0c8860321030403910705080c000b80310610040e200705056403502c40a41c103000011030700404110843c43c800c41401d07441400a0f00d602c2448104610824a01c0000f040220042c940b02404965001c990924003180c010b1200c285107900b2149940385c02c03080e004590303a402d83ca20454007404400c101c1760440d4000a80d14526680c010710590150104002903c6d90200311020400040c007040d0f40c6a8403a80c050010f580a0f43d81d492080441d01801800800c0c105d81500d040b15920303107822840b80582402072420120281c1c0801c5852185000d62003c0000c440400d80d404602078000b5801c3d9854500020450311080c80301901805000a82001d8800284514200004c80c11106c401040d91110b00510f681c0c4901d006a51552500c9003840340340c0b0b4841c1d1024040c00242e030040040791151448031000305041b0400702e6656686a0201c00018a00400b0301480c0c0d008d0060742d503d070301d0a0703204001060760041c20380b0744074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 977398129 1250 977396879 977396887
    0x3030a110c153004060608060f0103030f201f0b010e0a05040b0d051606120c090b0a0e15030601031508030a0513030501090c060311040506070609050111030a050f0606 73
    0x54490442070714100c2c0300d500f054040c1c0c0d08440c40c103420419046610500c01050400c204424401c05811102c11507180c0c4045542179a12640c83c0103080000b07000040c00514281000044a8403405108481501100c50040100341728801c180ca40032441503034078452401c17403c0c2d4105041366031056410720a0b081c244840c40049000c0092041c50303450042a00c1950b58070040d607901c0d12109400380c91a9400812200a00d15408100c14220b141f1301c079050005044402d180403008680c014040c52800c00c0c2c840c80e209131b0a01e1544001500460490002c2002006030950942e450300080100b01d21800200c507500d080050004082d50318072815800a418580320802195400204032055900d043c0791131615660030b20b228912854050348054240d42c280714070034041c400058400c0741129201d880c2001800207500034000c0350700417032040030340c040c2c801d00204000c02d9607500701e0200d69229500000703686000d00e088002d1900145c0d113031200180c2d61002c0040880f01000b405400c80001c4039510b0070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 977399379 1250 977398129 977398159
    0x501140108033f130507090b01051e0f0a0914011701030803060a090603030201020c1c0921080a120b010c08040311120102030106020123090c100e03030a110c 69
    0x80422407005503024880d482e012020f100c6510b0192000c10070002041c10300c90b0610454810b01c0000e180000d403100e0183c5540018883c3c050b1007103484811043c2c450b0341c10f14205002083c02e010080408401ca0700c81040302507000e2100d10000c041200b1036890300c4803518240084c40c40300580540d981c50510044103114039811040b501d04a04507a0b01540c51541c030b64030040460998000c40d400814aa41807200200030941c040d0080d01e03070b569100044030000d056450844807000302403c1544c0102d403520000b44541d0104080c1108542420b08000d001d544550360ba014059105000f030350300041c0741030843d554480c1e081c010f406406200f46031094002c40d9945842003503100310301c0018400c504214400c88180c840c100302e11010340ca420b000319101e41e521803003e406000500d06907800425940d112031344000c1e03000c90310f9001d0b4420b1002007203c1943e13202405804040c0b10408010721034228070b04400f595041004200e041410317030ba14a100110711141c40c0c078010000d40c502e8482c009000310111 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 977400629 1250 977399379 977399407
    0x1171e3108190e03070e0403030b01030b0a12050102251b271e02180909070911040e040507030b0a0b03061b091c140d050703180b0304050114010803 65
    0xc105841d21800d1410202d110a03208100740c078103a035030107008403100000e8900c4000001845a4081d840600c2040c0780d100044040f80c001a000b9139100c24071010a000e80412a0140007d05203e400018030706200798469203030100c44101d01035401c400080840307080005120000d402a440340d04410442401d0800c04c00768841421440085824101041201500c1c1600314411181c84100d400c0c1e0040f00340055500a5800307010440d003400c10701d480c4403c5c1801c116100c1441502c000026003001c9042008660290410301003105211206000200b100030100840b2406240300e88004c154613131035850003440700c00009242040540c0b4042060415407004160503600c54000401042c1036080c9440c00e090a00480f0a502c2d0803184034480401140116110300c0403003401507490703460124043c0e0100e541d0380c0c0117800050000e4814841000006d0054081c180a02031322201a50095240c4032641ca064000b00c1e03054965a45030000c3c1b50035030344c2c1c80007080c0c090218500614600091010562 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 977401879 1250 977400629 977400637
    0x109050111070e0c071202060f07140405040c03152409050102150a150b070203070f0305100b0a17010506010e0a0b160809030303090a050606030c01171e3108 69
    0x41924020f03002440c4641d00074111681117a2110089880910003c4000c0d035800b0700311804026000c081000c5240c040c050804010341401d8990543d240c14145814031000d0041d40303050b94241515200c6010440000660786070140005000180240c031541c05505900d080541440e030030b0141c43d24052200b6640401e00f407850300800c0c80100140e894066500004110900715110b02200c0d00c1030100c2c6041c01440205840d074000c808445c149915015010080a01c502c0002c0c0241e20148428000300743c0c80e00903001d11b50005007100c50031655901240800c400a401d8908965941c0041121960b00844000030008040d665449614248480402c540c070510324410340359075214284404210380e040441e085024040c0983c1d88900344070943e0355a030000d01d030b0704030382500a54002aa041c10000b500c600400016503c4400741d0803020015901048060560814020308442200d0000e5949440a00a1200c8021400b50701e1018220340741c90186003019090200500c00c0744404121960305075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 977403129 1250 977401879 977401889
    0x40504110d031e031409060919050307020a060909141005040f020d06170f010c05160203030705120d0b0d1208090a0b010e0a060803090a090c0909021206010905011107 73
    0x1109031402820305070f07040c0c40d900f000c40540c26218041c19080c80e6040c1c00140180710009180e050070303110508a1516a0422500e4050303c0e0300003031243ea00e208001001c502e1f0240240e0a4a190000c181c0203d1440081c1d0f4208402060801d2000c01c00c031005445181e001d160f903c88101540e042108003041c910324603201d107602c19601c1e400c0350207028007503070f048801000c900c9030200038a580e9440c604504007000740c03001c1080d00420300d5140130094113000d11011203849030b550a14141c22501c410707036121281d05050382c06220600c400f40000300d080110101c105071600030b0541b10f01492585e0802d036000000514042d2018140309400070700014500d101c40c2000703007007441c241c1e03480266580c90241d0b81240074158038100d20000030a40300e4411543c3c0100703424081405030b65106c0d10000d079a4820110301a400c1200544104114881ea0b404859030065a1501d07007c01c2d070340e03000b02c00103076041101198801040c0b802805115038001c10710701c00810342030a280c07075502c80e004d4445485030022710071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 977404379 1250 977403129 977403139
    0x14060f0402040819030e0307150f1e110f01090f150902090717070e060d050a0b030703030203131406040b030405031c050f07020613080906090612041104050411 70
    0x1048000d80c0e9980540d4040e0190004907000904d942d120108003c50220068002c691202444c0e110ba0401180e080155007520240080008807041d0454600304002c42850401004e102043c404a01d6103244030013998241c0d80d907c042c010601c131060305024030886810201c0c1c5c0b4203040000090703c0340c00090500b0f070700301d000d22001c512960b01c81c1380a46140d020095201d81a00c0030411469003203142c65542011034240c0800707641c0c0d04502903906036100d542c680d9001c48103021581e040501c540180d50b10441041e800301e100020b100209140403a541c104601603040860300c01c41e0322900705d1a0380001d1001100d040d4510400c0d0300419000d1081e4040e401c21308034000001420b0110410482c2e41c00f00c10201c8040d00c400d0440c09078401404240e85a0185d20b0402012440c214400521540205015250f80007203e0440c1d03550701c015402090702a401c1141808160301659400001d0308002d07151051481e840e14003848d14100c00c603540800300388200d24100500c40030404201c0c3c0e0004059050390 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 977405629 1250 977404379 977404399
    0x9160501260a1b021b0d1104091a010b040806160c03181e080f151302030c0a0603200333120d14190c080714030405131406 54
    0x600d10010b00f901951102c1c0003440c0daa0a2030741d8941c009500070b070081c103030410040308078280001c10022448580001d0650154034140040320f240ca1f60009081c584910701442c5072502102058203480800d0f40300070048200810200001101800301c69440f44860300c09190000a400024242e80d00142c0c0140030055a0705513080102d0741c11010720050000f044080518040f0003100344040d00c07880c050701da081d00036172244824030b8600145240742c010b09000e1720350482d60703580d142284030042e0305001d9925215036100c8881588951645001070002030b9000300c0d1640e145440d800500e001c1105205c1001000c100b008403010728200d00c00700c9243c41c192407200a1030410083c0482070004d18001c0d41c01003410b160140441400078260052030120748070b03450000042c1c42c4070603c0f8064409404000e00c3c26000300c41c0142c0c450780d2082c103020301c00c0d1005818604551500565250000302080b0b0315400000c081c8121300d0701c4100c520901403404014826000200d445080a0402070441801612480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 977406879 1250 977405629 977405641
    0x6070e010c17042103020a0312110c0609010e07061403183403030503040212190327080a0605181006030b071715180916050126 56
    0x8106041c00740c02c05400d0905030080790954040d540103100d0101c980000d80b102e000d40c0e44007041d0356009aa00b40c0c02070591448680c405032124045100e1100d02e860b0741d61414040340c2800400341c001e50b0550700042c001480c218050508441d03039881e5811455111050070004554403521190851019560254480d102c140c00304c3c401c284c144070f106025001c0e000c1711400c0d8603100da11101120b01401054081d90848100301c00104215005c05000a10300708005000b40c1440700c50740b2000c00c9140d044070b00340c0440d001010380c0c109a1200c00c800040e150142100076104404010b00c7c00c80440095940903407a14511a940d00140350b4000c140f030b07442d040020321800d1100344c031003a40b0165500780c95540f5130084105000344054041200d01da40e450011450080c466400401c4020084100301a96102d050000c0e0780250112615a07105a400480d500c09071032034031041e4003580b0341744020545100d050320402580400303500705a0420400c841105803031410741403d64104501480f80c686a13440f51 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 977408129 1250 977406879 977406887
    0x60c030a0915090308100e01050f1c050a081b01020a0f0e040905060a0f0f02090a1a04051c03081e01060e0a050603070e010f03290d02130501050f011106070e01 70
    0x20301102c0e070340c0501c0d03c0075503418550802030030b92207141080344006005882d01c5040080f40d0080c040c0e69004041c1d04011031550809a000c4045030980c9440c0b401180d009540360380c5080c9404070103d80d0034502040b20840c0740c0e10b00c620049450340340c100941c00c0501800c070062580d1010300303c6104105500b0040e003a83e40b902e40c04410815040016203805181040740903001d1b040041600c040ca600d031a00c2c1c1c52101a02d40b00351a0f0401c0c0051100d9015032401d42403000c1442212000150040d04000010350755466041100c1800004a40340b48481e1090901406402000b02107003040302e038040c684405007072001030b00da0540c2c030303d410080310844d9030b036001c5410100d164010035006140081408034858003c0e00c10021203100740c0e62189050b4140c00c00b00c0c01d41740b965041c0442c840c0264030100c0c5641c00746140e855038000152450f482d400d0781c0e4000a4000c002c02e10071400d42c5580b0001800241480299000f0b850701c00c0c28101000c0c12900200381d540c40c1c0c010507800401c07040d112608201c2c0c0c46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 977409379 1250 977408129 977408153
    0xf020d06020706051f050d05060103140304120f030824190521120c060103031211120105030d03140103121403010806100518130206090301141503060c030a09 69
    0x103c4801c029a01d86213022003060428040c501c03d030540918800581485c006129040c6158080d0140144d0303440d40e62121095600080705102d1400b0510001c950780b825000d03e20490b501800e408822623a50741405404540041c18039400390846041401e20500d1905414034948010f41e411200d401c6107080031414106160040d0ba8070103004e210700341720a5030f0308002218160076034003601d0208212248146003881680e812100030781101004102280c011401040c00d881c00c0303076002c0703040c3c21030070209080d503400302c00010600c040d540300500c901c0c201040310100d40d003020306003003000300f8002150700300c07582c0140b02c002d146564640c03007900481e106d1000d030507a50411600c81620703944c540d01270545581d42101c81804c0789004500c00209450801201700c808185900c140c8400e0f103079002d00301c54420080e28142e070812000c00885071035450034400c0328515003050002d56524249500c00078100c0074000500c5110f50310410900072122800c0007203a4020381c401c0f03c0011004ca152900c41c1505107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 977410629 1250 977409379 977409383
    0xf1a27010b13050a0f09050a03050d090b07200c060924030c1b030a09140d12050418200304030c0c0303120b030d0206180304090f020c0f01090f020d060207 68
    0x82d07162a000064690f40c00490244103071081c2403141101042c1c1240444400202c042c00790341c0700c40b0101c80404c1c0140c00500d001c0b0070301c2d9401b0403480d105403514a500c480944082d00050000d00200207250b2101c024481942d4511001d042801d41010008199006480c1001c1c8103c0300c41d801515070302240c80ca00c1c40e100c09074202c85501d07440c0c9041c825202d604540003101c00319400d241034104010b004002c9071034100b590344892a0313003030071701517294480c0c05500a5990050f010340c0180c030100d007030f0361000444044156a841d030381d01e0800b608681008882081080c03c42d0402d40e1200320311140c3e541000642502e01c1030b1607229507550800b110300005102015200d211089008800e06600c28a60705000c0083c0f00b090102d06140c20603d560707280c00d8804403006801000c0070031030341264410b000280840c0c08044a040c95100d040c95000c03100c00c038001c50603250340000c007250140001e01680171818000d00081040001d551944c10002c1021070000b0b20600d0400c00072000c211181e816103005603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 977411879 1250 977410629 977410639
    0x9060d030e06211614030f161b120f02071d09031e0405010906110706030c110304080706090e0405060f10120c0f0906120209070306120f1a27010b 64
    0x700385030000104c0703505184000c00000359010030010070031702010300301c90040c2404103025035581d84070701294254064000c0810b080000141c11803041c0c01050102c00e0403240510203d040700c501c40c07000a801030405c0301c01d900c29500041410008040d400440d01d0052407103895244955550003096402d510400000d1040342d02079483c22842c098554000e4010703600c0a880d0019425129001a50f920743c0d400008001540800707820b109072440bd80120f1041021401c1591120300280900c1d0b0551300640c0000f8216480180c1c108020341e4840c1001c1d0040c050100c0c040f580b82040e846c0e45072102e2000700364680d2013400c00041005a040900c1680050005d2800d100c0001032500c0c0c40d902005c801d1245501800b5144004100483d017481054115080103c1d4205503003200d80c02c0c0600401e00500720414107035600800540c0c0b0160080b02c2404901c102d0420360610310070700d000c428200140182071038080250303040107a441c10b07407102494001c458001d84c040d075154990080e03000d08010700e0026040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 977413129 1250 977411879 977411881
    0x60e0f0703090f0834050a080c070509090703150e031605010f06030803060405010b09012a0b04030f020706031a0d0c091104031203090b0c0c100e100e0a080f18030d0e09060d030e0621 80
    0x7540d40440c444064fc1c0c4605540000c4c502002c06050960729424601c4115802c00c02c0000444409003000f95601071050307001282028151074204101e5190303601c260b03407580000003004258501849110301400410140304d062004c0400001c000c11054100d01040820301c1d100144c1495540400e503080c0780c1e00c07501c5034246150600d00244000900c840184c003500c502c0b20081621406402503165003405483c02d018101d03d00302c100002d002c2510419280420110300114804400b1302407110111000f040e0150b8903490b5141c822180e50030f01800608040c41c021507a400564042d034490380140032a00034a03110b140440c0018148540b01070103448442c40c02d415840032900206044040b06401c2004000c1076990918031516112040340c01404c0341c00030080c0e0701521131060301401c440d40010030b20000651050022a183c140600e0241c0701260b55290300300c40381e140c81400706e98010001d0b140400c5101e45541c01821040740702806500c0f45601040c0d000e603400b4601c0c1000f8060318030110103005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 977414379 1250 977413129 977413141
    0x204090c120c0906080705130b07120210150312111b0f04051b03090709050f1b180f06210604060e0f0703090f0834050a080c070509 58
    0x4805a8407038881c514148256104080c2c026500c43d4101ea5603611803a42960740e410045410360b01180d454400c80d0040c40000c10b01212450107440240c0c81030803080026401e0840181c03400e40c040306035191540c14851440c070b07440742148900381121f0740607035070f0342d00041c8580042d21140107418450009100300c0c00494038200c030280c4680c4c3c0500c0144d9410448c03e40060a020649030302320b4551200141c00e03500c188907440f81c000290341c80705a52054406194840399a10241e4905607000c2d200d540e60340c0244803651041440c54031a249060b501145030030119004165a03821210101d4410654001102100d48440045a150490041c1409940550440c2456145c03c0645032180103034948800030070342d03209040e07c00e40071741d1051040102c1aa1594411000350000d49012035140c181c7e25500d9002811003009020b100d40c1c5034100303205100350310314014840c1c18480c6001000724540228103000c00d101050b40300c601a0407400d0765507504040401603280400c1903020b0394000c6011000c1100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 977415629 1250 977414379 977414387
    0x70f0807030b060d0f0609151a07140705010e01031e0518070f140103090302150c071709040b012a05240a06050103050c040e07020c060a0f0212041d0405010204090c 72
    0x400207105c05400c00160391505580800c4684072800d00d542101c00560500154203100080503415211010052a0004a40e070300341d40940f1505a0729140e501a00c4140aa9a00b26284e98164282032900300516111841d40640c411803078184541040d0b522000300310941480003194160f050080112810143c2d1800c07005006e8160748164034090706040e41c0b00840350300c680580610907401d0341c020030f00740c0c05110034150030800c0508400408030b01000114006850121308000310b901d262001c80d101c01c1440184020b440c01d00c42e856040004110107800b001d46a0000e5000240400c4034840da1100d00b072401a04e003100404810860010b0070311b046a0b003141d0000783d1845a801040144032080c0d030380c80190243c0d2403d4a00340b50f007007424041844007241d0103280c560309c98003030300c12624a000d082011609a9100d503080300002040f400040c11b030310307070104440a405614001000d240c9031400149501d0880600072414500c5c10010104092203401d4041da80070b00b00d41517040014184490000d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 977416879 1250 977415629 977415641
    0xa1e02030a030b0d0c030b1305011a030f150c21280207020105030705030a09470606090303220311060c060402011b0c0b0a0305010b03070f0807030b060d 67
    0x10000380c20026144410b040201c9441001a40a101d1781c56042c21550ba1206c43d4100500c05004542c0c0c4ca03d0541c00308400340103002d08800c600c5a4600c24000c1c68062508040303040c04d07002d0f901c2d40007041c44410b8007084041c80c0c0c5c1c030600c00c00750b2907184d624080c4c0240902920111901004603a081808802c07039848002c51503a008028205444c50700e00c00040090b8020f01102a011a00c24000209080d000e4401168010007510000030400e0381ca9079a8508000e019002296800f42d046001c00580354241507417104180040c18541c90242c003510f0b17281041c10091074240900004100035010303071410419035004c0c0308202c8401f00985220003c0070310407821b030302c4190340e141d0b00a035004407103081800c100d40c03045100364082c19041c1d440303400549070404404540c0d41f4521000d0b1105000c01d076100d01c580c2c040c1842031350250f625044088018159403068020040510b020000d003e0815040f5000100d114814208003080390356815041d001407403512211030304001c0c00940c83c42007400960100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 977418129 1250 977416879 977416897
    0x170a170f07140c1c0201030207020f04020a170c131502010212090a031407082b1a0a0905010609090917030c0a020d0f17090a06021207080912040b0a1e0203 68
    0x881050b0002400c1290b07207045454401e804c4a40c0c0034010002d035100c1d400400d00280040c110b0300d0380080950118040b6409507440b0b200049202d802030140303c00481b07903290070a8111102c0c50820a00c007141120381c1c1340505c2003100250311030b400071440c24002c0d01590415007484403107510924040e540d040d1a0420701504400052070080c0c000840c1190781c4c02c0d070362201d4100b8015420409803c41034402121003003100c1d00f00c1142e842d000030041459001d0491180c4500d40307d4001400c6040500c45038402d280c2010a0642c200b43c014800150b0180380300084031ba0740307070010801a8240c10302c260780314440d0070869030b220000002c1041c9405002c0042c03d10142c0769084070f14618800c44219040406200c002000405401c40e00200406522105403c000d00d43e00381c0b6152076180c2c0e603002c100d921240900422030120710400c000d40d07810001039680010300c0005441e074002005069100c511490180354075501c00414071085ca00d10804c81e00340598022a02441c4403103294401940d242c200e0655 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 977419379 1250 977418129 977418133
    0x70815101d060a0b0a030c08010e09120d0f06140111060702060c07030e04050f1803090f1e030a051f0207050c010342170a170f0714 58
    0x81250030a210500c0411101103040d9035950107000e100315051850041c0a080d40510b8880700031074200d5141000344040c49040d02e0002e40c1c019480e20240c54010160300040821040700100480c6400110b40351402845251526944403800149240100b9510071280b90301130ce4404085080e0442c0400d050090f84242c0f18a500360150407540b42c0d9404c0100d82110041c1c01c03500c08122401d01c0d65000c1c095071442400c00342c02c540010400b1404173383c8211180c2c41103507261800e00032034419a8412640c08000d600240d0310b401d806401003100180c060900c580100c025070b40c1c41012501103101400030740030040988081c4082410050b90324043c110241c0c820440d00c5000d004e000380c06108542c0c001d036012024000c041c01e058010347c0103042c00d15150011601d40b51410070044201060515010080240d03901e103141a43d400d00110241e0b504042c6881d2503803280700910075000952552050b03404020b0300740c96805400047e0290007450000c0600c0794011505d44100000c2000039076803d411542 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 977420629 1250 977419379 977419381
    0xf0a020d260f0d18020f09070c150b1c0c060822032d320d0c0e0a05010509040506030f10091b0617060d0206160b0a0e0c04020c0a05070815 61
    0x24001c3d140850b80d004c000e510000c000441151418450b1484d98003c2c5170303007010342d0b8804594580c100641c00300218080b195075250703c0034106180920850702180c88c0c0303600d01d0307068100e96600c510104580c1d00500080c00b01c0c01000030310303151001d845a940b12000c01c0085202249030324001e42004540c200c19404003a0180c0c0d820b01c8040304900a05540076144d82d146030001119049a650400c8120043c40780e180b001141c141454280d03000340424212640e000450b01e901036001450007840840580c071840c4424820030141e80d00105170b840c0d01800300c800050580322100000d00d03041907100e05000c24000d44c4500500810b06a02042005006808040b00014200e80f00c2440a0303075030240e5004203201a01c81100c80c5d40402d0078580c007003000740c0034445c1e031581d030b4000030400d41220b030074008540d10780b500200030400800c240c1134010407100030a00100c2c1c05015456121071407103044034051030740440c0e6250410020070a42052b00d400c81c040c0d554260312000010740b2402241d07489214010014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 977421879 1250 977420629 977420651
    0x608070e0a0b0a081e13031101060e2e050d060e010b150904060801060614180a03060912182709080c0f2b020c03120a020f0a020d260f0d 60
    0x4161180d0f2801e071b490040e00c0002d59042d180310080020b0b1035070315903031084080340150350094214000d0920508083c03000e484c030b801441004070000c080060300350300b200c4100915155240c4007441c0c41d41c0302d6004030342008404000d030f0050944038800c0350b11520b02d0001c0100383e03010030300034150110151010f002c1103031510880380c20389240b0f01c106800925501c10b14600c2074035160251071841c3c1111502003010341e910b800582500c00503041517401d0740e911000e00d410815400318024a182c01c1e810230300c0110400070280e08003040940f0034605407000885800203220803ca00b44a00a0344110702040081854100030429030000380b503801652041d0301c40c02109540c001805081d03404001000c103903088003800c0340c0444038020380d0104c0641c07042a12440d4980c2e000c6c490f113806003090b501d03400d80b902e48040000b403078400c1106811546801050380c0501603205c1889206840d50081042c00c940740358002d030000e030781c2c0d2500710034035002038041400c3c026056040004c20780c00c007800e03000380010105070f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 977423129 1250 977421879 977421931
    0xb0a090608060f0402030724030c08040b010510020705121005070503010f180207060c0206040516050312030c0702030a1b0e15041a040e0a120302040608070e0a0b0a08 73
    0x98081c0c08001c0c0d1195001078043c0241c008056800303440035095845190351004001100308103060f64550901651079000800b03981840b8000494146281001040c01c054403a06d2450744e040c01505d000300041030385181054003c02640004206c090880c50a000c020300d030071929006c110002c03250b2241004085061a441070b0142d905030b03080c804906040c00d1401100001c0d40c8200031080c03000d00d8080c8407150100e07509100b00c0101d240150040c107058907080c40c0c038a04299904040c03020384510741e00184400d4800181c0e00c0c1701801c0001c0900c2d5661505488031445005020000754136210b482100c2c0300700030090b0080c0e2074a04844501240554072030310320811000e011240e0a40394000c0010141c80c0b0b2403e90003201c008035011031010700c07054040303010406840214810b0f580503480300700130340108540000700c0c1c14502001d1808500b041e0034424001d00441d405031000c401c1255007020701400742e444401c0500140b0b01c100002d95110360003980640120000c4a0026045402d10036000030040d0f4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 977424379 1250 977423129 977423141
    0x907180b1b03190e0301090f030c060f05160e1c0c030b07056603030609060d05100f050609100503030d1d030403081c09020a15051c0b0a09 61
    0xd03d10081c040340c040d24120340804880070040d40c15034070b411000d00072405e1200301c50329840c029a1000e0031444181404e00c01d0707550030540540b14600d402d041106020540640c956425428030b4140950500a40000c0c03000b040062800c1c058020f2103050420003a040a401044921405003098a99a243c409507054043c003542841d80640102d04052a241080c0d0044598402d50400702c140f8980c5208100030b06814041450718580381d41780c86891101c440d25000c5117211084c004600d186450f001103400b080014060500544010941d50308120f8180904c40e90120100c03410458a134212514401800041c0c403c5400385081c540421100510441c108050300e001038001d42c51702010200c150024015070901d07000c1454407940034202e203001400100005c41c080d0b2122526074040c5c8000c000c11100d000c2400038114030f481d51480060300c03513042d00b0341202c04811a4140e2522030501c281c410388244510244582d002611481c803008050b40007910754001a506150f5660715210440e0444070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 977425629 1250 977424379 977424397
    0x140618010501030c0b0a03150b04061b0c0909020a0e0403080711030721090807090c020705120a03031a060c1b011107181104181107020f0907180b1b03 66
    0x700a00117000003039024000f44540c00d0249800204080d54441058104009800c9405074400c005420000298070004840740300b8104248200081103980d200384d4260414420342d606180c80d0300001040d580d5080403040200b4081941c0440c2e441c1615000706280c000f00d41410100702030382c098610f60030b00002500c1c000d0754006015180c0c0b00c0408200142d45409030810004c0244402010810240030f01105008100d1000d01042486a0b03040190400c06603401c01409070540741e003034402403400040c15852036a05800c0c0090480d0a0b10781e500101030181c1c1086d42c005034005000c1e020b007500081c4074080407129403a00ca41030404100111103070060040c0740140755002403414000159010400403024100f9800007450041d8440840c1945d00070340d0240c24044c044032010601400140200b1420b0040d010059252540c030380c3c00250b075030104c41e002d035024003101d1000404d602c0c01400f500316011207004800e04e100d5900c030720001c4c40398061400c01444003101040e1255811000060b910040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 977426879 1250 977425629 977425643
    0x70c02030601120f03120615020105160c120806030a02090906060102010e1204030212100c1806090612050601031e0204031b05091f09020f030a0b0a0503030a0e06040314061801050103 80
    0x1301c0140c80803260300080c03600001307000e907480744d00041051200000111504142c4c0000c1650715080070a0024106d20010080503c000d64500800050005013001c84501e400e050181c0300351240c0c4013103450f01c48030701c070000e40043e568003d111261000048081c881c000c240c0c02070101d0100950354681701e80c2d0003540025000b8050205200602d041303504081c001e60b41c11b00700c3d03180c83d00c410344220642d1216011440414449070101c0903005000160402610361810952021131601d80c006080e00096040b514265a444010604c683e12a80042c0b04a41e486031413603280d001c02108080c002d44c0903120480311880e89013440410f01146500c42d00840344000c090f90655543c0350200c15590b071000400c3c18000c9001e810101d01010544040e0096140c0079039266124030f491460602140c0d242c82c2c469210b46103901c420056550000101c1759088140c2c549407004d41c0725a4086201d50050b0f800081078001c0c940102c901211001030442d12440c001c008020003810155244c03400c807802804068060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 977428129 1250 977426879 977426903
    0xf030d0509150c01050f010f0b07050706120b0411181e0f030a060906060f0b0726090a0e071808060c0319051e091504060c17070c0203060112 62
    0x7032a0010150360614882c0005602c1c2c1200100741d142165011610030b030303142c0c1d60b04006000f001c95851101e4043c01c01d00c0d005501c0e00069031600b5a89501d03920a20042000000c4924400390f03082e0440c00b40b6040c0078009204c1624554880305c0e484c2c110b82c1043c2c0c031804030003801c00301d00e28207004072540a075040410f4900c086941418801c840d182083c0c8181c152081c4503a006c00541544180040240102800141c4a04003d005141040e10f5170002002542c00c0c4003040115162a48116004410b400503034420b510143d1007402c2401800492030b400b40c581000001d0072111050340d240b2800013503403104084000c2d005806818403040c05402d01c01d0344008005905020102c008507000a10079000340201c4480c440303010143c5d0000c50351044d91210312002062004640c0d044540c00858042c00782201040c00c42c2901c5d00c81d80001d01c0a041e00d611900c808100c0c0c5e001d032030304c02c48500705203c41c0403851411040141c41541c4940089009100315400001d14281c030344400c54200740d00a81914603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 977429379 1250 977428129 977428147
    0xd090e090a11090601020115030c150c0302030a0c03020c06040803041a0a0804060c0302040e0703020904050a0e0c220e0706110c01050d09110a14030f0a03080c030702010e0a110f030d05 81
    0x203903e400a050ba0b05541d03960070040a40000e42c8c6401c002581300380b08940b100c5007081028070400705061201418404c42c003843c10b00090300030094031190403031843d145202c91301070b0908030320f802d00744031031035800c090000303400300b04070801100510a071081d0b0f000c50000700b1000e10b01098280324501015002540140c04540002c2c4160052300381c0c0902464003605003034441c540c0e520389038026a44540402d500162949581c01d081c010968494203d000400c442e0144402c0e140e00c40e580150510b1040030030b625944100149155201e6007800c940804000c0c20a02c01302542d07641c1050700801d00800c0180e0340d0f640366414000740603410600306941c0c040c14104031650000141402040446205011003001c0c80c1a48408850358000c1282001d4421481071141c14541084404440110940c1007810181d02098215250315004454000d82d203649035140d0404a0040c8801c0c409007803540141d01c084401d001c0715208a40c4e00c0c0f64203c8080407403069080405903100d44000b0284003042c0140042c0311 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 977430629 1250 977429379 977429389
    0x90a0c05060903030f0f130e01150e060a0e0607050f0609070f06021c030e0a1104060b04080c10110d0503100b090108061507050102040b0d110f2a0d090e090a11 70
    0xa103186c1c1d100c80341c240001d00101c1d0045c5015600003e01c40100503004208107508190310121008c031a003449564805000007041c031500c9007010a606200318190342c00710383c1d1100c0c4122400c81b41c021003621200e0b6111005e0030384030320341590303440541d01c9202d0307000c9140207042180c5811140103400410f00c2d1001d41140d1003520140300300450034150b8510324010110010301407105000e01c280484a459900282000106c2d8446c1d0000620003000b4042403154040c000b4280d03ca4140450f45030803a2180c18004441c0010580d400030018003545681c150100d8000f0f0156010718019050030851944554100e555802041d802d6800a42c010b0003203502c41c10000d60340c003018142c000103545007000c162111400d80e0722680c0000c1c517a80001545809015a070b2003a0510408004a004c2c9400c03140c030400c00c030900450381c504020346070200250300e0359260307400582c0203014410155040318242d50006440300c0c00741c1c4101e0140800300c80000c0c012070380c007041d00039110741e000d242c15403030302d00c4202404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 977431879 1250 977430629 977430637
    0xc0403030e06040b07060b0301051b120402041e050f0609130f06020c0d0908010b09010b030f0a0b0a06110715050a0309082203030e010216030219030b090a0c05060903030f 75
    0x70360408400c110114076011540000d2400d24000c1e0000b0a0f02e554860515003110001042d08500062983ea160b050351525411900c801c444450707440705548403400094001c10a01014680400280c40f4410b2900101c1c0c0246100f0050071a201c500da0355403e06020111004032526003407400f240c8160030004000380405101c450090400500313007040c28800c2c910b0406c1481030413000c40c0c131080e400c01540a0034041c0c0a9900b80685004045525202c011038840c04003900c070403014103141001500c078296640c082c500c540402400c0090b0f090b07840744080c0c003603840c1c5002c0c0c0000707018040000c14003c589080c0c8000560151340c440d4504150704104070002c164a80084414880070015804590300101c0303a0010080448bc0005580e8074618002e403c1015802c003c90554018440180c18140a048075a0440b0740551346d142c5001e40340703001c410b407090300ca400051403d4106024002100f80005410102500c0340120000c00d50304c0710100600d0f8013916403840da26034420000581c0700c81440001e8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 977433129 1250 977431879 977431907
    0xc06050c0a0b100e0105040c1407060f140a0b1e010e0d02040c08090f010507020d030c021504110f0a0515090a0f080d090501051606020306030a020a090605090903030c040303 76
    0x510601c0900759a5000e4035041619810962510b040044c0081124044601d005002c00c94007080402082c82c03008c2c10181c91101000102d6501140c80814411a5004841c0d51040e10000704100402c0c0345044500141c00c0d61003200c00c61810fa49602c007070500c1500030b85d8000026441380303c00d81e050710045a07031100c44080f4a40207210f00c80703280300585983c09131130044280354580c01180e14200005a1a01c00c1544007210243e0604007030040203900440c81521030721840ca00071034642c0c014070007a8604a40c65000e50b070120b40f0041000240001d072030044d041007004546000340c00a85400308264204140a026400b014003c024120b00ca1027000620710900068a403002e4981c2c8e40c103150307414410311f901078111500140040881d2603800a0040e02a140900342a42084421440c0114160154800070301c01c030350010108500366405c002088020b130b4010010039180741c80e818120098500340c07250078002c403c8a004a11f0040b0003000b5a4415030000034030600f020306e10b8800300c603124011440c1b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 977434379 1250 977433129 977433133
    0x8011a040c080c0f0913020a0e033f0d09030224012c0411040b0406030506071404080f030d060b030417031003060e0c1206281803091802070c06050c 65
    0x4040464603071140c1022182e40c0300500503123444108401030103c100d0200f8003482904140108400601604100d10903804e40e580d4682800c18900b60b040300307a40d95070034501c41d034400214100940005e0b42c0c0291030307200c1c442d0f0b0981e51880e4130118060303142d00c0041355500c940c1e1040001840076040e03845e0915a01c00b0701a21040100022010070802900140c8043d10441d00541e0041c01c581460b02403a00100030039a42080030b1807031500e9194a81c0800b034031741010003110074620030340d81420383c040d94080c02c0141d0a507100d42c01c8845209540390f0007448081c00b41410800b00080c0b5601c80d0040d40c0c030650b041a421100c1608603200d101e51039000802c2001b50703810358a00072011610030310454030350215030f02c02005107180440c20001c460000800355201c0340c0c44070007080101c10540300014143c401010b03a40c4403d400c424400c0001c1d104014405d460950325a0000d414968420003480c1101c1079842260000d03030755942c800c1c0c1603120314403000d0003d070074220003040000d210310002c25412450100f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 977435629 1250 977434379 977434387
    0x1110301030609021201020f0a11190c0303080606030c19090f15170115270b0414090103030e060c0c0d03020a0b0f1003080c031c0f0606051306141308011a040c080c0f 73
    0x1002f8803003860440d010703a07200701d01d040284101078210400c0d64005504072100c0303042d4604080d4aa0140c401c04900030385440c500c1e0111803109001e8145400a4081c8140c0350b01d500b500c800b0b03c22281040030040c940041d608291150005406004203416240c5a03074140905d140782007070540c0c045820a007031252042200082da00155050106078000e0025044220f40d161b142405180c464030a40c05514031405101c030041000a40140340e03212803850640c0c10b6602c0f1800d2925044c1042c00242c0700d241c0110f600a620002c0543c0800c407050721501c02e00407600c007910303030410030050034400300d03814a21900c52800c00d00100c1e0004001d8440342c82e403417003264548842201d0b04a040c61021040c44030030750b01d46841030000703201f86c001d00001d0f21451600c3c505188619011603100a600d105840604c4600e161042e400003804048411a203850074021354000d07910030402d402081c40c00c2200031041003403104184140f074036000b1001103104a030740d91581d5440c1c4e5200110b0ba9400003a8092007003030104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 977436879 1250 977435629 977435653
    0x10f0b06040f030f0311071806060314010515040305030c15010608070f030f18060b0108060102010917181507061103041a06120111090a060519050c01110301030609021201020f0a11 79
    0x480000500b240c801d1001c3d00d40031098444d02030f49d050f50812401d050401440c1c41848100c200f2190440d041201d02c076200c003d40000c1441c15204541006c0d02038000080c024031101000075101e45003090002102c80543c0c0d9600382111040400c0d901900081c56444012a400780300e5000b41e01c01c1d481c01c40f00042c0e4204611b104001010700f80004a8060b62940040e051540e0040c04007584900700b0700003441958200e55404555242c000e190102d40c2801054100c02c1a444501e0483d501c04068603d210b00103a85a000505401004049860f2400d184e04000c48050040c1036034059070340454400000c0c0c0b0000c00c00300c0d00d41002007405400c6554401c82ca01180c4090050114103401500c5a60340c64405030140101d41c42c02c0c1e000241400006c11900d002c0102000c0341000940701894010744039000d00444501401118550b00700440000c4000710a005c5d0a50014a00d144200c8540780e03100070140d15182030740070b41d184d07004200c0001e101c0c081005000d00311100d000304003942611030543c6c5c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 977438129 1250 977436879 977436883
    0x3160c050d050c011106011202011b0210210c0c12031b18050f031509030702040230091c09050306040321020712050a11010509010f0b06040f030f0311 66
    0x3204240c8103940b020982e03500f15604141300f03426801a8402a14013981417500007039401c100050001c2c1001401c46241080381900c0b10008460f80d8001d01a5808881001c0b0003402c15840c4c10350040300600c0808240c4890005100d0405256466201c2128000250b01c0740e0307c0c3c0307129400512040c1074807000602010701c0072a603102c0048505880c0c00d26411116903180c41403120319042940140c5c03c00f40243c0c400da50004d9540202c00407518070402c60740c0c50b20b40745170560003440390080d0840c0c004580c00e20540d2410202069828480c0140c407402d185030008824904815562007007182c10400481110304688035201c00202c201d410040e014a0361003011038641502100c05a0000c3d00f0341c80c3c0550943d041907007001d0b403194402e00c2507003031aa880c1c58040700e03c056925204180b20002400141d101d000c0e408001c0781420b00002002245095140303540070745541101207074480d140400b010030f20302e0540b0a9805941e410a0301460150541e500c01100f02c12586c03094091149524004200d0101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 977439379 1250 977438129 977438149
    0x16030311010b0a05030a0807030917100e1f050903040e040f0b010b0a05040e100504020a030e0705061e0c0c06030a0905060a02040303051801030f0906050f010803040803160c05 77
    0x11940d91021044010308500e0300715030700b00c540b4520404140c0ca040001ea5400140c0b060300c1c0750840b080507038448940c601178418621940c071941454400428880d240c0c0382c0401d070f280700700140070014080300d440e5541480d269000450880c4001100c41d0a12101454680c401580f01071031070100c0c0e20745a240e0081d640f00800072603088500c503024004c50410020349802c420f0060000d14401800c0003280c0300090420300850092070b18074203142c80029403400c0c24500000007000301400844d0344008884009003c0d18030300c038589496205800c000182c0781800011500441134202c560514401c0e04070032500a64402e4580f040c1500c00e5000800c0c60707036500c6006500401c248035000880601c03d14001e410801c00410007012144180800c10209400404680760700341c41010613058111070b48010f8006212074950241450701c4e2038842c1041116a85c80180100c081150b03031480c9a9881c6c00e101c1d500e1242d8011500c5c150414481084a918040f0318143c03c907120b80400f58007141c0315004516000b00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 977440629 1250 977439379 977439383
    0x10e13231e0106080a050316030c02090f040c140f040203100306051e1605030a1523011202040602030406180b0d02180a06230c150711061509091603 65
    0x500701620050210007482040000c0801d00d020f48000d03039154031010740324040c440291042d01c0741c0b4440101010310810048034903d6005000c22007508081d031810700f10107022181254081ca4001c000700c1c1c5045000011010701c80c0c020143c00c070021010080c00041e400203810b500b0000003810b008400031f0130354095588501404040b15061060160350844402005404202c507a5000c4142c603100d40da10804403070784400c003c030001c03030f46d12621071134942c80d1040d5a00200f500c3e2a036601c03004a009481140560841090b07a400c4603240c0c69180d8407049100314403031a00075174030411040003824041e20800c1568074035100f002c0451503503a1241c4c003155001025a80d480d560016070014100300b003410111002e0340c1900c0410300f0b5801e001c0050254244000d54030300c584480c22221442481c1142100c01c1101002d003600c0014900751109001140240ca0090202303c884050400000b0000340f00391185034410500078400441001340000d810024051340043c1c069800600c800100920780900118 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 977441879 1250 977440629 977440663
    0x126010513110c01020c0d0504060801030204020a110a080301080f2409070f080706030501061e0509030a0c0e060108060d1703060f09040507031b0f0504020a05131508010e1323 77
    0x850b06d800841d00340035050b0740030b5040c0102400140042c503800141241500e43c1624010ba030703661032520907200341d8050b0414188038816402598104086400078504840c800e0040343d4403d80b4082200da01c2d01205081e08030748101d440c0e1071100e801203070100181c000c040c92058401440e29181004e0007841583c00413030981d804403200300a665410700c5168010003c5141c600c5e045054014011000e4160514107810490f000ca04903200c2d550900840060320f5101245414071680c510410402c400704072041800b2480007400100c41e410001040c0d00542e5018103044140381e1404520344107500082c1c0300942258041021890a0b1282c3e01e0040c0103d0180004198841c0b461421105480e40001703000e81d1410764402c1000102c007600c00070720a80700116005a125101801c080b10741d400342c40d10f2a01580841840045d02e481090380c001c501d00140e6840c0143c0360381b9009c40c032102034029208550030120300302d41403000c83c42d248404112481d14081040c680b0510b030b01001d19114034210003089076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 977443129 1250 977441879 977441887
    0x14030c0601140901120b060f0406120b0117070e0705040308040321030b0609150702061c1103011203180807060906090e0105101b0519020126010513110c0102 69
    0xc0c140642c4004403100d003159510f1156040020ba8203903105135650007884410b81c40c003c1030107561040301c1c0000d64503014000b00003455031000030340c1500b11020f07400d4501d8400d010010941050150b110a441380d00b150040c40d03098940b900c28103a00200400300e60802c1030a010100c0044c194100401c002c601407100d9a407052601c03210002c850120294110501d0325003024a0701710b86a45003900c14041048440700d08150301c001d00548103100e42c0e0b9000b58020400100028002908180c00b051203035111810000d0440b014071f81c281a200a0190114102713490340d088000921481c020030341c3d5004507032042c007800c0c1c0c0c810880340f41045175002100400c1e00404140621039110b20000010030464524200c10352400c1c0c0854803001800d11a0010824402c007815107800c41390300f49081d000da0050032a030005500704000502100c8018049000506a408400790f01480000e020201303003a00c04018110791800c1c0c10030000b07502038050a8403164855501140100c0c80c800038015038214040003582e1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 977444379 1250 977443129 977443139
    0xe120321010519081209010306030f050a1b050f100c0230061b130b0a0512010504020a0f030b120106030f0210020d020601060311090603070c12020c03030306040914030c0601 76
    0x203c9485440303007078054980c60b01045500c80008000300c9070030702e4145560b40c400303500004801418940d003002c0d24a803081c0c5210000c00600269140e0528004c0c036603540142100390340e4200d4904644130305a4040c4100d01c20349041e14103400c2c00e08030612036080842d0281d40c2680401c4030404900c91a513106000d05030804009142d0709000014030b5517041c00b0740002e150140018144c500c2d080780f400492000031804000032006540c44401400038441220348941410b14014000d521400d030308400700c0d100714000105801e080c003c0e1510b46c00981c4844e01034800da000100c0c01490b0704004164401c01c042c4034883d07a48000e01c42c1401840c011141c0648448081c014400041c0c0c4034040ca0301154000100111005e0380410564103481c058603020030071256003550342e0218010000116032181000050040203500050318000143c4203c1560000c1c100180090f0307150742c030306030040b43c054108200282d264540b0394080c51a00b81714100c16019032044c04800e034a150000104495039521800c01801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 977445629 1250 977444379 977444389
    0x140f0d0e062508040b040201020a0c08010204050f272503090b0606040305120304020a0905010b03090705042f0c0111070309080c0607022e03020405090c04060e1203210105 75
    0x1c0800402c0c10000c0c0b07000c0e03181100402c0008000c00182c440b000010200b02107a2090101c2c454040c3c1002d55210916211280b0314000e500c5440707014498000e80e055101c03142840391103c440712400b115542c1d21400c0c11200f90710240b60040107030f407014100ca42060780712182401101088905507600181200c094984540c0200c000f0f48480e124000600c020800504000361061042c283c14140b103880c3d031101e00c017045650001d034024523102401c2000108e00c1c407aa020140d8400c0c9450300c2241c420b99640c03410302003210151405100590480518064840c0d02c070f41034940700181c005100fa00c1c041200d201c3d1400c6910300b83c2c0c50070820400240c01d005041c2d2103594140502102c60107489000d080c0000208e2038411a50000d0041c55a840f0b050743c0d200e6189404440d0f001003c000200101c54084001c00961160103050f1040103150f01165042c88070009440c2030310398546a554011001d201003155400c1c1e0b10300d00240c00d03c02000342c0c1a03901e0108440000074803100c601c070b041950502007086 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 977446879 1250 977445629 977445661
    0xe240d1b060305180d0c110418021c11010f0e040501080d110601081b0d0209040506100803091309020a08010213090b01030c0f0f0908060c0d0b01090303140f0d0e06 72
    0x8040b03849910807504881010482000d58601420315088412941c6880d0801f01082004260700515000c5a42000741c00c1c0240b110140380308580b4003840404c00d0003105040d0a40d9403014100034044958001c680d401203c20710145040c83c00d0078601002d43c0070018042d200244c100010369005a80301802c029085521288010000c4010709015810440c42996440c502c0c500800d8140400300c1d940819101c400684500540241121400349032a00701580da400e42030b41c009810302c6104c04000b8211902000791201004024a1011640092078a9102030401504140ea11403030f0300d42c00044001c424070017400f8641160611089040c0740003011000c4441002106040c141420302c0c0e0030b261640003003807410b00c2000c2e08000d0000b04e038006089640f0520307900148402c4c4600c07800d024081022001034995181c01c16414030100180000455020055104c02000f191004a08491003030104002e00111047d8010b580e0420304218070410a5036820304071182141c100714140704541c680c1e90010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 977448129 1250 977446879 977446891
    0x90c0a090b09010b070f06090c0302030a0b0105030607050c121e0c010e070501030b030c0436060b04060303051207021c0c060e06130602090402070215040905010e240d1b060305 77
    0xf1401c2045c4d6898200c0040c3d48010000c0040e0707680d000c01804c0250f81da40b0540916006400c445c1c1059480c501183d080d042800f500d0721903c41c0320300141219100d1001c0310303899200500640f421181840c41c00200d07801c0340301e07600b40740300009550585c500e00c0c09000d8021048054000b06c0d0b0071800000045c14481d42c0c3e0021410075050960356410358500141070382c0665030030f6400084210b00d000060412800807c91144a040e003803508500c07040c0d035500e581c4900c40c061401004030050f400b042000f1039150b0300c401000318106001d0f00c0d01512440050941c080d405005a41100602e4246000146c0c1005000000f080807464050180f06880c8100d18000c4807080080480b410112068160000c0f9003400814680d00055840c5640e00c0315016252165409000221946020081d601003504140034603c009458040002185890044030b18001c04010482e5000603200d103070142402c142c00c201803a0480200f1038081c0010302e40586900014040d8007800c004103082c03c0005050b1040680305d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 977449379 1250 977448129 977448149
    0xa0801151707050c0f101d070509010b0f07050a0305030a200313030203090d23011a280f080f0c3a05060105010f0315050108090c0a090b0901 62
    0x1010008030322424100d402c900d240c20a107403240703c0300103050714005203041d9942c5c45010f00117603008100d400d604141d450104014140300104d13028511030781d031aa1184a42940805804010489a0303070340d4000b04540a103801c0702511300041e5441352031409940303400c200c0015200208004003210a4882e056560006000f0032614040e80c0f0300c4e81c1c40c240809801a596a102003072890b003014020011144510000741c40e800039402d0038280b003440385103d01251108400e622400700f56920045c0b0820010340d240221520302030740303900280142c00100f601003000d0a101d130104440070740c04c001d15440084c0300030840d07440340b181010031250070075000546910082d4802602d013002c85c1e0340c1826220140303241203c140052405e005000081140c07040c5142060044003019400780303c408150241a03982c03e8803110000c4803015422011548039403610705500c551442c0901c1a5072043c0610740d00a000b000449180000d05000a1048032180c0d21900e1066582c00304210340e801d000004a006001c5421 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 977450629 1250 977449379 977449397
    0xe13090809120115150314090a11010503070c03030b062a16030f06020309120414101740061805030d270b040209100f0b0705010b03030a080115 63
    0x90000c030b8894580260741c2c43d1701e041d981200700d00e407090340328550103c9031000045243c1001c1507a05e0300c540000000740e4070b44034090100581c550284080302d01a015035580d948594402d03880440080640f981c0d0380d50b01c61010885800002a120101c10705190610000b011030742c2c900d503d040c50042e440c4210016002c04210070400300f0103100c2c080e0782168100304c1c003503500c0e40e506180b981400401200e05070384907008100440d8140128103600007030482550440d81c0c245105400b03a90000c201e8031740300b400000410006001803010850240b400940a41c40003000c8c500182c00c20014040d40e02240600e410102d01d0003d00030680200c21514041030903c03081441c0c2a12170070303141e12400090451460701c40450008848200b812000c12104d0f0205503100d0005624140030250b20550f4140e1084d40044041030710051400040d808070703030803580c0c2c0303450311803500d80f103495a40c00011081d14107569441c0e400415803824002002040345941da098401e42c10b003540040799250024090041104001e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 977451879 1250 977450629 977450651
    0x1c240e010807091a190e07030213060c062012011a030c07050703020607030f0815060d0b2b02240306040e10060803040f120b070e130908091201 63
    0xc140d40003503c08041c4007040c1c101c10300f49180d04070010a02840d800101442c1011240000f20600d1401d95405440301581a242d1140450a9009145031241100e51070f5200708583d0707009014070703041c0c00d10900001c146414002091000701425580100c0c049100250380b102d012101c0d8801c40c054250f55074100000042c400c202c501c0d60100900c01046800009144428010301f003040200841d4028212035403506940380050801849110080200300b03010046a508084204101802035001d4081c506042c040030144000d4101c1e05001504145400e010030002c0c51890700d16401c002500d84011b089041c6407041c02480c00311510107001d00d40c1150034000d000d403c1c0400b126005542150080703000a0342c0072165060503690301600341c0e450700c0d00c80f0004940c5c0c801f001510840f021820581501540c03603600240082e140714005008803401000298000d0013100720180140e400f80c500604081c2c0d0340100402c41b01c01d940c040d22941000328600500e440c114030700c800c048040d8070003444491006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 977453129 1250 977451879 977451883
    0x60f0a031509170d090c050d0521131508010e13080318010906061509030507031e020a030b06042a032703080f0108070b0f1c240e0108 59
    0x8a0341e414010340d11075680c50240415003000185403c4100000303551340c451503180358000d14240e40c0440f00c5e1141c440300000e00d80b804540300403085030401c003d81148440e001c40001d18403000561030074000018000210309034030f074940427000342c018034103254051120808090440c02c4141d12512070140640100040d602400d20007441090f13101d000035489850f002069a40c10000003c04400e40d86400301000501c1482e0b00030764102e079050b40101050500540044440b0b6016005c094450350150b171080001910b0b081c241841c840d0b11440382a044c115650004045103a598000e440d120b410505000403481c00e4402c104040d0b01c0c2070365020281500d94100b00b12040c004041c001450340e107003d5642d03903041c3d4042900ca0414025603221600489140141c00d0078400d503442e00c050b610340e070008034500c44002036100c1601c4004458a0400002d500e00d00350550140c1c114050003207140c001c2c2100303409140900c0042d403001540721642c01740594403116071600e00e86d00c1000d0036000030004100300000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 977454379 1250 977453129 977453153
    0x1050d0f24170c0d0311071220060f09060d0b0909031908070e010c02010909020c0a03020c04230702031306050409200301140d023f0d08060301091a060f0a03 69
    0x498101070031440764000ca480e040440f55481010211050910f00c0104483c200314089c1c2181540f01310441c4000300030034484140103001e01855540390030411600c0d2031403c1d201422142c204040c020800500e41800704220003010340d40c4094540c8042010115443c1c0d0401043c0d80380414900006245810079005040c915078140c0310b81400008074408055900c60402d44020744074002c0e0030341d41c4032012084145e0f5281341c0b00f010340041c094040c0003000c52a0070300680c000d80c0b031074215440c2d0640500c0c800070780c1d4560261610b015803008100c85041842201d00403001801941c0b0f9030b41c0c443d4074019203a0185e038a400c030383e14036009110051880655400054905403150303c801c003040d641004011901940000c040a9444001520b005502c500e18991a05640316003920b409104028052000540d01c0e02841000441c1c000e15901d645c190701c80c41900ea40321a0040020030494a00d4a52820b028640e08200500c80118020001c0c10f060544a8001c1109c0a40700005a0b078616141d070381c1c038201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 977455629 1250 977454379 977454383
    0x302360111120904110c061512120301090c1b0309030b060916050901180b0301080d1e050702011e08271f060b0d020301050a1401050d0f24170c0d 64
    0x82e0b242c3c801080e0782107039070640d0746c0b01403454120385640c00c0c04090078030801811100e0911840390b1103801c0820606c08038800f405800c003440c5044c06e60f420581c803039010f003c000c2c08507001c021814040e009210540407151900034065210013030a0303030641c00c203680804001082207000e603021a013401400d0310940c0e101c00d5000f045191483e03c480110004881101450351500c84880080c8808911a82544000c6040f01e400c0e200310395603890170940945d00a040c0d6507001484a100d121001c142901a4005100880c41450019241c441024600f078148000001241c0085c42140402581f1031503082c0f141c00b000d0848005004101c052413041e5901c0000b9105002c10400d08503801015856a4101e45e01030007918002c0346c1c41d0014088050000d40003441858030900e41e00c00005880800e1001341d08020740182d480b54501031700c680c01903014080190324003084070781d580c59010180e00303900380c00b03042000110720703070800a464212200321248540d122002581c100400144959640311030000d4207030303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 977456879 1250 977455629 977455631
    0x2823070f05031c0219170a031401050306100b1e030a020705010c2a0809060715050c0901050a0813021203070614130b0c120c03070f020d020d0302360111120904 70
    0x43d02a14181c1c503440e0199902c0075400706c0114120b0103650f0181c200e001011000802d09045030303640e5080654400080e6010f101c102c1c01c1280503c182030050005101940b05a103028019541e40c09003402203500c110b07544d41c1460750208055007042402c0c0900400040145407242540d28129040e4056450902400440310b6480e01c04808221404007070303807003401000307103d00e4840140c0d0400140650300b000280786054036140c0001d0020a040c07080d114107250694402d410440f01c00b405842010020f032511800c4d510701c094603c01a580c44480d4564011491301958a5000c50b00d420000e58094542c18911998440100407020140c50000514541c00c0000780d0b0b9261100308891189129086030017203018408420810000791600045010312001c1c2d5940d401000e250004036103d0070007001c06001070300700a60110560f8440c0e0094034008480607540c07001d41c020008080c6103085540d00d40c000d180c10540d038440480da045000385240e10700c8500941010816480c046182e03101e10050740d44a2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 977458129 1250 977456879 977456923
    0x191e050a05100e0301021b0706020706020a0816020d060b0f040e06070e062203030f180504050903090d0b010504110301140d03030b030d0c052823070f05031c02 70
    0x42d61040f035035900d14102c041e00071941c6504010310451191000c1c011800c052044000005e01c991000030500101c5003254060125090107580b04032842c0e00c282c100340c1601c01c00302c9803980541e0380c82414500b0b00b072040ca030010b484007480f8240101040f4008141d0722641c60700980810545002c102641d02500d0381ca003d076003c00076040041c0c03840c0039485414046400141c404003294034115404803d50340243c131403400c015103014040300c004042025a42c10440343d40b10400c001e06090b003026420810980a0700d0030002d140b400f00e182111002c40c00d8607204120b0004000e01d0425206500e822080c1d605003918540c10040707031030819407100301c2080c01012030301000d000f0f051180c0d00449140900409803400414088801440d40c02c2c1f143c2c0c20384450084e00c101807034010840039980001640b028150041100613250400817010741407050201c900380c4450041d42e008207100341c0e000b0345030b144080400ca0741081d040c54503043e40000c04050824100100043c426000543e080f10038004c1b14a43c590 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 977459379 1250 977458129 977458159
    0x609061510120f090c030503090301110f0703080702030f0d15060c02010f05070f060c02030c010c050a1b0c1505030a060b040b090f181501030b090402060712030b191e050a05 76
    0x900d03c1e440094200401854003101f0004013000600c0d40140032802400302c5601305603d04074a00c54800c055a000c038080095030002409110708941c01202070050f01d04204030001000d2690b803000d143d0b401216901d071a40e0120741171940c640d00180285107800388486e580c80d400608101c580901c0e030300a10101003210800c200c00840441080d03603202c0360900060360710040181d03403a0049012044594203001c40424081e00c14001d0380ea800085942e02c050317503d0103507907003541460700810a8403043c190b0000850002c4105103054070340801c55071410398a24102070144101e60360394001c0c6d010100c00300300410421f81d08505030391050302d00300e0301c28660140d41c0001078034a140401040120700840010840000f0030180c08402e404400c2e00d041c040042c0d14410005620341c00c4400070341c800018010f400100300d11116410820320740f03003000115402c0101c0043c603920f0301c0b10500240c24480c414180155071303421079180c102c010681c1c4c8046000d410b101c00034500e0055402401d01075070315014038100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 977460629 1250 977459379 977459381
    0x7080d06050d0606231e040b0d14060703200901020f10051803041d0612060907030201121a062d120708070503040f0f02030609061510120f 61
    0x140002403115120320014038151020b00818805d41545003102c491465041450681c0380071440b20003440100c04201711000700f0034100c4001902c42e089961500b2940d900c1c0c03241410801307454051601c0300340318040d0055a41c50082c005006404050400c000641900584652141e485200c4d4081a0300c5681d5080100c0ca007440c2030f81080700c40d12800000140682c07aa0344014050222510414003142d01c0c02030566503442580300361f41c03030004203181c3c20350386203e031522158001400030811602c000c41c0058244c42d00e08165500103c82d08981c03410011981c01442c0030051540c00d21082c008600b081c44110791854405040360702681c1e00040500c40c9000304400d940b823481d800c4210341040d920f40012940290440444641c1010341784001c40c14036401410b026100e40401d40e101440c40d5101c0c1d5a15010340c48240d030031500312007900014401690244484d6120340c12500003403a0300e14100b0104408181800685401200e0300a0704107160741d481010503113a80700c0441c001c01e40c0b00310215004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 977461879 1250 977460629 977460641
    0x15070f11030d080115030212060d061b02030c0c0d03021b060f0d0b1207050306190207020603130b01090b061b07170a0501110412150605100201090204051b07080d 71
    0x981d140c0940050780c6411500003101505880c149203031203c6642d00b101c4103034101d118034a030140c509421080000c10354a400b0000c0040144191004205584000c060003101001841d00a0140e0004900e0300c0c000d60040000b036913010000c90300c130030307014650303481c065200e0101c038500c0c05000310b6001c0946c0240d101d2100b01c03498141e0b04940c1680d078680ba006001e0007880c100c2d458a02c14a034885170080301e501e0008481040e04e0300100907103c507403924840041c00405240c030008603941c007845000003580d9201c0c0518401e803256000e01d44010a01c4c5849403410070140c02107031a1501d007a0050100740c0740c0038191400901c04c01d83d10b03c001c0200141c0d061030101c5680c4411a440e4900441203800c0c400401d212a011f071040009200c140c2030f0780c50200d400c4c081c40c00742d9a200e82050510f280410400324514401d00845240080c41c03a03150008560980c0d80e9050040140c4c0d150b60000c41141418402c140d8400041d042a48203145e007410080491700c5110006407070414003092083e07081c50164800c0e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 977463129 1250 977461879 977461913
    0x2060a021c02010e1005041101210507050a03050603070807051003140405030c060f090a030311071209080d0503010305030702040c02070803070b1e07090b0a0e06070501021815070f 79
    0x81c180c2603031100d0340240a80b0800142082c1801040c061030b005202d14001c02e40200d40c4503240b070203c01d242d0340044614680500034a140416004064551040b40e44115400703041c40b0307038a071035076070103411400f40540c0c401400850180c0e00c010405c01044401081d00303820784004540280c121000f00301c0c00c038051700d01c0c450b841c40ca0844010034007040081c000018802031240500307840850f50342d60701072a0f070306ca4200e0f0803500b01d41040d400307000024442d0703201030410301ca44080300d42880350945441c1c02c1002d802080750040b442080302804008410405215200b0203031600034a15819680c59680340e0140c288004d0180b900d65800b4070106000707200c002c0c040c10038001141d4584090782401150b2042c140d0381d004901c03003001490070f8130700c014061052180f041d03510382c1e4061600d8007410300b103503070701030b0240200700910007414094941c1c2c0c0e900141803507806240096251410078500b02128454541118469100d400d00703800110020015201d4803030308121647c3c904100f03801c000114604003410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 977464379 1250 977463129 977463163
    0x90803191b06050907050102010e03040614131d0a0b04090c1a0702032a0a030305070f11061305280306050703110304080d060803090d0b18030705030c010c0c080702060a02 75
    0x101303c5291400544002102c209a00034454828840e40c8103449104501800b800507401c0082980c0300341c00e00000305000d10140740e00d180341640e15043c20707008e140f65611b082d041c001900140000d00d00c05004018003000116420002154a995244c0505030720b803007444216038640301c0316122010302206590341745401405484540041c0941101102000000050002d002001240b45410404283e00a0343d81c185c84040c50079804d44c42da401940e0000310700311055400c440800b922519560058031259041c0c10b00c82c0e078002e042c101003022000951b003001c180702c01c00d034031428800005903910004413504928002115210050114017030000c2d600354111512000081c0800c0180b103d00404c054103d0300000c00c4980d03150349100c0d489115040d461680448203c0321000801c2c15221841d4000a4100040e0407100c41c0c166031a085400441080d1250f400c0460102e1085e0800e002d0003a640d0384c1850104c0075030000c0d988429035070290210180c06524089200c071074940c000c008058081d2802c0302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 977465629 1250 977464379 977464381
    0x10260703140d11150a020304060603060c1101110a021c020a080315040507020f033405011d0606061b010f2909130b100321090803191b0605 61
    0x1104503a94011142d050000a04004480540c000c0101d2044001d4080503115829038540e202d81c0340203074002400c1501c0f4941d4038000000000d0040c480c0c038010315002e44070413100c49000b05050f800c40f00644030008003401b08008100c174040d40410400718140c24225103510504014000300c0c0b40c20b0442c08024203c0e00300009028000300c0c004015a0508000c64050002c1d40c2c0f4800101e8540c400ea00001c81598420f00040e20a50400030412243d003195007030081015800701d80c0d0070790003180900181d90a9545809410080e480e00b010490902d900c440180a82c0c1081804505c0d00d101c0d2039007490104c0040b0024503149402034002401821290000340f1451039420684580600020101c40020b072841c441c2411310304000c42c41c14800c10b0f035900300b9958180d05487c0d1041a01005151040d120300c0440013200081d44404000030031108042c40c50f0b82504c8220000d0010342564114079455482800082d11564030345500c0d40c004c00541c9131610100400c0c2c00c001504442c00d040c01008241000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 977466879 1250 977465629 977465663
    0x3080a030218040e15090a0609080c06100312080a061725030c0306050c1b010509060f06031e010e01140406110906040b090114070605070810260703 65
    0x14000c0d020309000d000b001448601d5103802c00048420100d011900354020070842d002e107840802c28503034083c03010010745040d082181d65080856001b08002c4900031004903024002e51410081c10703610000030307050320700203d065480304462207001401080c100008003000a141040c990840b078001d00c0d900700725400340d0801c071280503155038000e10395822500381c0c021110480a40c400211b000c4039089142c0e03480c4113040d6155400504002041c641c10348100300b0072104042042d030040020400088000605818201080c03400d124024141030000880c1000340328169601003540308c1c1d000e94081307111a18501010384107001d4001841e561b0880c1d444e02e081070204c0042d80c01c00310310480c8a0030040080b00710155224030240144501150000780500c4280306c0d81c0b040b500180548003050408100a040c0900050340c2d40c0d1240310121441c070f480c2e005200219400c0700115400540003d14000858207248003160441907040f074403100f044204e40ca00110040601904014580080f803808068241c0b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 977468129 1250 977466879 977466881
    0x1e050307020405090102040f0306110403020307230901051302030406060503030c070807050415030f061404202215150e01020706092319060807120b10051303080a03 72
    0x2800c4160300950a05002400300f480602c00c59043d10820003200307126a0440c2c69034001044160b141c0d000309501008044056603041000d82e00071b01001000500800b50135071800c40300018405018001e00e0414014030540e030b202160040000e09034040140c0340d59a605141018040300d030322891305400005812040742d44042040710966151504885165913108203100440e0500032005550b095030740c50031b00004c1e1410b20805a150701541020403d84a41d007030130300e0320400c181e42c21109000b5080000246000c82d4641d2204203004031960319410130a00f050080c50469003003056280d643d58100800214280324081c4003070450100d1070071600c052068050310b0706803180e40050240c422034100040041c0709014441c04d681c86501c0700b03050703031000c0e40c002c00d615800030002660141035038040801001103181c1c404014041076561310384905100c803018100d05214030b52030020504001c1e03180203175116000456003c003181d1520b99690340d03490920301ca2644480d04014400000028000c504980c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 977469379 1250 977468129 977468137
    0xd0506070201060f050307060c14030f09040c081e070c15050a0b0a0807350d08151804020d0c0e071407030e13150f1e05090a091e0503 59
    0x2180c1c0080000315120141c2d41c1111a81e0f100d00c542c10790003040244901032044180802d00c1d84100000050039032451541e605541021002c07041c0300d1000b180014492425004051040406091003030b082d00780f03880b480c404498210041c000c000450707030200d265144106013160085820000c09800320310146014009020190b0700c9071841e500341003101e42c940ca81b00d00981c041714540802450424a48200d850340c0101144401d0a00104030700148061030910a04004180405000c1c15480713003160009080c9801c0904101000c59070512810407540341d085030784034117130a030b19949442c035603544c40000c10307a4503c13110013414074842c4100012140e5400d41c0c014001c5107203486090f0500307000f0500403c01c1c041c031003025000842e50130011040b0300300600d1900010a61800118440b00c6001d9544000d0140390700107a46800001d00800400d159403c021800280fa0160402910324040c00100203000280c011500c4076503ea02410400c49142d00d000c480c3d080f56488141c00c1e9126050858680d04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 977470629 1250 977469379 977469391
    0xa0c092301050c01091401050a020f07060506030a020a151215380315010c020906190b13060905030d0e060d06030f0309080c0901030b0106120207080c06091504020321090d0506 77
    0x8c00d001c04903100c808a402500e84281c2400c100a04203400390702c1d00070240c0806420942c00d40030380e00f007c00c007503124210040094844060148528044524010480007a840fa0b04090700e1030000706d00c03007134104516058220b41000d28111b2030762008a501100081e121503008840aa099402100f06034010003e184501104407044243c580300078015945c901c81c480300294010032110006115240841d0708402441c42c869651408a40304c0b49000d426511030010300303070307800240d900421545500154403400351a0550203806080000e41d005811500303154205445120089505260003620340e01c0340d4021a0410002da0082c006070030003a181500a000704450b900030110218a0750518140701c80c103c0f43c1c4900c007003585a00c0c041d81111a8240702003100718140c2c0800840011410450242c85d1005000000c0c0446041c0500080e00d454036905120602198220800002d86d0b0081400d104c0d42c201901502d00414044502002c0f0b03208180d0144d42c010703024001481880000194030b440740c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 977471879 1250 977470629 977470631
    0x11806030c27030c09050415050a09060e010e011d0304140102030d0f021c020313080309010207080301080c0a06080f0a05060d0b1302190315090204061d0a0c092301050c01091401 78
    0x16445001c1702c0d040d13a100320b0700030301003121342d00d0100c5080410381e2040d5403040244000041c443c200307507140000d5075517441010f0081e139100c55580300c502000784200000d0000020342d80320200f0071201040e44a00030703171046d181407201c080e10295a5900034000c5079810048100100810020145501d0003034102c1000340000464140882c0d000103e40c0c8202d03405400c1d080007048031440c503940c4001c1241e0000742102c0e01c554090100c58001040c0401640c0a800309201400030740801d481448010a070381c1d40701d90100843c070800d0003e004281441c00b6042054844081020355540004c10b2080d000400d004282c1c2c11070388100840511140c2494048500c200c07510001c0a0150000004c1c0145070300002e01450320000c07c090018105a0050920520151011a03803d030b0703640c10a081010385001c10251201084204100061240704040c1c218105090499007a4142101310b01c0005001e414000182d041d000720b0004ca80c094410b4480e00d0130540000d0102e40c036603152200ca40c00d60002415025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 977473129 1250 977471879 977471903
    0x60f071101080403020a110120010f05090309102a0503030f091204091503080a0c03020d0c0c0b0c0a0602130f0812030f15042306011806030c2703 64
    0x40e42c41800340d03900494142d0b0041c1501a903a440b032050004612035403d0503c089841110540d550b62040c1050702c80030040005068072451340b840050307480043c03005407a504200080b0303a80e1741d524120309140f0882868801c2c4c1074030b40f0300001851200141e80700c009030384116541d0010000000001c5100300d241304074000041c1c0ba030b43c44031039a0b07071a200410540010240024401c01e5039940c490204825040d00d0400d180d40d0302d071120741859120070158400181800c01800500d41c041000700c2440c0d0071440c1020210b0380c1d41e2540420340915024804452000140c0410180c00400c4003248561300140d0131540c44c01c0c0c41d000c00c042000d1500c40d00415042c0f450b4002610b010114a0000d180898840985999203480c40900c0c825002080e00107603c0b19040510040d81f00c80c0720324031120740044910a401c0c1182d92420340d05d1079000782001c2c1088151028841400c40940154084504078100450880440f0000f5206041c100449601d480c1c030348402598100300c41c007c0f40c001c81e070140348002c0d00703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 977474379 1250 977473129 977473163
    0x14030f03190e062716030503030106080c090d0201050d0e0d031b0216050d030c0b07120b100c06020c10090507031209061d01090902070b0f01050409021f0905060f07 72
    0x35000300300d9914461042c029000d002c013107002c05001c100d4104103000e584c141070004040c082a030800e60002e44d825072000c00188030b110340210032980c000c458046200d08080300c1c0070000c0c0b0042c485680c004d0402c2404a070421840c200c80d08a8100e88281e48280c450100c1d0390100200204903481400340c415242c40070000e403460000c83c0711344041c40307490416030280307042205000442d000c03030300202c3c00c008000d06490041039503270000b00d00a82d9241d8a6460031846d40c040c0c10161001002014841d901e0f480301e000c180d9802417406c0141c51740c00000981c0742c03101e618280781004020600c550440c0d0400c01e0039401c12001107110016170784a0744141710f086004c44421203c6407218002d00e0080380f881d406823080400700317520f964210501450840f00c103903203404054040ea000324500710b40c1c00042e8818040c544076a22a00350244c0300c191008c0081020540009910800c1d8441da28411100140e030b400015105500c40009000060700150b03444c043ca041d82c041ca6130100c6020f4a1a81c1d8210030519 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 977475629 1250 977474379 977474383
    0x50702010507062f030f24010f0509150712020a0b040803040c030c060c0c05010807021b0316080f100c0e0613050301061706090705010c14030f03190e 66
    0x151640603910389007440d00950b120001000180030b0360b010448008180c12640030121110110588229010b03078136800e11441c40e20503400068190580585032601881400c4040b1880c070705001000d183c44444604030880c140c0302c0f485652402394101d46031100000303405545070001c00b0b285200d0101210b00c81d504c100100d846026000c0001d020328108030103c1c0100c2c00d40005590018012641410705940e43d0755010b101955039030003440456103603843c810034021071407803800082c6002e0030f0009462030310000c001d480f81045030340705000c0070b001d01003503902c4e460820121400c40c4106807100d14854964400c50380e21030160040069501c942c04420017842c6890041242c07407900c0f43c8407650070300a01810480c1540001035020885214900005140c0d50240669001418050004008088003c83e07143c1010002400d00326654440341c01040946da010031481e0fa0300c2d030402040c48203034000080403400c520446071090b00003c0301005220b40619401c0f0460000a0010130401801e00075160103030b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 977476879 1250 977475629 977475637
    0x10801050d020f01200a060902030c0405040b0106140408010203100f140603010302090921130915090b0a082506020607080601080a061a03040c0509280b0618040c05 72
    0x2074100340c3d40a586101035004032240c18400010b50841c0d84082500101c0da8500300c4204400e9034101d44030454613040d42410300144202010641d400e1000b85043d440d01c505403801842680100031030014900000e0900b1001d4070064205000299030302d0a00b0b91f038038111030840740900d54544a2120002403544803020080d003045002416550950307103107400b040720200b401020001c40d405001e4480380c00c035022200058146002404260311001d22001d0070383c0d40c00c015042a20b56626080d081c2c00c2442141032a03c0848407914004102d580d50507000c928010900c1d445106c2500c152880c200341c11000081010b0100b06aa0144564070381c0e0f05001c0780d070340b0000d550910101d4034120100d00e01d0f5126011503548903c1031200803e0040d5510144004140030201594006501005120170801081c0c102c0340100f404481c20305883c02c3c400314004000f5099001c51810290180c407100940c9103076044083c80d0000245540d03141d50038102c1c00c5486203c03450403140303c1c516000c1c90120700d1303000d4010341d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 977478129 1250 977476879 977476883
    0x2318070e0f0708180a0807020103110705071703090a030b041a0a05040201020c0f010807110f03040b0c010606030e060c2a010e15010f030609020411070804140102072d09060b0405010801050d 83
    0xe080d542469120701c080ca0780114008e90405888540c00580303100c0140c0100788d6584240c0040000174604085004038202c0c2c2080720304250400c00c4041c04a0760707503640d00810b89410142d02842d9455500d01949202d89041012007030b61802c0c01001013000c001c1d8030840c8160b00070380039110603040302c03420440e60348801c031641400b0030074440c04140201e2207002c424034400d5208048680301e80c0801d07070851031904140d0165000707040000300082005000c1c014840108120b050601c10f64401d05081500c03100020104100b1150100d0301e0340354001400402e100d0326644010b40050407480f095014060091410401124402c040c42d81151151030000c2c1030484916041000e0001e00f1aa82e01d07014042c001c00a82c1c4c01602c6424501c00060780100520100d0710503d074032683c82cce144c240250445804848601c0c15034001003000c00c051040400048000104003170112074800c1500c0100901e0701080e04441c41880c07a100780070403607007040c030010400d44200741c0326044681e83e22020400ca0100311140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 977479379 1250 977478129 977478133
    0x70b0f01060e013b090108100b0d0506190f15031b06120903050f030c090a0801050114210a23070f0e1003140601092318070e0f070818 59
    0xc450800341000006984c0c040c1007400d41c107802c03020200003148040b00781c21401c0e494021801c2d41c0c414114500c10368103040c40c207079035050741d1400c507444d00ca413334810081c40b0401440c65248000c0540940303a2004100b207100c08000c000b0300d140500c2140c0c440032680002c5400c14035030b240344c0034500d40005083c0101c2e403866445025034400015010080c00e070480c412411b02c1014081c60401141200c0a036102e640201c0b80c0382e407030b04502d030300304440030740030394000703191030b4500001440306c84080207009d68000000e99185d00300c0030700922085040b42c012080d403411405503c20400800020030024269031071070700c0741c10b89400e41d00c030900d41d10b880c8180702d51400d4900078082000a50420018554004001000c01c1c105aa50b030311003c18800da20b80455405401100040c482c0458600c84c042808040c140310918020944000720208103000e03107139025020220548101414080281e4006082999503090b118240b0780128143c400064400b000070601074800102880c003800d480040425103980 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 977480629 1250 977479379 977479427
    0x408010b120a020a060e01170c070c060f0e04050606040b0d05100501030e150903090901090b01090b0301030201051215041d060c070222091e050d0929070b0f01060e01 73
    0x174103451400030014100d061140065a18004540d030307421051280320307825400303651340449107000c00040d082c54200c003042c0a00441020740f0320b5440904901c80c510306580000f01515403000080150003190311280d104000007403c5001481c403a00f1190294000c882c03402c100f20384440042d815070b8081d800380b240550204001070020440800340f5030b00b11801c0300c180ca28020401001c02c8000b1004d800c0440000c0d10b0308822010f559000b070302080107004200c40c0d00d0446d415680020034a104070f154440b01c0204141c0407034904e01100c6006408560000d204004503000041121401000381c0001c031880d014031000030f0410300141e002c0302c50180c3d00901d460048a4542a030402040d0480c8030003100c289e40e0f016100018003030792100c4030f844407a00320003901401a480e06a18110380303032602c442003203000d480422941860501c40380c6400084400d07600b640044501d540150b01800c0809805021a1005d018140101401d81410f03141a507030341c10328072202c0c0c03001902d8204051304003442102e142c103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 977481879 1250 977480629 977480639
    0xf0b0609030307080310050d1415100504020702040e010507120501360e1f0f09260d0f1407020a0b04170d0906240503030702060f0f0408010b120a020a 66
    0x41c000e55010241048a07140076413200040361a40b4450b5000f114541c0c00649e8800414104000400400102d45004100c0b0714214000c086060030324401e55001d43d4011400d0021551180c1005501c52076040c0200041c0c540035400414004c00342c952050f11610f00780010400070390150050f042c645000c0c100740c4c0303107140399502d061b00c0601d885025007000e80d544074104041101404105100d401c200c0001107003002c2a85000219140002420842c81c0741c403014200003070120031552480d101c8540e001003c650a02c2501c1514407502e11f40e801520716003030769400d4440e541d9022020800502c6602c8150343d03204502640d450307031002c402900c511403807000980080c2c0e0b01c100725200c403620402d0a90514904581d04029034680c2c1d003084030000c0d100c1e44603080c0c02e0813103406440c881040139110740303c051824000c2030300d911071405c002c4e0007504002404403864034418104d0702e2a0004034182c0740d4950b42c034055640281458128284500c0c80c510411007119000a419014990020312010096247c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 977483129 1250 977481879 977481893
    0x1e02090f030610261b09060108040b04030f031815060b0a08011223070e070507020a030b070e0607050c010212041805090c04090c1403031306080a02090d060f0b0609030307 75
    0x1e071030021013040d80d802074041c805206000750b1000308100c06140c0801c40e100030400c5004140205400c0c1081214010400450940ac030100d8010b5014100394442c103051a20807809800300080e840300c9480b060840700308008807040401d2400100300010851300b82c94070581c11035403080c0c00d0500c000919200040c802c1e401c0c5a4580384040b403080003940f0140e03508154200c201c01421034541e140c0d4100190400030380b9a50701c20f5a40c040c1c050b203402450210150700003040d1400d41d0001a10b541f0781340000514075406050100b026000c0100146c4d00c50100d031a165546610710f65445006000746171404041603c810706660030b80d004240301c1036040d94600c010b000185002070a4804501c41c2540d01c0c4c00d80e840d1441040c45080c014042c80f400982003400d1840c8001441d0915806a03204200e43c440620101d43c11500382c80442c58000c0c040d4442c3e25500700079010701801036620041c88031611b000c020642d440391011500d002420300c50b0209a03020040c1c140945184a5010382003001848006802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 977484379 1250 977483129 977483159
    0x30209040f050a020711040c02030a051308070b070c06021204050d0606031401090b011203090e040515070302090306090706020712020415060203031b0a211e02090f030610 75
    0x35200103540158041400706492003034442d4160075900040c40e10a2003500c007000c8680700b00c241e909012045041500135903034810094084204031020501c1c10040a246408000a092803000c40d054103885103140300180c4c1c02010100c56450034040c002600071300100b188041003485200b2141898a80b20510465a4401c0800c64603159036103c0480060060484e980d207100208000044607000c510346048034003810f8110240b16500c01000500003540561108155071442c40800441e480700e14080c2d240c4100400f844040b4000d00081000050707256000d4141c02d101202112040e48400f1481a1111014000c2170010303005404203000000f10040045070302d62028000044000180d000268491460f410846c010307040007090100c828048441d03c03243d0500804282d00d40950f800000d041580c0340c1000b4009600c40310717106901080d4544c40304040300c0100d810503003044494101d200080d40010390b900d200d41c0707164000d040f040c10005440c9210b80242a0780d06241d5082c601d200704041c0c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 977485629 1250 977484379 977484397
    0x6020304140607180e0c07141f02120f060d12110a06060f05270601050c01021b100606051c06050307030506041a0c0313020a05030a0803010503060a060608070302 71
    0x10788416816550408120441c820820350340c0c0d5000ea00b0070359000d202c001074598020358100440030f0500040070000c0080350750317076540041500c05c45000b0b641c940d4282526070320a20502c00c0c880e0004075a1220310b4004050803e6104d41d20403007640e4001f189040e010301558402e401240d00688070001523480c000601002d140d90800407800d03c0343c1d1680c1132800702c000d074040b01d0850700d503c403c011a00e070101c90900a0f00c41180c1030b041c082065524020190304070b50011442c200d04001090307641e4010030840b078030590340000a40d600e444182880070b1500010705c1d448a907124402d14184007820034801e0a00ba100c10340d80d01850284280e008820304650641c188000e65500e03180080c65580800c400c00085204c0e1019003000d1400c0c0c10102c0f041e00440c0f02a490018268041001c81f0b1855803c030399104442c9030100c062982c160010407825162038002d650144a03015118041c0b080000145048800172422078807030f96254101841565070501c903030004510b203c0c0c08902d0365030190f0041c00d840c00f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 977486879 1250 977485629 977485643
    0x1e171e060f15070c03050c1512040c030c0311030625030506060412051b040207020d081e03010906080c060403051c170a09110f100e0d0b04140d080702060406020304 72
    0x20b914010b03039050700e5005410480f00340180640400800000f40091041d4040440d042000481c2c41b102e2a0f00d5845a11500460440c505000800b005030307200030680a10307044010300424075141d02e440700d001080c07004490b100c1d2140390700085904626500340c3c510795a040103c00701c40c1d03138907040a40191802078051039014005000100c0c000301044441d03d81c840c010801841c03039410040640c13843ca034080392068000e6004000300005600c640c1c2c0e540e030b0724580c0464440c0e5030f207610040c0c60382180070b00707403901c002c80200000009041c032a682040c0c0540b1021400d07140c0c4a0b070200200580c07481207110060680e0021440b0002098030026000000316040c2400000d800b88811100b00701802150420446641e03400d8810501c0b0329840010000341c0c041d100b0301a4001c85400040c0f2458006010b501013040070460708101c1d03102e901e0314101c40342d44202c50344402e040503c0c20314031051511040a40500c034001000017000d20610005000c0c0510b90040c100f00e450350384078040a0b60000708242c03040c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 977488129 1250 977486879 977486899
    0x60e0120090f0d120302070308070801050d0305220e06030709141b0c010c030c121e1109030102070c05190308071b05030a15050108070f12031e171e060f 67
    0x803d04c050707198200010584d50050351ba006519000c0d12040b4003030200403c00c85d0150041c480ca40300c81c0101002c4a8141c01d025482d0900105080392000c88980e44812a1882400005404560421060044400300c00780c8044544440ba0442203c0f1041c58000c801001c14001c0313460b05407444125180c01801140c1507192a1240700000e0030344004003c10000aa0344868807910a81d1003200078040e804009028011405c51a04104440a005898042440e034540f0302c618414943c800302c900110015000355200c40e55418486103a02e1144201c6004080d00d02c00c0480c01003800b80300e8820359501c103580c9401c207209074442c4a10b6043d1000744842c1c21040388400301d1760f60303020070544141a2050380e140380040c1e0b09204103816944180d015032110350082101b8052803240490031400d072500426141c0a006071414222901040e0782d4030700303c0e802000c140c1240d54030360151508880c0e8042c000d038440585ca030390b030320b101021201607000c141010140b004200c02e482c0900441c564014002c0c114088 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 977489379 1250 977488129 977488133
    0x1e040b06130e15010206070e0307080d110105010519060c020f0405340219081e040f0e191d010f09021e090619090207060e0120090f0d 59
    0x180e030001580c00301c0d00040032000c005544a0540302d960005022035550701681403240040d550341806404031091001e040c010380074603242044414000d0a520003121800b0942d00c101030030751310507030b8040e400a5080400126103810490310f1071034a19141c4520070340607450074030200e40508000c64100d0740804207502040322a0340d5402030341d020343c641c3c100c00c41c0700d5441c01ea4a176026030000d01c21040451071041c018840c880d0040303407250b00e1100c42d519402d031141c1d6a1070402420f2182d11000010040180b50340414030008001900640d140c07802e030040ca450701c800c0b07810165401220011040c3c12600051240340342107801c01c8224031100407243e030329141e0003803070503007510100c1d5070120030240c0d0750f00940103510303008003880c001700700801c10200360015010200d000c800b00102424043c480d0f00048a14030000c5489560080040580440d2a096a450311602401302c92030140c41d10740c2080d95691042c1c05164505019041119200f071038400c0c100e09110402070045001903220300e0781c400e0440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 977490629 1250 977489379 977489389
    0x5160507090b090a050408090f01030b06031501021504050d0c0303150623030103050307021207030606080304151d100c02041d01060e012114030a0c0302070605091e040b 74
    0x58850654041140340b000014010080002081510100c1c181410700020903e0b0000701e0710481d00030780301034a0342101a00180d0103002e0030b01c00e5a40001001080290313080c503034400703c0400b1009a094440c098440f400d0200742c0c07281910050403d805c640305001201707009040e130030b40ea94031900b808a11205040d030a00c7c0d0419555116001080c0002031f0b503e00b82e0407001506101d6500e0000203415035041d0f440d030b15903a0040c090028020564074100c45003a00e0200310860003550302090070710500e510761003060b40702d400605c0b0b24020301c200360803440c0f03069000e03c041595402c2410140010310120f0400c018005024496000911808034665005600d950282c664090081c10202c114500100503807401c41d02143e0106c0c0401d0016401032000e0400da9501000d64418500d1503000c180050500300c4c1c001d013404480404510000404288040e00040c4281815001e5000d8607020381d52004181c5c0d01d403103803142459001c500380c00513400701c81c084900001c6401000c1d00000b071096482c000310b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 977491879 1250 977490629 977490643
    0xd05042306190207050301020403150b0a1e061704020f010e1f091503020a050f340209010e011d04080c03030717060a060e0409020d02061908130b07051605 68
    0x201d0488481000310056010840513008140a80c021481d040c51501d4403070840346520070341100142c41e140c0c081c0407640c0c1c20800c200508114500e0b004140007680108420300d03214480c50000c981a44003500c0503c8004210034452900600080380c0401003e00449055a01048003540581c47c03100003c01d190040750f00301100d001c0c0c0c0c0c0341c40c42c8003400e20307500c0010100e182c02c2440c10180100180c0c4030320340d8000e040d295400c106c0c40f066034035180603131486100e504040c584800c0d01d0515410558401400c40c12035a200e6000342c422550990721444008041d071340174000d00b00380d60700700e241703070030900c0740301c0c2071103648079000f6010507040c00c03400788c0410300311341c0255850310003d0400140c444110041c9280f26400c21801c03110030922501e80b00d809004580140e1207075201c1d40d41d4001180964175004544040f107a80200015a6084052001400064541905000a031030040010040d50400400d0f405e0741d5007159040c0c40965481808855685c07100001c00100f000c1035903210001a0200811 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 977493129 1250 977491879 977491897
    0x905010c03090209010b042411010504031d0916050919060810066309051e10170a03030c050a0909111309020901030e0d05042306 57
    0x700e045949401008107000c0d0607042101d420030100010041e00d42654600218122200000b01c023986100308280c03118010014a140c0c19400c1c601000101640110074aa000c03040c0348110b0a20404901400b800e01412146d0380009186400d8100d0300d1070183e0050078580038001c000304e0142d84c96400202038450203a04c6500441c62540a10240803100031003400a00400d1030144d072103003042c5a0701103480050882002804508207480e0712020141c81c141c0a4250308040c4000506c1900c0c0c018080c419625042402401401c61020a1040c01c40c09071070700542c22400c506200150400c2100d04480000d0900d176003189132032200103010591020003a4440041c803000d00504e107520700b800707400c2c0c0d921040070004110040003080b40fa150400542e90680c0c506c0c04000400181d128802c00c01d81c442c0d00ad1400e4a458020300c0080c51401383e40060ac2e14040c01e84e42441940d00c9804601d5032a007550a44001144d000c0c8401d114071886121103548a281101c000d00c480b40e61440840c1e12541301e040c0d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 977494379 1250 977493129 977493131
    0x60513061b110d0c0206090109031a09010b010509091b1c020307120509030d0e01060909050a1506060c0803070201021215010311040f031113021909051e0409060905010c03 75
    0x10034509401c10102c0412641d054094551414040700c002c0180e2690000288102e0010440c561103074414883e00e400b85034490908000c0404000c0002040b09041b01c1c00b06580d8217280b10009694460010384003c540040d007003441c039440340202503503082c0c6c104411980f200018842d00107c0386800f2104e858000c50300f00d0050380c0e810001402000c80b6400d698445405003448280103800700c0000c11100d800401070000030b52209024042405800158032411040d03084c01050414000c011403d40c00c038a10445031031240300800e11880702903606510400000c901c00352150008104400000c650000c0c49c0e100051400200c4c51070407001240c240e540c03424000c11041d00450650301841009c0451840c0b07a071407400e1030314199400e00a040c8501000b40a2200010109800e0701e0b440c2c10304070440d907544019503ca141003a0001507101d100e10b52540007541d8440002141d05018904030100c2c184200541c52040440c010310010781410a0110340369607896225101042c800c1c41044132401040c3c5e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 977495629 1250 977494379 977494421
    0x80d02100e0a0506190e03030402010903060902011806090501080906070f0f0c050703060f050f16052a1f0c020d2f070501020706031503021011010908190c03020a06051306 75
    0x1403c1040302c4d1415031b000441d40c401c00600000d0707a0096010b0b81100d60292020074100e00f94801251103822a9894a041c00ea169601103405604407800a0a0b40e1003a03a41d60410b40e50b0302d0280d940c400c8180c400401240041c544480030318032030014890340259500f401e178003015a66940d189000c0d1158016a89256107002c2c45203404918090180c0040440c0b070f07021028249144403c821200300c584d01c50600c000051511850ba801d0321020780c8080da0f0034408014400400030054884075140c401d0f0700042600c0344880d0245070b00d0b1150707500d800740c107500034408040680d805a0301c64000e1a82100860408a01255240950101040c010b10108081c100c050b2900001910b4032400790080340905040140b284034042691620208a940440e442a96000404402d59003000c00c0c0540b078030f442d4241122541808522002410f4040501010700040e1404100071260840070010060040c3c10240041c00030403541d410058004803884480c100500c02551740100302d9041902510750889800c2c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 977496879 1250 977495629 977495671
    0x1620010213050301050402210705031518120d1a060a030b130605060f09040207023d080a0c1806030902040c180303030f020f030109050f01080d02100e0a0506 69
    0x1e11220020031054009100600301a80001c04000701c150300c1351f18442c0c00f12850795800c0d500300044001080d010303050320560000910380c410349c204c2c1210f5007113000c0420080520381020004e00025078001076a420f0342446200301018016040350b01c00c4001c204a0203440507410340c0d46000a1410a40070b880c00a2007007081c100f0302c40100850940e040c00b50f807400e0300030405030300d0380c0085488000401d40407036555002100064000d02450101a401103101280203d610908651110700d82d902c0070340e0010300c1c16503481c141806070385c4072100c040058001008103c43e07900d030350844c10340a041c40c01d0101607100c00240c0001e2034800b80d80b0040010b9215121041035041c0361040d0b030341c0522a071401d410001d034541c80c071040d003480512000741059660161001482083e9043d6504002c0c01c000e66580c2e56500c55102c8050a41a294560751070880000007401d02c2d0002890702c1c0000140e00038120754500e81e60808010010a50b98031104c0c003900e40c010002420030f101c0a841142603c0c50325508510b80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 977498129 1250 977496879 977496907
    0x70c030c0816212405011e081c0503070c02090702030a121107080f0409020714011d07170c04060b1b0a170702040b0a030b0a0e1516200102 61
    0x5501c034101640d0f080c80d03e5600003540241c03042c2240c3d000500c50000381000138968141121202c203803680d4a00c0c0c6030000c501c0940c6081000503203016139101070241511002c201d44c660224110070300e2085842280d00d40a00d015001446d4001c1440c2004c0c001650300350082408458100c406000507040002c8a5042a801441339401c1511840041020048400c21101c1c148240c007030103001e124000c07542e807400c6d9916a088030f0207002015420741d02c030f0406180c8a802c43c9400180c0c182c495007440c00c0362100410740000000003082ca14003c041e218684110300d00340242d054201c1c1c1a034051981d000005864a02a1038002e201d014034072541d5445040103000b0000d01040707111120340014948102040d061000c61005941c80b003401c0d5600c3c495440020000d0582d61030076034008450708030002c180036280d2407051080d400340f80c040c08526040c0007070a440c1c481081243d000807250b40c0200b60f8014030820080180406801c0c803883c48411030716620341e102884103c440c2d21341c1d00001c00d404980d0003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 977499379 1250 977498129 977498173
    0x1f0c0306060c0b0c1b0a0c0306050c091f0207031e0221120a091d070e04090503030417091305060f010c080d0f2405091608010b070c030c08 61
    0x6890600250807650b541c0c14000034000d009a0021a00440ca00d076041c686403880c1c400c114500d05c202c9200400c03601d006040c144140c0f1066074080d00d800300080d40d0703030208000c951500000402070a040c00c9049502c0001c581d4580400c01103100c1d4800c04400100354a600b0b0880d0071031000182d8103460300e4810031124001110856192400081980021441c0040c50918010624006945070074034600110785080d042e0703125040d200214207070103040b600d000012501640c02c1e1b84d00c0761450341040301840180c5000310780c0107000ba4800c00c0003074040f03a14400d2070203941c0d00c0401c2c0146010303000000203204420000140305001d944005001051801c10700605800f402820681c504181c04c2d140c00305540070300c05c001c950003510707030b110070070480c1c0194840780d2829402c09100e4400c5c003101202814460b2a4040e55002e003c04002141a404001d02c045840540039906d01d00c2513801d2002c500081e03000030000301c401034240700d4044001403400003040050704800e401441c041000000141018078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 977500629 1250 977499379 977499389
    0x2010f0e13022d0a0f03110d0f0e060c0a080c0909090d0201050703090c05010c0c05101106011d01061409090103060c0f0c051e030c03040603020c0d0302030c0406111f0c0306 76
    0x8a080c54002907400c0c0005680101103d42065a68108128000e46c080c01418801c2d0300c00000000720692042c0b00da60040062400b074400c20030141d0700482001741c1d1044183c07902da401120030301003408140e119002c680d506c121120003050400c024400030660048041d00c0104450700120303610290307d942441140d600c4007562505018140c0151203001440045d806070504000d0103404201c1485004224100103041c05000d80d8541518460000c00c0c00d80022107002c405e00400000240c40c480744500e04140c48a411004040c592038110700b0b4505500c00090f0344a00350381800920040d60704c200225000b907000301d501140804074040010320311481903c0d100188101c80d140302d8007160380000c402d00c018003c2044013417042d0595091502d18003460702e61803030603c4005004145c2d1a850340181002901e09000c9880003603540c201178060740801c403001c0040e03403020300003041454072603070f2032440c0384456105a41c26564028130085100318801c00040409459400c60044254188100700081c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 977501879 1250 977500629 977500687
    0x80f13120f14071d0601020a050f010b15040803040b030910230106030504050a080a0c050715020f060135010c20010b0a1a13061101110301080a02010f0e1302 69
    0x34189420310407042c03050380e82e10513151a030100040711a4000c00c6100b20458100084511000c0a4160f69000e03200c0d0b4209207000e4002103c0d007038402c160050603102a185010051030509041105ca0310f010342004112400510410f882d8400d20b01d080c0c442c2480319406168100b403080800c0940c0d0f41618410390044d0f080614010400001c0ba0010449038455030780719440541c0d4840b009402c41d251f01101c08003a1050003947d40024101140c00f0b49075444110603025507008540d0f960385a9182c0034240302c0c0000d03180b08030808400342009a022040c176805c1c05030003401c802503002c0519084130503980c0030401150458184807540c00108140800740c132507440007848412043c0000c510f4031195403203140040c1042d02c4414884210801c140c60710f1900c40001100ca40c0d50380d1034010020b40c1d43c070b03050000c6546403955100d140000141207074181c4840c3c1c0006c24642c4007550046450303103401a106401c0021607048080c032552068034000f1109141000561140036403403120540308240e40128500c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 977503129 1250 977501879 977501893
    0x5340b040815040c090e013204110d0605090606090115050a12023006030a110105091306171b0f0108040c030f0807060c0c080f13120f14 60
    0x507403400591840a4907151200c2d01c1e058441c2d181c02c42c0c0201140e00300d1a002402c18076449603080381503010020355034003514029a100b00711a030482540703d00d003442c00f640006240024006c12020700044c2d4001c8170107000004104242d031989011500700342d810a060760003560902550b0b24103281400d0140100c0d0340034499410030303000d0207400d07442442d05c1c00d4244581002c018903415090390503283e580c1d000014158800b81302c2c03541c030002c200d50241c120b540d030308440c0301003240d904001443c030741500e51022070708140e2981d8400560f000d802c5800300d01e84c07103694041171411640701c0e800350a0080410100d00726000c0c640ca101c003403d145041700400d0509440c4e40d0b201d800d07583c070181c002c0000c2c0000c0c200782d02181c450b400c02d0344020605400180030755892141c1c5008005034007004014850090100300103600103640110b40c0058640d070041d01802c3c060082007a001881e000030072031819092266030106a868159464444207480241c039403001c01c8110500748103821003d4203018248001522038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 977504379 1250 977503129 977503139
    0xf0f090e0a0c12060f15110613060b040c080702070b2703030d020309070e0a0b10050c0124260303071d13050411100c02090405340b04 59
    0xc100801101055444000714075896000d000310443c000146035003070213aa40c4031a22010740469500c00c080e60000c400d01025016032007a4800126503001001611007610340764035280c1000c0c500c00c0c0c191140d0ba95074940304060340e518841c6406004c00c9481b039070200e141040700030f400e01c50958032508880c202004030080a40030000c641e089104003030082038003c015640132030700d18001c956038046490301c00014010311080c002008800c980340b540e500c60350303031b6a0b862001307041c1d804040c00300da0030000021114118a00810217080c42000079070000070b504040f03031501d040c00511650b1071580d9600301281405034015290303452140103080041050758085051040382c0c0d070302c002815035040144007202005000c1040030400c02ea00f20040c40444200007900d42d14000b08801c0d00e084801c41120045083c0609221040d4200090320307840300100301c80a40c00740300c802d00b4018000c0320359005515480e030180380041401244451030915100340c8071680b01c1140410b4003982c00825041d0418041001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 977505629 1250 977504379 977504399
    0x901090312020a171206010306030f0b0402060c0a03030209090c0c0a0f0515010e09010c02010606050f07050c04050f040c1a0405040914071806050d0305030f1003080304030f0f09 78
    0x40301e500011508565440d2101241807100000b40248003003240018071090004e0070026000700401140804003a461303043c01503041b503456100081050389040b1100700881d10711840181d00c90700282082e483c00c20070b030b1281d50501607000c408902103503000c0340014503428198a050342c0459204021403030505042c0c21707035543d41c0c440400281070781e00d06071402040080602c0070240410175580c881c4d00b5942c43e41d40c1c01d04424411100b03035550350300e00500039201e0b503c140110001c03070f61151525444d02c40c00784142c040650002c1d1040e02c461091021412064503940700f501c1c80340481d00ca180701541018078100058010a030300c001e110f840850140d821480e4240b0482c1c0458108030741c000354030205450080c0c401203c20503604428010904e00044031800c5480711644400042c601b00300c800e0b100c3c8100482042c081e60040c00040c800e2001070342d4401c56a11841d000702818540901c515942d950315105540216411400280a070f1514032010340c00040d48894513509040c0f86441c2824200303492 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 977506879 1250 977505629 977505647
    0x906030c09090a081602010219170c1203070e0a0f0515091c11010201150e0610020a06020406120e1c0e0d02031c180f0506070611070606080d050901 65
    0x10388900000408209184001c015441000ba070015030a03031201700b06800d034142c11407002d000307a0150145110b03241303500d403104079100c101c41e40c00407402480a00e6500080280d8000e803400341000e2007001019039080858101541c4078604035a980c03026220440d06002d010011355201c8103184c00c42c42028801699a0340c4d000d032445e0094025151030304203001c0041c503800d800240002c031801818004c2ca046c0004460b148501c480c00380c00034007281016008031510f08600c1d1240720344036250100491124074041010061290080c4121216008075860b090200d90003944002c3c046110b1103040780e480aa580100c5440e03946005c00b4140d2410303070405080000c0704080e280306c04c00402d10301411032a9103070070b4880d0040343c01500729560384c2c00d220003200e104d158400e8500c4c0414200b081c90b40c40020b90940c81020f480c60b0350070300081d4610b04000d01030647c00c1110100c800d15202d4141052444010001e44542400b401c000310f49585041c003a02c2c2004e8034075024000b0014104942101c0703980100d210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 977508129 1250 977506879 977506903
    0x6030c18050d030e090f0a181703100e0a0c140a0819020f04091d0106050d0b04060f050403020d0e01140421050d0f080f0f0f060a0512010f0605090603 66
    0x5504118919044550005402d584c5a0100c510700a010700c801e002c0b01814420110403404000310f034034511040041154980008111240202d0005401c50b0014065500301054620408441d07442e1944c40e129003100301c644c500103a640340c54454140c2e500595011014811201f0545410b40040e0004c040c1c0000500c45c8881c0e003c9171b0400385041825504071b828114611020a4403503480d030030b0410142c4070b0316440c81c030b1498010200007000700040c404c203800c0f01c00060500e00c0521080d42d17901c1b0000c030004e0050721026607403281001c106105002d00362156100c0d40c05011210455000070704501c1455000c0703030410252100105842e1030540840707040d6040f0f0352041410340c02a950440710380d090804000e1503402180384074446035402c80e0004005c01034548440c1500d5039081160302d1518000c455090296910f4004220320740508515590843c00c043c000346c503003a4035400030500e09821200c0f4001640e5581440a000289503c13500c0042d00301110803c0e02820050f001075904c404072406 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 977509379 1250 977508129 977508139
    0x305090d0c0f08070f0f050d02012a030c14120a110304080304030b0915091b01031808040f0911090105090109030f080a0f0f1205100b0408060106030c1805 68
    0xc55400d0003800069100100030446120710b41584401041da100d4680348604415107020140101e0140381107004ca0090311000b4018420507c403a4004640600c2000b148411580700a01034140e05100e42032030705034881c044e454000140280d0315010141d40030b1503443c400c2c9500b0041c11000c466007503104aa90000320b6283c0300010120400303081c2d0451250381c7c01364030a4400090004100f1484843c4944035407004016110140080180c90b15501412207060400d40c000ad032480e0305d0b0011100c0a241c2c0703040c06240000d00040300c003960505080e2120802e458001d4080b07410040003841078100c9018150381e5105011040c101c28000e43c407402200340b1181405008a40700c2c0080c2d1003114010300440d085010a03080d84110b041036440c55100000610004d5006103040910502585600303070000c038186c1d01c0505000740c2146010003004054054800d0100341c9030005050013000000d040030340241005883d03503515242d0042d00300c41d5051241800c2c0195909940041c06c81000705504461060700c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 977510629 1250 977509379 977509399
    0xa0305090402040f1403010605060c070501031505042307020c030a1514040f0317040209150f0303070308061e0108010e0901061208070c090204080309010e0d050715020d080103030509 80
    0x940030f805a40c1064480754900d201c002008060b00d405030480b010160000c02c0300544a07028040948102a42c2c031589a2000108000d40d5129600441d9020030a4a9610b415601ca800040c241c8204400040e00910195460410b407581c0c4040c0d2070b000384d80382c00140a90307869a00480e84071800b150340500025845000341001d004070707030801070404842d2298802c25190a10b01064000780b44441580092030204040c520f449030541524080c5400402c4816640c0c2d81c1c01161400b800c002002300d40002e00e0041480c1940c800300003800c1d89600c25103605082c1d1400c042409980c110543c0f0310b0a000300720031545003907641c2060a41e81234442c4699a03100b070741d540c403003001d01502680c1d0011fa01c0100361a03580d414000070001411b01d00d403140100000096660811505030300450150381d030107800411000c9003941c001c01d40c6c6000c41d880580f92010701119601c0700c900342107556000840587c40030310240826175060288000080d12420302c0f40c669415030b21300608901840b00a1405529654 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 977511879 1250 977510629 977510647
    0x8090402040302281d0c1b06010b1c05072f0a060c0807020106060e0d0c0e0108030307080708040c03020108090f010e030a03060512030a0810030804060c0213020c0a0305 74
    0xe011070380a036801900d5141d00d114040c041803555149552114078030309114601040c250340074036010070307001500c41c000501521030306100081c547c041d01f00c19048001080358406134003c18850a1b00800d0a2911540c0310440c042480c0e20849024944002c0c0500e030008200740c0230b40120862400100409401d000301c1000b01c0d280c2c421144c59441c00846100b0101e0140401c01c194008001c0d5942556070540c65403144042030b4260b0300240900d00103d207a0b84080603a604041700012001c9024500400a587d078811102154010a8014003082d420001c1000b545640103000650000000c3c54014000c0c42c16440700c003900c1c0310300c1c08000d040040ca0fa0110311980070400108000c0811300000b04000030815800c070356294045488030001c00c0c10000001402c1c5007141c180c600c0b44010002461602245000464030b04000a105010007800c0c00d4010001c40c00e00400303840503160503160518045094010095030b0180000c14080c2c00d801040744800140c0d0109260f0100d42d418100503880d80911 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 977513129 1250 977511879 977511881
    0x209010e2e090e1f090206070507140414161103040b13050f03030a0e1005040e0a05060307080d05220f17070b09030a0b040312151e081b0103090605010801020304060b0a050d080904 79
    0x4000050027500c55002d000c00c4070b8100600030010f46000b140c0801402404002260450104440c4032440700c01040e01001d410380528080071103401c0341f0382524a403a0300c0701240c20700c5400012101086d603941000a00146c101440f6600d480c0c01c0c21070080d030030940150801450041d10450b054060051071841c040c50701d0048050f200035041d007044120380391408160b481300600c03080b00ca2070703c40e22503448006603152000c1503002c00d080a582e02c1c58502401c400c01c11000100b0b003190a42010300c5480001141e00300c001c121409401d2403e004180c40c01800c21440c5040d0705604680c000b240200110b04440d600080c00c0004a139000c0410043d0303030b40e28201034460445234011885000d041000c14803424103203010080540d068130909502d40e007488540c01e14020007500511034141e2004050505036000c0111038280402e05243c040340d010720710b6070b501d0705481003030b400034400d81e40110030300c010000c1c2d40c01851070655007070b1441c8682520386400102903114a4001606080c40003a4200b496295 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 977514379 1250 977513129 977513137
    0x1c0309060504061b09080a060209030a0f050a0c050916081e010f030201021011040e220c06020d0f12090f0c060509120a0209010e2e090e1f090206 64
    0x4100200100c2c900341c1001000390130b02000310141c40c40144112008107000f01c810005496903017005007113042c402c6d80c1c0c0b14000d5002000541d41440362444200000d01e07604d0342c1e074416030f00c198040e00340ca058500d403e460381182600b0441c8680341705010009807440d0381c50007a00071183c2d1314020900b41c50b01d201c0d0034800f028180b1114030540001d40080b4140e00080c104404480c03003070f401c507441d00c103000d403c80301101c4200c415100244001c03c4100009500300150a8010002d0341d840210160580b0242e241d249540c40100e6078100b025100b0010180c040c05416968426804c21070866500c01c4402000a01c0910b40181e0140d43c0e01c03119403d100b20012089109030340000c19400c01034444070041d1154000308000d91080d503900341103050142d804510b841409601900c0c40a280c0d09140c4054a4654020701d9440480c0003d400c1e4007050035031602008070b6a044582c2125294203007000c0700142d40502200003002d5000508056408120400c40c2ca85542c2001002a495030944000383c5540700d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 977515629 1250 977514379 977514383
    0x42003060114030d0804020904111c0302060403030b10020717120c060105090c04210305070b15090702010626030906030702010507080a0903020d0f020f121c0203091c0309 75
    0xc03450002181d541265071a80c40e5205040b011107480c1c03824a90205c1d2080e00854000350004034200128000441d100009203400713900401002140500d1028810820100d940960060344428140414150148142d088600d81681c5864150401100c0a90340301006d110b0b81c207481584e2205c00c0003515041c00a000e100381c06566041e60b80100b9075060b60b8a86082c0103451041c20742501081200d010f04040320b084400d8500c0d00c028080c5001204801c000003050300740c1c103001042058000080c20035004902c40e0541e00c0c032050044c25441c041c0524540300500e460f00b5685040c005100450300c1c2c2c01009a07404600818a003001800b04a041c00c5001e8440419001007005c0244028950103412544c0302d00c5865842d82d07070300c0d95110014019101091000342c056003140d079000b040f00b4454007540c40343d4075003130044410042c03c80306100d10b03241a41078081c54120001c142140140c44d480070030070786a000032500790300314200208001d40310903064400c40b01440350703d2110080f8600903003260103415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 977516879 1250 977515629 977515633
    0x8041202070f03030315080f07121104090b04050c01030507020c0d0f0206130801180b0601230c010207031e0f0503040501151701180c05010c0501020f030a020a020706020106030b042003 81
    0xb5070f9034507000d000b03400c950100d03400c4140c10141c045000c4a00044024060400c0001001e4161400c42d800d502826890300683e0300a0140c4002c20447d00c0b00d0049116852042d041042540b078141003c81c01c0005052a00c0e0406051800740114241d0000c1c0706205401e0494002c0b1a9002c6440c09842c2c10320300e110003d40040c00403d54402100340d4010210445010300020320170400c1c1940c17010340001050800804458140c00460318951103456150010100546901e0714803001c0440341040384c00495079102603a40003c1c1c0326040540c01015244002141b082075002000980c10203800c0f502c05500720703400c110001c00080c0c18008250800781251519261030404c20352580003001c0050700e6001688055820a124610fa29202003d0046d50035001504030042c28107000044400b03c0048005440640d028001001140d012074000c0d4000c00619000580e16404000068244009a07019000b964034106080010a03991402d06611660025185039031100e40c500301100d00d0480d00c0015014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 977517985 1106 977516879 977516909
    0x50715110703082706030f0417030a2315060a02120433050712110a03020c2b081803120d06050a060804120207 49
    0x414403840e165410190030350000d45024201d4005603042140000c0801c562401c00800310a040300803200f254061850400044290000400c44000070001800040401598440150382c0c044554052a143e081881c00600104003000070358107106148a060f00e103810828140038803441c200341540706007003030200902c500c6410840c1480190f1042c03540501d00250340b400034101030104042035a0a241c160100390301010000036104608904480c04502d1b0994044104c1d221240c100ba4540c00004a1840031201c140031503680341c00b24001d41d10343d44101a40800e240140386000c45882000d0081140b1502a43d903039891042c41503203088202c100011308000c09898800203040c565039070b80c0d08d4880400c1c24110740b09906110703000300180306640d2907501c1c82801c01810381907a110804c541003070409003920101410240812000c3c1429145e040d10810809001d05001ca45010702 = true := by decide +kernel

theorem cover : BRFrame.Cov 977338129 977517985 := by
  have h0 := BRFrame.cov_init 977338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 977338129 ≤ n) (h2 : n < 977517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
