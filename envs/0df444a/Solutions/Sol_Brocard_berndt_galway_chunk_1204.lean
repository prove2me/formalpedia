-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1204
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:44:55.101639+00:00
-- url     : https://prove2.me/submissions/86dba734-28a9-4c6f-99be-940b4bc4ed3a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 216366906 ≤ n < 216546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 216368156 1250 216366906 216366937
    0x10c02061501270b03010302011d010903030e010c050a08090102010b150d11120f063f011506030b0a090209030a060b03031b01150923040303140406150b030c 69
    0x10302103d40300010f840b02002510451203a00010068200002103050761b00030399500400c0c404140d400810103c810449a0020300e0412080011a01c980000b442c0d060052500400a03011900c1341c514080b041141590346038400100c0e2000da42c0c09100d20140c4c5a82038070821114507010010700c3d20740c09002d1043c443d003502e5100c144003000c0140202e641d405501400000c00d03042059003e003046c60b086803168054a90b0895196500094030701d46140c5a000c1020f504845014502000240062941118042d9200e0320a01070a0362044200000b400072940c0004d03a04170030000300807180e000390740314032130f060300c1040040d2590b14007040c44003940c0c3e04a20040351142ca060301091031842101480c904014402131802001c11043d045101c03445260703100c0f00e0340651102104d03021a114110502940d40a803d90501044a4400c14551250203428001500803240015481184040360121180350b5226111900c0d440400e102d8806000d03050345080c29442d10f20354030383c941c0c8540185801c0525 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 216369406 1250 216368156 216368177
    0x605090c0f0a0c12050711010503090a060b0d2306010b0708030f04030c05030406020312060315040f0c051f0f0806130213030203010906140f07050a0c020f0307080708010c02061501 79
    0x602880c243e86a031036000584003580854140b004000e03411010003187e036030f420b080040c06250312034010799014141a00c05050f0501c9656510401040e400c01c1c03153b004802c0400c00c5021a00404440794003082c50141c01005034005131f44241450340580040d481c0a0003032100c800441d00d10030549600600140715080035860380c0c2003c4d950714651480c010b220344000a008591a94084040d00e9159081d4a4294843e01e4040805413201881411150300318842c90000e0040764201c040d00ac00640a400c0c810707205c58a500104001d5080721650300481c020000803a80c6c6503500002d0b0100814540c94943d0f19400c1820002e22000a50110b204403180c000c02c03904111901503240d00f0003180c1c0200200103940a83c81c100d000b4201b4010b94200c503400c1400010921441c20302101c4c410802d5558441c6007410240003a142100480e50aa0b00b102c00403842e41d05036141042120003401800000703081d082e11307080581f03080d0ba40c0080c6010440d0402d1052010842400b601d0745440c0409080000c80300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 216370656 1250 216369406 216369427
    0x80f091504050a050601140316051f05040f0f0e07020a03090612060b0c0a021f050d02160f060f0c020114160e06040f031e0b040213020d090804090605090c0f 69
    0x680010b1000d465401258000920302e40702c8503c507e0010400c0d41600d466400c000003121503e12244242e075002107803250105480015815500400740f03443c01c1c65030a0944401681c00404199000f0401031480030780c1c02d100c3c245000071711590014541c4002c1829a4079aa4000c028598911828050003061549124403201d1a00240040d118030f80c40f9540710840c048030642c1d43d48002c40180d026040e014101c580002501da001c1d03c823600d035600c4191400d0308090500c002135020000c0142c440300506070150005410010114405006a1012813200c480201030421140c082410405682c0340010030410600240d40c2994060950310700b0f07610580a610702a110700340354400c0c05510400000b40420618240007044040d64040c400c1c40048c01e004c402c100a00000d507110240c5041c1c0108002801813603c03071090f49244200910150030000340706540425519012012640c890000c142800320008500c15000140011640001031741009142c04451f803160310354600400c580001c816880 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 216371906 1250 216370656 216370663
    0xb041224020c06040210050a0206010b0d02070212010c080c09010c06020d0906060803071502040b04030602070c050301050106091805060603060d170a03020d24090e071d07080f09150405 81
    0x103003014244159a2200c2d1103103041d0300d81c8000c4030203d100702c0f440031140107103c0c49802541c100e41525002010140d00384010034040d0703000411500036035602000007900580711b1a55046403880d4581c0042021400b0394405070119031300800c810098036060240c501941e911140b4008815000000180c0d507100001e40c3d10060584450040c01d03086c1071440014039210000020600c403409042e2285944402500c412305a00c514420455041400d11050001c16103a90041010300e20410451004e15501e401007800d40e44c0c00d80c0b1160200c2c1102404000e0400c7c002010020040070f2802003086280c800001400d40c0000341c82d245c080e04c101124102003110b0940724000282d00c00094548420401c41c00a0107507100d00540340c85541812245501c02d41021707101346000b15a0040300803001e060001b40402404c200c0500d40712445401c42c00140c5a5280c80c0d8032a00d00c02150140c04503242926020b0038001000e401c841258203030804100100c04041607500d452400354904610b80d8a950800615 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 216373156 1250 216371906 216371963
    0x110607030c1703070f02030315150c011e0b03060906010603090215030c0307120905370606050312280e09100905011a030f0a0207080a0e09010b0412 65
    0xe02c0c800d400042e5601079041001d0b5220f0021551601d1380c103841036404070380701c0c0410ba4100c401900903242842903454112030b041001e40000310405d052403001c80b101404e40d071401070800304500c0001303030240300c41d180c2e40140307009854107074010095400e22543d40c0340c0c0e89805108000400d81d4656801c0c0865544030701d920b921380200b0426640300d08042e000307114558010303a0400007055802006038809241030058107a40c64000000d060b1080b0900c440c000064004039070014040440003141c00c00c02050135100c2c0310b2a0044c6400101c443c01c00060500d00f080a11040d00800c0003444801c24039402200c0269210481c4400e0340c10f03628400009072170151020740c0c0207900040102c10804102840c501040c02c0b900d0106081c406642d0355408010060701ca04415a40d644080000542c41040400401d0b00200407401c0140307401c036a0b07221484250030100076200000d01e1b02050040d03610700b4520b03450240844071f071120315103440c00102c00d43c14003005100030450600180c480d99402c3c0320100044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 216374406 1250 216373156 216373163
    0xe0601091a13060e1f1203050304030c050309040c0206040c0f051e030a020603041a10060f1b0f0803040b0f0705090f01030b09090106060207090e0c012003070c051309110607030c 78
    0x480b01d042440881c00c80303000300e24401c0848010b030176001403800c0000c816845000d402d40c65591460f156a00d04442c003010650050365644401c010b4040d094559101d000c400c0740e0700383d01a00032800c142c40c1030803c6c2074083c1c2c000d10800c0070b02d850901c840d0b920882017040e1500004034545c1c41000b80702c0840c2c18114608000707907010304040100010700059001005801c4018000c0300015030b1001103290000c1c0d06070240c0c0000440703190701f035000035024800c11000200504242c564080071070b5180906442c4000003151100404028002005a45564550044488601c104030f925024100810340d0007250102489849020300262403a4000e9104000319140075010078420306c0e06030035460103004103204242c010706c205c03000002c000700707103100b41546030100300054400114114011a9403148000601001301d64030030010540d40c0c000c20080007c10f1062011102d07040c540001c00c52010219071000c14410f0901c030f80e01c0c0002e44c0f4071034901010601140c182c0d07100c0141e410215821a603040008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 216375656 1250 216374406 216374429
    0x10e1201060e0f07180f05150f0a050712020c091b090306100503190b1602030c0109030e091e0718080703080301031b0b0703030b060702060d0e0601091a1306 69
    0x3c08100d4460b51250310130152601c0d0ba41002d5040d04850b0340c50701d40c41c86003005030340c940b040900c203c0c13801401c5825625020b981a07030426212110001b0b40c1d62000c100c94004c02c8000801000b048000042c131810000c05002402c40c2d0700005000c03540000d00148044482c000712107403840340a50b414141d8100e410f000d01101c0c16850310403460100301010740209403007403048401280d07480c1e43c444082c4034500e52051900340241c0321602c6036540e02281440e880300390f0000703000403100390310309104090402e4000c1e56440e03000740f0410148805070780301414021400308588000722089025142e0b00d600580d1900c1d0950100030fa00307054801c1d8008c5508181c0441c01403c0b07000080c001c402c1c1c01346040c4d9010380c4c108280f050f04000300030ba004a4902c1940f01c1d03044180607138000719000750310800e45c0c030700d0141c40785190105980c0001c0c025408074681403001a601d0074030000c1901c0c1004040e000d00b00c080010842010700090300c00c0744c030b40e0041d4600e200e0001c0546a0f07500d602c854000400500780361140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 216376906 1250 216375656 216375661
    0x509010f0e0c1911010e03091c0503090612010920070f02030c280902030403091a091c11060c0c21060106110f0d12090f14010b091302010e1201060e 65
    0x8010500d8882c95402175802e00010b01400c1c5800b000325018244010502a226801c1d2400443d1000000c0c0c0d05072840d0000340f1101c010794075410300508000410324030402c0c1642c1016908400c441900000c0d050231071038910b038010110114002c8403002608081c986000c0343d002d10000f07140071108540c50741c02c850340c03030400000c4078034a054002c2944140b44182c070070a61503012040480c0421903000d0300295403c50b04120481c81255040c2140c0080719803140b4002c180800304a054080101c001220018240041d051020798808108505011a00645000301c401c0c2c00a41d55030007902118482c001c085400d0350388481841400d1444414401691503644e554280174210302c2c1001c81d00c0c1c48602a02c00b400134042008151494036050320b40700c0d00000100e0800c690000e15040f502103840c200440501004900301c402c004038025100000803610003882380c24010112009881018180814000180183e8010f00244e010b048180d455100302a500c0c00d45602501e100c5c0e1203030150940d903d00307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 216378156 1250 216376906 216376957
    0x30b06030109120302070203211c15031a060405010303140a0917010905070609050d030503060d0c08010509100b1516080307030c092306030703110c0604020a0509010f0e0c 75
    0x1d006514008c130242c442d03182c070b1030250b00e003040c44400388135001540130130000e440550140c43c12002e420094400141854080e80000312501a60700181c824800d0002ea4452160b4140426075000a0543d01407249501d19607001e01050800c8510800703031b0030045400000c15205a54100060104405040c290800300382028000c5c5404181030b00c2038000d0302c40c08105a03000d601c1180407100003030442102005603031411120ba802c05843d00340d21000030858000490b0380d0030f0304440502002000003405041203100e41e45040d0100b211202c07800c0c10310314400907640e80c0c0111141121381c1d09800c10358407a500b03d0f4a00c2c0c900050308009041c1c00703000c424040510751544c088021136600351581c406142d02c4a200075203440a0304500201220100e803203d0480c280f01c40516080b0030309050105604000c80c080d4a05900450b003404115031207103003040154030708030201e00000d107001c0e2640c11103541400d580d01e28131402402602029001003020403d8481180101c810034170b80460911000c2c141002c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 216379406 1250 216378156 216378161
    0x1050903100e0c0607050303060415080d0f09050f1c0206120f04061a0d030c140d081504060e0a0506210105040212010501080c0111150709080d0c0c030b060301091203 73
    0x75072440d40c612030900483e0b2141811070442d1090b54021005604581c1d82d00300b08400741c086600396012200300340a002075190803c02c0082d1a415054842c0c07509591402402812078a00e58032485c4500011b0f0780c401d5880d11030b043da50003101c05941203130240c500940041b4909100f0682c0009200c88408100809036050041990145100f40c4080c81840c0c2000034117103070071010f0888180d000413001b9090002a01030390302490000d10412402c509104a00d03c442e0a242142441c00c0200b0034010400c4184040038181190000301201c2c00c10045041a2040f450720000905542c0850390f07807000300751156182c106075184d9008500780308000e801d101416902030041502c0803800344011001d0300703d5462040c081c25060710905401400071702e034082c1c011a200c2d0949010707c90140100e004010000c00c6c02d401da0352048803191141140c3c2887e01a1241c17520080600c120300700400020f04200169034030f00703154101e0743c0181548007d0b0302e030030000a00410303103000700504020fa88101a805c058154 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 216380656 1250 216379406 216379421
    0x4050c040e040c0f150801090207030e092a03040b0c0d06120609060b040504020306060609210f070605030123041d011e091e051c120f020a120b0105090310 68
    0xf04001340a40d54441120311980001510903000c50f01c03480050040b00065405408502c1c001e180101b00310b80c40002044483c2802c0c2c81d0403a2900100c0040302a8000a030150080100a02d801c1840c5250646803c0489200a4001602290002000814034415800c0000030385005264221566020f140c00001406500390480f202418084040301502d49440760901c6960041c000e403184d6501e003010007e0030352010041c5076014031181c0300c1003a1350480150003460406000d00501040c4e154000c414901904e50b072003d001c10804000622901410800c075840c0046021303d8401101c040f140090080c00c100c0206c0340e031414580700105800501500540441cad840700601b05034124448458500b0380d40101c07806090407000c040404c00401305200a6411300b40901305a5040d01086401c25034035149654003880003c02005600401081d40d00c1070f245e0055020000314503007549503102400c0706440c1c030245010030f43d882214074074503400f440c1213a04e280002019500041200203414000388600d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 216381906 1250 216380656 216380669
    0x6030303180c0303033b121303061112040308150307060206010b0a0c020907030603060b0402090913081e0c160602030301031b031203021804061404050c040e040c 71
    0x6040d84081032030450800080001c0c0c0007182d0340280ca04607142a0064010081a0b030302c504054403001c3c440014070b8205038021031482a0b12580c442c89040410f250101c2903030702d903003001020040c2280c1000009091011240c0c0004040341a003810220305009000e050200141201000200700805038440da007a8411051a906c00c581000428245903031a0180d00590016078000c00050022031403607005003007030190340d140007035110780c01d640403c1c540b0b0703401d070703607807400f2a8440300d06008014141c0145065a0002d880c11810b1503515800550816400f41c240b1112110303219511050250300000c80d29600d0032071051440440001c0240c200d140d111111440b050300038004540c1c40700049003e5081110510383c001c504590950700c45041c00703401ca81a0034407800c04004004001000d155140c4000d00c0749440060700c030030001035441090008421200d100d141b0340790b001e00c900701084000c0050303264207882c000303280d95400d40d121109210f20f41026241803445402c0000f0411407200b40800e0303ca0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 216383156 1250 216381906 216381911
    0x1110d020a0201051807090b151303030305060613050d050109020306160801080105090705100302120109020711030d02060c1606090b01050a0905010608060d030309120e0321070227010906030303 85
    0x1a40d91407282e00507a4111703406002d8000c0d0108003c41c0d24143c02c60303000c420300101018201c1800c1000302c0c8050f0702004040313000200d40e040400a040d01441383c2680040150b4040c0e150809000354840000704501880b48107035450003005050001c25808150001c2c2d014088030b07140c1c1082e01c4000300003c0c6001e05900080d0002d0004a00030006010307079800766842100802445040208100e103030032001040e81c042580c01d00c00c0210704503c2c201201e0007000400d4005030b550f170b000e04081130010440055103020354089107812176150350000b91076900005400002d03460f00c1d41540010b40d1003c0080025041c0d50414884400780007690784114100e8070102c52104c0215555904501600c200348203640100e107000000503003500740007541e03003000780c405d02e0000340a2595544448031144400030340b40020b0380c081d0f00c618a0707007410011b50088440d50440741042509401010405203c3c00c40000d0040e0403500d2031001c00031070f01d41d165022b80e80d28002c80460f9a10348450400800184c032003a40000d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 216384406 1250 216383156 216383161
    0xc0810060504090b040f081201060806010e01110c01030513170a020d0903050a02010c0c08011406040c030b13020706200703030605041b0807111006030c0608220501110d020a020105 79
    0x10303180c42681000c036401310038005650381c2c41d19140703030040703501c90141d83c0004100035001c0c180b00d6840300980070b4031141d00c03100e860b0706050f800100541060072a443c1130102000758040780600008501080e5942460701040e242e031142411525040c5042000b00040c3e034008a0f00143d04050b006400f103858258202c50300e2402c185000c0322018814480501a40c21140124000d9407048100c00752007030040300380d000300b50750b40c1010030708464210450b00311f400a00e00920401c1c0c540f50142d106401300c586024000111342c0c0d03000481c201042c0722200801580005c008040040603040400340702c900c50340c21228101a11000070440c1d000350f1080300000e1411000bc12146024810b0300b0018514044070081d581c8001c800740d99500e0041c203280d003404200001001c60f810100400400b1400703100b804248289546000c0131018205c3d00094103100c600000c020620001d2030306500716402c00c800c00d803140342d01c40c241180103001240c1800c880040000d81e003000c00c8842d4000302112011603000300400e5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 216385656 1250 216384406 216384409
    0x72102010b04060f0819121b140c100203040f060c0c050d030801030b0109060e010302092509050909061b07170d020405132c0111030a0c0f02070819030c0c08100605 72
    0x9422500003000400310916070420b4038841d40c1c00341c40c4a200c1880210400301c0f0381c0c41d41d14210b0b000d803013480c2007a030ac1303d080d01401c4e01308407281c01c03024001c0703000540c00e0074202074940d00160a28001e44c410803003031203c2203060041c040d140c80c000b010054081c010003555824005d1071110240025100b40500000004000417280f0030318044480180c2407001030703402d5900300a029030010340001d110111028003000c4000c20b108000410100584507224001c0ca4242803001c1070a0041c58103035180c1004040000d4030344080460704116160b4800540c5e224814500382000c4031034071150030013004010a07031103003074030840e8002c0081c1c8804a80c012021114180e0030300542e400c5000020520841e0101d2040718070703500c60451101046000041001612410410300540080701d04c07840207034444181c1d01409400000d155080c014520141113510308005103640e4801000007209003000d001100c400c2810303c500150760403240e11040d200003642c0d42d007120303550b2121495021a0413602d00000021203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 216386906 1250 216385656 216385693
    0xc06020c0c090108030f03040210051b0c040e0106080d0807140c07140916140403080d05060103060e070507020904060615030603050d0f09150e060a0c06050c072102010b04060f08 78
    0x107a00c6e10a8243c699036840d402e21405440c0c0d004200c00b80003040c0f001c0001c8031840600000b0f0222040c00401c80741c40c980c000c12040c1e45040124010b1640340c20700030300003c2d2000c24101112a81402c01d5809601c4004003102c05034180580140e0441000c140803064680210b03001c0c0444501240031043c25040c1c0f810404005004e44108203586203401e80030070010b0141d1480c0104040018800c0d081ca03503251600a0994050b07005020000e66540c10420a5030305841050050080b03442c01c0455403420030405052132052110107032141c118400003034208007158020001904e403e200307010300880c01c803a000e0081c084034041214180141c00c0c030445c446105500034110034a4669401c8491490520440c07108038440042e07504212b01100310b044c41e034132a00000c040b8880b02d075540041010140c240401118400b906501e25183c04004850100300039104a080344050703000e250340c2c0340300b039128140c3c0100300b80ba40711034210341407400002e851000040706004444c1d0a0307003610040414019080e44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 216388156 1250 216386906 216386917
    0x19052505031005160f11030705160e07080f04290709090c02031b07050907080405150c0307050a0309020a121406040201051c0f15170105060a090b010c06020c0c09010803 74
    0x40201c1d10300404c1002c0d510803e0980b000f6105810644841100d0300d0845046a00c0308000352080d611104445000140d05032286006000b001402e044d1b42c104403500919881002c0c1103008103c0e243e40204050040b807213480131522020980f440100c07000d101404100700c200b00c824802003044c0c2403000a9140841c090f44160700025800742d880e11001e4900b014820741e2041d01c8916501c1680c2020071252224412540605001c0e00c80c030400d85024680361b440c122030050780d06104a0b0b200d0238802c41c24505426030742c00031740a05107940c03109050403049000700421000030350f01043c403110015400345108800c0d0380441c0141841001c40318528000c0b40d84203010f48000780006c0c0c2c2013005002114240e90756640340c2d240068086101110441d40d2020b0380e09ca10900060040244004c10914820102040c00101c540000340210711300343d000620f034121548500000a43c0390400e680050f07108281441403175510072800c5442d506030310b1445698900a141c01400f4101e0300c2e0020420160000690f41c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 216389406 1250 216388156 216388171
    0x50f03150c131404240b0d0905030c010509120414010813050114090f0a020d020402032e05010801060f1e0c0b0f0f01050a031713081009020a050f0319052505031005 72
    0x10a17249440d0042149500c900155240c843e906d1212800041040c070080001350b10020010402d402c020f18000d0030308181041400d0b070403604000c00c10040840b000004041da0003401c12554039500d5008803d071829035120300600319460102c4296030170050b801124007455034981192403140100c1d030b0003030381c44100c2c0380084d5100c40e82402c20001031903d90011036011a40c003460089160b502c6520000008bc40038043c007070501a040c041c0306075640701010b1401865507140040c03117201da00030302030400180344c82e21040c00e16007400410142c0f80140b8140d0441503200002e00407a103010711804201c0e42c02654103040e24100320000240d6131600d0741c4801c2c1a41d412001004201074000103035070142c1d001c0400d031407400c0d0f00460001010b6005200603a003002c2c0c5d8890200e0707002c1051040000e422890782126200c0d5410302544c4c4c12a071000030b8400100303201c0301811841010142032107441c102c03083d140d8421847c403010100d40880e00085c0c1c40c20445506600300c601c9034041800700000d9840499501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 216390656 1250 216389406 216389471
    0x5122a0c030d09020a170703022407020f0a120602040801050105010201020c0d1115130b0105010203130501110109020a03120f050a0c03260c0c07050f03150c131404 72
    0xc060140b91076102d0070340f00388000c0540c050341d5a41c02c01d42054810a0107000071070342001c1e404106500b482c1e940702a04042038040c0107541040f07080c40c10304070300800c2c00c007038051480d103140045203807940901d00020b40607142a0380841101403420401951050041c4010355081c4000004e0a5005009032001e140b00d82c00030306403240e6140802c0310f554500c541d443e0014401c003100880c1d1900f2800486000345025980802101258204442c6404043e8001411948204910b00304807401c661044c082c0c5000346041340d1401010141d850140012440c0650301c4082d204000040204a2421040c0c0103c540ca644d0058694114151018010001c5007804138481e90010000684141d0041020807200400203600a00e89001d00152510484045030340d94400510982d84010401c9844018001181d0011100102e000441d881741050900f4038850340000303001c03a020155140c1610100c0c51101d0b1418007180c4d603110180c00e01c5004100c203501991a10700201041d0700b0310350710402002c0195002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 216391906 1250 216390656 216390667
    0x90308010303231206101d010f030b04050a0209030d09051c02040e0609010605120307020303040b0f0c0109080703080a0212041707020d060c110703050c060a05122a0c03 74
    0x1074901d204410000d0610b0f24500d0040380fa00081100944014000408048502c2c42c0400c184051240c0c000342d81824400d0860560503d0b499132022040080000c0c43d02c144100601c5105a0107442c0c40300e101075100d03003000e0420401c428503a01625984a0440456a0311040014190b8000819000741351b00254420a0380701c1c2400e41d46141132000727101800001c4d450003060840c0b4103103607050b144030722983d44a01d0100224500141e88280c1010140091417800da0355a0005e6624411403041640c0e00744003042400f5054843c1065a050300c004800a000042c038900d010f01c0c5079031200e0421008540c2d0040803812055482c0b086e84e25080d643c1e0758180564690741ca84040c0d1200d100c040150700281006900700503103034141e5058940d4862880400c0c12040047c024007000c82110000c42a41d01061041010800c005a21710b0035560030307900e0554031b0080060851f000e1007100a589449070489041c41040081d451000e281c0064009040314041c81d1211184618810160300d1915903005202 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 216393156 1250 216391906 216391913
    0x60801121101050c06040f2607020d0f0510050a0c0504030f0f02030c0a030606090b0405060105070b060a050d030e01032004050f0a08060108030c0609060714070c08010e100f0903080103 81
    0x111054681e01410440e00304000410b002e4a01001182c003141d0004045150504200c0a024005a5415122100b06402c000e4041281d4680203a00011f07108a807505584c10922020107110308040360810142c03009001d01c50b00d00400360505850703900c02d00d0714150513502c50b507108000b920103690b404241214000700c0e645801c4e07104461803209a034076015403003010819903200c802c082d000714820320340455001d1400c0000003c554206142902481c1854100141c90380d014003100c229a602420007030703c83e181e00d8045484540d068020303a4200c0303c1400c1031001d050700311203004d12106003603805002216104100c0d007551003031071496030483e584c280820b00c80c0b4542051220100180035064071490340e80d40e500340c0d1500800780d01101580d00005200b0b240c10f10288075890b44040244000d280354108020f0040284001b503405c5c481940c00410220200074205081c9401411494024021000310404850711420a0b05440345c80d5464290f00c92408201e501403101c0007501a114400240c0c078640303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 216394406 1250 216393156 216393173
    0x30c06101508060123040609080705031504140c03010c1d220209040207080403030c0515010803031303030b0d23120301090209120105010306020304020f041a0f03010b03120705010606080112 83
    0x41748143c80403070080304c2d05801c142001400c001d2099540d070503181480c0081813814040340340c00c10783c02500303e0340b9514a428044480700e41c12a60141d6490a003201042c0106d0a1290400030f01b50f0550034002100b09169000000101480640101700740922400c010403090405201c9003190020350b90400700b07505240c65010300010040604058504442035459484a40c441d8004402180f405600202030080030401740e07643c0182c80000c2c02095040403020ba83e240402461010311003088810302c410035101c2d400140307081c0e0300a89500d584207954075040c201500c0750078980c241000c0c1d003c1ca01d030511400090b1000ca212441c50b01600d9a400d01251070040c1d40008107141d0003070313515900d03115100000d1199500850003104016100d0410703104000001c1c8501420910030b908126001c4100b560022000d030b807604084075008108840ba00200713000d4900ca2070f42e03d9040c05103101405010070110014030202d480740d402000080c0c2c07070300001d50b5000e100780903241e01c82c00300c48a01070004d60400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 216395656 1250 216394406 216394427
    0x81309090b0609060a260706090b04091122060206090d080105091302060406110d1119060f0f050402040e0109170d06031709010f0e0d020409020a0305030c061015080601 74
    0x1038201403000d61107006c00e528111a501c14601c0504005804e50841c1070240714080c042c058510742032441e01e10b0b24844500500031406001405a076a043c581e210b850720400319201422400842d121118070b4000d0044114032900c6100054010b29000640c004400b140000e00800e43e52294029a400c01c424000c0402c402012805158800c0304100c0140c0d454001800080009036903481c50301c5a04d5004c1c0741016058070f001000d1001041708404038903c046450100850100440510080c1c0d03400e02602800403205500302d42850245254070700542d0790001c61007940242c0d800c0c02600340000603103088440200d4090041c8420000c4081c643c00e2003401004180070050001c00d0760b030317101d441d240d403010030018482005250000b012509542c010002c1c0c46100e03000c2c20300f450551306810104950418905009110360742c0d03243c0400071551500b030754801954200d81107036150a0701042c1e0a07036455003600d100c0341501c0040800107100349808405004001c1594030040c00380c852400540e64550403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 216396906 1250 216395656 216395659
    0xa141c391b0909080309010e030703080109020d0b04060f080114100b070f0804060e0906030609060703020703090905090105010302090a0b0a05040b0607170904060801020c3403081309090b060906 85
    0x5098001907902d0031401034000d054000c11215603241898952142110951400300246400c140200c1c40800d41200b0058112502c640700540c0d80d2140305900310080010924003944589801404515400328441e043c1c181d51050b070003040400e20303084100240d0b00303040340c80508002e0445800d0211191000c00740808034400c008162200150759210307038058026030403490000c3c04260042a807031400c8861150480700a80c081c0c4110300701141c40a455500040500b41410340000e9076104241c4612940802802c1d070345410001070a04140441c0604000c0c072007603101d2094880490703500703c001e116500c1d10722307001021a2402d5292605100c00b03090081e29080e8011410711404002c107060800c1d005c01c2103040641c85076500d009000700022622642c1000c0150f03881030003810300c2c2010024030b4410070040b03d8001d41d800801943e455981d50400d43c03140124290000000003004081c0d0041c2c1440c051355201d05841540f2850001c04550384ac0001034040740e06400440d009040c101c03002c5411040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 216398156 1250 216396906 216396953
    0x90501020f420a060605070f1712010806010e1837030309030f020a020307050d0c17071409061c1707030206060405010510020a141c39 59
    0x4102c80e41c10102d1589102d0306200c0c004a0040141d5000b0a115480240170345040480c140140b9032a00d075404044014024034502c240d0b0f00c41e00360388000034161343c60003000d142c1c0890a9a110140d064a0f2003080c41100d03142c402c541c020900740c0ca00000c01c2d40500c3c9c0200001c2ca210b45440f40c0300359020102200c100d486c214600c8070521070584034034801c01158040e0310b001c150001c0c0c9140003041444014040c0c4119000300844200594001c00d03c03204443c030807209044c0a95003814404410070f020380c0059400707909004052880342c804181c1070102d9059982d140b00c0243c422081c04142e650444069174801c084a42c1c03980b00e0000805590307200340c0100d14406403280d550005a0040c0e0008030250056806101000f88518003801031030701601d002c0c2d80c0d403d0100380d0a00003940c0d482c200d4500500d520034845103040440e1003081001e0400c0341c0d16000a55942101201410051706e82540311741a120655414283d01c81825860003044011130411035a4021522110f85440650a81e82034204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 216399406 1250 216398156 216398233
    0x402070c030503030f010e090d0818030c0f16060801090c020a0b012702090901050105070302010e0a08070b0f090601140402130e01051804020310020322030f090501020f 74
    0x200d60410348009588540019907903400c01801c3c03891502c505130312456240c1903042c01c104c400070000c620b00d010781c2681d0802e40019145d034a200c18603c00051841046d078400810865003c0320006000240303092003c00f80d03500c07040c40030914031010003a0b000b80008201010010000700e00d841c0d0103410182407901c10b40f40c00701d4056440d018001402e9000d00c07560302d02c0c0c070307038a48004410750840c000c1c80700c00d81411850520a14007191030203105100d402d041c4040468942c05040c002c0d0801109100d00c9400d44100740131341d00c3c2200c0b0680200c0800c0e1180908140000c0504000011090040316210000c2108be03181580503400892103d400310340054007804429400080b280490019000070041f004056040030706201b0040412003640d0080d081c0e01c0300344030240c0c43c0032032030481a43d005075002d0b0741c03a0b503480d4091541c84842d80d2002e50074a138070705850b8145940440500102d803d0359440c000e9496450300120781d1240c03c81c011000700e03000f640403102c1c4003940440030062086450b400d10b40d050f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 216400656 1250 216399406 216399413
    0x1a010804050f0d09050a0506131a040801020a020102030109140f0103141002030109060317070309060c0c03080c0a0605130503090607050c1c0b0703020708030f0a02090d0602090f01020a120509040207 87
    0x11103d40100c0020a107004014409807800c3d00c1000081c0c4001d40b00d550034801403e20b014a03901e0644100180c6000c415000d10518078140300311780182c8200b00c025503413801c143e440207000b58003d116641c0d40515001c59100741c0314000520a0050844980c4613030309900b10b48400a1041c4490b01000e418429503560100d1076019002450091900d510001051490b505045c41031044200902c280d003e400c114410009130800034102c141c0d0410b01c0e0050346003100c0d18056006100940000c1c2511b800814100803102d030020b03070050300c0d0f4400ca10500850301c1c1c000c08107001a5242c440280203400621400f0103600340030014044007030055085400020303401c0701103002e11210b140a04003030f00051441106004959074103a4202c2801e280452510b1482d840300101808050502c61002140350049503041c4220f4060710210301c2d004180203c004882d01d0004025842408564040c011104004400d580003041071001c40e50080c51580c1055041074003200c50358842c0032101c0d07106900b07000c0103012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 216401906 1250 216400656 216400663
    0x609042711090c030903030c0c0309060316090b0310050d050102190207060f090f0306090507090c050705010b0a1202010f1710030501050a1e09020102122b1a010804050f 74
    0x500e401903400400d03640707412061021100004051696682003003083c000061400421680d1241c4164003140d00c43c03200780a22803c5220300303020070b46c1c455008014412039201782000710000c0c80307064940c06507a55642a180003180021211108141c402e100d0800041c10001c1d05000384512403000140703001d089141400003241c1d08201080142e0001d0703820b001c45604001d854040340120700f01216460300d0081c00c5150b0144a0000900081c0c840700407004100c41007007058044c040555091145d042c0d507400040c2682c000040980b20b540c20040c2083c15810190710301020b46401000c815034000041d00190b40c1c1c102088002820441005c0d2402c00103030340b0660341c9002e110707060b0700038a50903d1130408509440380644455915403804801c41c411091540e0800c80070000c07a200820131488600050342002440003100b0a000720015040218003100f5402c0f0510541450300f4001c101c2141100100300c98002071400540041d0102460b9290700a105e03440c0d0080c4600d045511561595540504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 216403156 1250 216401906 216401981
    0xf120902130615020a020307050f0103020714010203150f031005040c1d04020a051207031401020906030c19300902060a0206070305061503040b07050702030a080306041a060904 77
    0x30780303a030b03560014001803030743c600341d2a80c034002c070310003005680c5058000035180c42c0c16101d854819007400b405814a81d000381c069400054120500903c1e2104a040b82800307540300300c4030301c48044000d20107035010b4a002c1c10344850a0360b001c0d004044181e10900002d0080034003400a40f6110032000e07001411450000c1d1061004a461004c5241030801d88180908407549800c003070b108011f84038030406041000500312080383e41114005400c0e24010f0901802880b4401005400042c0081085003003450b035402000c3c090307655846031402c40480c1c00d04a9944151150343c01c0034404803030110f28402684a001107100038280c00c002032411030355001070401d1f0301c40b03000c0c400542c00c100100041e043c1c02d80f0070158070000640b00d0b10340f042a11603421205100040c40101005030520218040c24410700c10f451a066020b0704403034403007a10341402c80445d0401c40d0243d103e21b007450445e10002e028600742200d200c0340580028241041c500422001e0000072400011b1009103414542000f802d50b07605c004d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 216404406 1250 216403156 216403189
    0x9030903020f060421050f06010603060f050d030f0e04060f0b121605041e09020a08040606060926010b0306040f050601080706200a0611070b0604020a0801050d0c030510050105010813030f120902 85
    0x103a21440c244600d00801c081e944401c2c07161040d03d02443c00300340c01034003410011e400361601c00007055031100020014001030308030100c0f2441c80f40001c510034140e10000c181402250401e00345540da44da89102c0742c01d100101032030004500b0710081000c01305500030004134450b06403400400c00d4540d81c000c030480e000300d0707205000102d4035004c1c4001c0c003c540c46a00054402860050340301410034540360466201004008075002040c95400101802940810b1301400008c0544200382001e050200c844c13202207a0540e150701030b80000154030040045c81004450464803403040c03070b2010003481011030034103d16412040c028a04008006120751003460411400791450603118001424011aa07410041c4000d01075481048170418650f04003000340c1c1100d6084a48002d00302240c03501201103a107a900c020042c1c4103000821403820700c5900068140e56080c2c0c0c41040554400003506100d026046004e0045905030f4010413116219194202003a40f80740e00106403035049901240c0d005006900c40c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 216405656 1250 216404406 216404411
    0x2091b0307030c030c110d0c05030c07080307050d02010b0f0904060f090615051e04020a021e0303010e09030909041b0b0c0f15040b070c020f0409030903020f060421050f06010603 78
    0x3c031650180f140f1003049405203411591524030f07400d01070355040e6080c1410103200098020100308241001142e8550380380c50b00343d4101d20354a4001c150703a50002003045405001d01508003c1042c414850690b0b840303c020140041464540184280010094000d484103074540d030003040c00d1007141c0150b5230803500ca0080010480254000d0540010454001c14464070298a40816950000340c10486422040380c0044c2d64400301d007001d91402000300001c20500c02541e0820001d402c010020f58121040a030700782c210365071036640050326880350645c926030002644000c980403035407840780141760f5559503030750400003512410388000c0790704a040000b16951100450b258103410921413400f07060380f4840030040d24102656411401c1000401d040100308800101c402503580343c2039030201d5604040c00c1001000c020741001400069039002c01c1c0e01410708503001c0d4640703040c603800b190100d07104250102c0c07170700c180c40160703441c02010100261018447c043c1138031007885081c0501402040d00f80c500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 216406906 1250 216405656 216405671
    0xd0b070807230715090c09090203060604060312030f1e06081513030302070203010209180a14071b08090603191104030c141305010602010905011404030c02091b030703 73
    0x141015807494000c140b07012800d80a0180112000585010f1a40180d603900c0c0303540e003110b1210060280d04030241010b031103404002100b242c140c0c0002c0c1824003d03030903986503985410501090b201148002803030445071040b188000d40c0710350305c0202420348d81e00d07000c03031220460045160303e03a9500c4d49090070780303944007402c006000c01000409200c80c41441010041d141950032036081544254024050640008111007150742c01c0d030442d0070146000b000d8200e00381504102400031401146c81003a1186420550a206182c1c6041584179a100340e503030080d2602800b00b0354421404065040761011030138007968019680340b0010710712540346180c94900000e111483c0700c0c255050090800c2c1300340820001840441d1010480a00fa5045080c00188600b000c074089003800008002e214646858400082031665064001000160040e030090002d5000c00a0b60411090b00b51401404500e03041d00c600014200f045903294044c00300000e01c0007008d419203001125034030441e04240020307916441d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 216408156 1250 216406906 216406921
    0x30d050a0801080c0307031b05060307030f050703151406040902030c07030206010f050a0b0a110a0503090414010e070c03050c0d020c1804030f03020903070b040b070c0815060f0d0b0708 81
    0x50700790040c044071004042c0b80c164032021a484240500010784900d1881c07020544100e000344054004000180c0341540d01c2c0342803080240208145c1c600381000704e0814010558041c824025107601507440319801d085c4500d4000c82003224500c8100ba250004414400000c1c41d00c04c42c40594819000d041401e40c1d00c29081c0f800904004058004400d180d010242c1404241c0701c11056609865a0003c0759507640c245040030784900f01d8000031400540301d0b4101503c208100400601b050070001e590030f004404000400c000505024004e80b0048100c1000080c040c51040c0c01e408000c5000e03082251a00d00401422400c000103000e06c80701590101382050a2030400042845d03039140400c3c10214039023401c2d07400620031400d081d610010590085000002a503050101c03400038150b000a16640e40c3ea102c40160843e0040c1c035054036040189000045e40ca00013080051441001110f8500c040d82c402c01040051010241c6803a00000b400e41500002a2900d09a60003040719440740b545510303002e030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 216409406 1250 216408156 216408167
    0x1a092d0a0e010b030613060b010306050603040318090209061c020417030301030c06110c120c040608060a0c020705030a0314070c0b0d0c0203090d17120c0403030306050904020a060c11030d050a 84
    0x15400ca00a910040030802040340d1074111600342c44e40000701080c41581308c0c004034050304558020981c441c400105000400d0340002d19004114a803800144025955100c060224010000b01d260042801c0000c008150304c100c40c00d012096a8500c018106500c6203038412501950b5098545103500c008010f00c248500102110700400c1c0078903008190007081989191520040d1b07001030b0152603081075421041d032007072040c1c0b494410f0107401080f2680d9150308190340c0310300a4420889a130f28160440041610201c1c0071000e0700d40c06030003001c4407a403d5400700c0f502c0d80100c0d00f1340e600c0c3c00c050cc1028009444284940010201c80001070b855009a01507034040791030002554040d0b500801c04550f440d00c4082102c00c4050b0442c1513450581c000311044541032083c900100c0c1032403849010401202d030003c000e007056034040c0c2d408009141c2c4905c28004c1d001415100a0760180c0c2c100c60400540744a180503d191034494181100c50541100c003103443c1c03014400104000c40e10105500d0320701603001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 216410656 1250 216409406 216409421
    0x2105011103010f14030c100e09160c20060d050412090f140102010e0f0106150206100509060f090109061a0708160c17030a031a092d0a0e01 61
    0x5031000e4519450b020019143c0d914901c100d10401e0b8120851400c03030342c3c051004c08440700380900980c11403543e8400c010b01035959241060f104042480c0420080c01380003031100300d41030031030312104007000b1541c4a8000301000f1100240102c00c85652410480d15000003410b01807503040e20110301c5080501d0907207034103820009010108160741c8000c0040c1c141c0c20001c034044480d480030039065070500d240102d002d8043c0b1035060f9160322400521440060055118208030342010501a1050803801c4d4102c1c1c5a140558881042e544054820300403440c009580d81e0f0005001480c0840c8800050003298039030100f41c0c82002801d50f03424040120700818200b050341320380c0d2107041600e003614580d14401d0703a008a02449650700c0d0700c0900c1408004118031a0b001501c02030030070242c0001403030855996a40200c03000390010382000c1d04141e0b107070761030308030760040d500c0043c03ca17135040d50340700075842101148566007012040a50b4003222000c074804015805500c90300c1000c260060200302c000d081d01c140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 216411906 1250 216410656 216410681
    0x7060207171602100c0803101715150d050a051c03020703051c02160b040201020d050301140123040803040f0f050a030f0213020a051206030105010b07060f06210501 72
    0x1c0084070390300c0510401001c00c2c158101c50a404454961800721844c828110004200110001c1800100155119620100c4088003201000701d9140c0300051b031104e0100c0401c1c000d5260440c04208400035442070308001d00c1010340000d07000907440c1c54061400880f080f05035280c1c0c10038440d10074680980c80c082c1b03992001500302940f4000c0303070307030380040441c07082c080e014066100100c842c81311910701c0c0e011a0100580d6055448402805040c01c403440c03c0103880481c0948100c0c030032800518040d03020749040301d801c1d200381e501000d801c0f001520101c038944031a0050040313071104140c00043e1000036001070300605008580383ca08007039420741c0c60300258000c022182041ca10400c07090351007484074000e4942c80310016480503030740c0c8080380350913004d910151080b41c0040ad450390070710740c803001a040f02450381c113045850340c4881c1d05050032900e0a00030310820100c1040104041425600000d50110404c10005140ea0f41d034a41c0541c003c01143c1c81c102420729030106401802001d000d44904c0d60b07003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 216413156 1250 216411906 216411953
    0x10f060f0516050d08100905010f03060209040e010c0207061101090b070507050c060a050d050604090b0a0207050f0a08030f0c03070c020112022208120c03070209040f0807060207 78
    0x412a0150800c501000c206040081c0082c2d02c4400c2c580c81c125480b10b40b0f5018049910074221044094005107084508000449081c0000224080e080c080c03075040352000c9540e0b8590707600315200d501c060b5205601c125002515034031a00180752091240d060fa06000b0360141c0b944908201008280c510382092010310750313042101800100e140404c8140d0006464100284d4807006450a5400c00d40703130610303250b03200a0116040c829150800d0003890f5140404170100182e9070b0303010800c0304036a0740343c00203003540d01c10034001059402c3c075600a0001501443c211000600304d4007125180c1405000b00311071078a030103c140000c1e12105210310760085480c1001a0562812000041000c44100d41c042e0400c900880356007950b140c20740c1100c2981e07040e00702081c40820203403800b42d0705125904c2500c40910030f48154800760600001a42c81c0e0103485c01c080c4ac9418043d0b000c21008003400703042030300c85d50107001000d00001c0c072036002020030a105113005170b101c20103800d0140c200003c21105803109823 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 216414406 1250 216413156 216413159
    0xe01080c0f1f02071d0a06050616080a050412080403060b010804050a11180a06050f01030e0a02040b0303040b032d0105130c0203091002030705160f09020d0902090403080f010f 77
    0x80d1105115100c8810b220701c0800316454260080b403410300c0c41c3c0e204584010500c200380d400c0c01403500d5898495540c90605100d22542d41c02030021910510070041c04080b07901c01c000c00010840c03001400019a1072510f1400e15880d8070701c1030310285010804030303141040040c0405c10466180034040000400b402c10407030520309034403002e458102040000b000001036882d20013159a480e500c00502030081e4003280780070316011b081c580060115006441c803a81002455103443e602c240186c03141142944090090200c1e10703401d00c07000d0000c04e03c41561500041c08041803012001000e544681040201c2c01844d50b4442c40907111061889081201d9000410041c042500c2d00c5001040b10f840304040000c421402c200100e00318000d074070341c42c0e521075503a1480d2a0b00d02c0d400800f40500034080c0c015541d00c1d031110142156220554407840c8010040782004028452603070b07000d84100040c00c107021681c0c9003242d00291030340b80c04407400c0300030070520014007a240726003035605c901405098100d0349040b03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 216415656 1250 216414406 216414409
    0x20c0303010603050402011e0e09060a180207050304050603100e0916030f0204270c0b0901091203050c16090b030703170d060b04030f05060916030204020c15010e01080c0f 75
    0xd1005000e03001c181601c420214085910408410003804070504030790000c1014a03000408075001443d00758892104d40000c6a0603250020100c0d0481d42c0d545015190081540100382c0603401807802038502d03004c28000060030b03403120307030065100c0d284440b15020804c1c00c162003554040340140070700006900401490354910040848201a03070b8001c1c14030308091545100040141079241c0e08580f0496840c0390a000071955120b52004291048008138890b586481e8441c1203405140000e42c00110a504100100c1c0405a284030700c090007454594503104000410038985030030321070b0103001c9400c1d00000304000c440e50702c9200d520701d5080f0f0180101c140703503031180c40c0d000708104001c02200800007515829012241d12140c010321817070101e903880710303942d0030062203020039a002a00d09001d5040000d120680120b2450110030311310005021003802c0d40c091000035001a0608460b038402c0c0130182070000c004800c428003c100c015000c500941c101002181072844200002d130040c003d91f600036616 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 216416906 1250 216415656 216415663
    0x80606100c0809041a13050118050402090c0319021810020303040c03240e0f012a030207110619090602030a05120c070803040c050411030105010c14010209040f090501050604020c 78
    0x440f0f104032808110303c2e9214009001211a42e5000d552000c001c520f80b004940c2a40c001d28101c03403038042c51300030b03018004050400741c1c1d40850b4025807003d0b070000090700320400790000e0760700516000792042240c003451000c44d0403680b0482d007007942084151243d041e146003078103007000302002c00e00c040c0d4194145940c840c5d94100ca03c0c000108102405100c20602c8000700103401e40340f40c0c2200c01031000c003000c00805916607640c803040035607550824405460098515001400f40d096420454103010300c0c0c03078000c80080d044007400b01ca04102006262000d0b6407010043c0c15403002e400951039a607040074002400c06156076101d50250340003032000b040007d0b004816100c82c03040030414803000b6621002c80700d15a00ca44000200716075004000d20091100350303500c800540350705a40402040450603980700c4240824450607000602c1495100e000881104007603403c1200b200001d4200001580080c06854510143c1203140ea9682d40f02d0051201c01d00074035070441400c1d14110f107084d1181d1034460301c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 216418156 1250 216416906 216416917
    0x9060604030b150301020f070f060501050307051005032212030f180204110c0106030b0109050601140901030e01110c0109170406320d020901020d0e061602060f04080606100c08 77
    0xf00100d280e80d146600d0749081d01100e0490300034440d11a40c2d0b298a10745680081070f4014142c1d016464078001007010b090018080090750703c010714084216a80c40022245640011301c0110b584c203d500c02050743c901d812164081c1c4034409c1060500c04d03403080c00020126082d403088003242a05203445a50150350f00f0342d01074500c98060300c0c041100c0141c405018418410340312150b143d58603041d00007041c0401c00b01014180c40b071441d014002500c0d08001181c0400c55441c812426500801181c08158000d500c0007070101288000410b40c00800c8600300c0080e0401c0030211016512000e92004100c1d542d8400c00c0b07480c202d260003900701818100c0040c8442200c204c501c08030044044104280d01e400f852451040ca01110110341d14034106d540c0c0e2002c0e4010b0110113000d4804d5501503440c0301e0140d162200f00d07a4000e0006400c05000680820110100c181d00741e070006810450380c0c0d0480004402840036010000040c40c090820b1001c0c00400d0080c01d40303a03810810024900000244071400302ca1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 216419406 1250 216418156 216418171
    0x115050c010905061006020d0306030209060d210302180103060b0406110f0303041b0e07080f0a02071b0312020316080a05220305100902030a080703030b0a0305070509060604030b 78
    0x584850602a8031401010035100192152158100300505811000c00c0b80d0b0907641b03680d00b40c40300700c04070000540580d00103020082d17110f1b203244002100c42c2071034500141c050740a010340044510042590440c0188618038000009030000b03a002401c0410090301c1d00a800c0a1070b0400c041842c090b45445607003d07502800003084200001003014042c03c004480607440b240742600ea617400e1501c0c0c09504064075100d04801065a441c000445600200f100740c80b4100d1925080183d80d91501c0038010b240004050240841d424004107010a00b500010359841400522440219080d4105010418400381c4000110340c420000c0341240c05546101c0358803151700c25001070b1244d04405007501c0d98000c000d08420b0382031007040343c00c0d40a8201804001100e000c0e100f55000141240018015501c0c1a0701c040e406500981500f00040c60a400501c24180030b441c00082c41c000354000030381a8007059205507265480700400780010314150401c00d810900440d40b181c505861640c6100b101e03c001040007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 216420656 1250 216419406 216419417
    0x1e030c0306020a230405130e0a061d030d05180102190f03060b0a0503070e030303070c0f1b0314071409061c0c080d110c0303031f091109010f03050115 66
    0x7403125400390411501000c4c0481542c01400ca43c6403000409402c5403040c14410804140070480aa02621448401e440c6c070f44040d1030311021035100d84c80500101080d50440d010b009051802c618000e0001e00b56602d68bd10001c00c0605066004600b40c1c0c202284400d40769204111820001d81d10b1620240c89544030309004041e4481c40d80e0640080006900c42c5945410000da134840d52580710300290b00c24000d94441e084108090414940c3c3e17400100c400c000440c11401c103a0700170446002030071a10038803d0746194018113407490b08200a103a6a84103d606422002c64427035076001c103010b440040c199918840311142040c10000c0c5c00c200d005400640117602c2c0301d0000700071902c0c840026102c25003107c4a01c1c462079032085c145507560f403408141d400161001048007013100000c00c100895003001030085007186c0710749007141e100c1d40c07110402c803101511540001aa00c8614080da1001e104406640380e214030460300054803400e2020138a0081503c0e00d0018450110302681040c1d5850541ca8031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 216421906 1250 216420656 216420667
    0x8030a080c040509070c0b150907031a030106060c03021b0d1403070f0c0801151a1c0c0f120212010b1c060f050f0a0b2b02070302071e030c030602 64
    0x822107104a801c0f440c0c02900800070000401c1c0c0150a00b01e207248941d2441c1c1269803602800540f428080d010158403200390404101c03500c2c4290011070b00041c0010003a03030701500003000a07003190306517070201020079200324206047c59014000542101c0a400707420303450050900001d943d0314251000240140c2c1e441c1c10800c0207000800c15108103a900442c0103100100905014a004005200c2c0007229070070564085003001c0d10000a004541504d5100340d11005980140c5902c0e030041084008031ba58040b0100c0c10039001c0e4050f04201c1c000e140c40740760680400000003824400114140080c3c14010001c6e880c94094000126044444072841580c46a508101c2c10420310015002e400c0e040f802e007180400c0302e041c840f09070301c12144211120380400c02c3c0c07141404000d614038850001507000900202030a03000c5940d680f504240350010f510354001503d40b048007243c024800580040e8440103040c8484000341c0e8242c3d04490f00705001905c6240b45550b50b8a40c00d50a00005001d503401046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 216423156 1250 216421906 216421921
    0x20916020d050d020d0218120304050108160c020307150807030605030a0210020705060d020301080c030a0f0f020102072c06120a0807024009030c0f02011205010b0d06050a08030a08 79
    0x54171550203114034107661f01e40000600f0307440b200142d40030038404c50000e407800182200000c22a02240e0040c1c440641c540e80d112030204100d0b04d40103040d01400f0000c20100014ad03070a010b8000a0030400d10301c00070803510f40d0401004d00b60002c285a0038103140900c24002c0740d600117400c110841d41141c0c0154894240f100c22414401a03600064000d40086040c41003403200e50080c0d4181d90340c00c811100383d403100004041d81c1c0e03040c00c2ca000d4001da0200d072881c1c000c1400340e90300855140c010b00459200554603040340c14806c1c2e100b0490404401420740002d03d59002141a80c1c0095084803d0030307031000080109503c0d103420b500003c00035000000c04000315158044503036202030a9402240d00146c4008015550441041e00190306203070b5081111009081480348440031601031380d400280004540e2900ba40d0410484143d05020034594010402003d0740102030181075900303600342d210b8580b040404142e40301030700030358466212074034140105071002090310700040c00c1d4500203500da1901d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 216424406 1250 216423156 216423161
    0x2d010308031e0705040501020c100c021e18041101080c18040f0e07060906050f09010806010e030106081c0c050303130c030605070305041703060f130b12060103020916020d050d 77
    0x56045108041c40701c100f0a10503049806041225004c0e000d444800d41081d00700240b0b98500480034005c281c1042418004d0b041c02204084559141502c10200c42c0c090b1002555522980160203030000e04d42042208005c000083c0508021080c03c140829040c045c0e10f94109004520581c3d010700c0d00401e10300100c0c1d0301d980048802103010702c2c007080408550764500da21202580200f4000c40d005020004109104d48100e50301c604074041e40a00308090f041c011101c801015011504112964001d0f07a0107a81c207126200c01820528010b107007008120044048840540e07941005015003644018003060010003100c4d4051300b60441d60b010540d1914145840703040701d4001601891a003400c102800e501030f804280603174050f6420b41812654a10707071004a210803180c40c0c5d0010840c0e1001c007960708111241c1c40d850001001d0201e8140011030100e00303c02c5107454110500e0744a00010819070800c40040c60300628180c2e40007407003649514000e541c400840c0c000da000c1090028004c0c03d10b141c981d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 216425656 1250 216424406 216424441
    0x203160303050a06270506010809070303050306060f181f0207050f01020f03030a020301051509010e040f020f0a020a1523040503040f1412010506010207060c080d020307082d01030803 80
    0x2001c400005c03500300544d07803a1400141ca4624509490240030820301d6006e00f0b03189200b0440b401c001c1207442d08540d012a446c4c2c001808158004605000d960030319a0503002800040d02075541300504004000c1c20441800009005803440000c0383c0841440d0343d0340400c1100c10784000342c4840340d04d1162600100e00c0c0844600042240d0700010050001c4690250000d41c1240d50440f000c0105000c04000e6075810700c5030000449c0480e04144036190f050405400010824110842c018148480302405542030740c40045e4600050700007000c0c00c01045541c50360701c0d40300941c0c080c04105403645c0205800848604465010240131740071300040421070b081045602811004960f0340515560306240641000300300312113442983e180030400c601542c14414584281d005900900700303285052070503a07541d044040295000d010401545569030110700041d03000701407039903401c030341860016091105510050300c0d1f600070500c101d994810b200d491a82c002d06403030300500350300d0f52901c54401307224501308036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 216426906 1250 216425656 216425669
    0x1806172205030307030605150307120e100b0103050c120402011b0c0e0f280902010504030206030403020a14030f03040308090c10210524010c1b14010203160303050a06 73
    0x100d000c50104600800654012203e641741441107030f460b201005410300401c10702c0b00e11008180001200c661103400210070801d20700b9800281d004140c00c0309410008004c842184040e12440c00100360350340b5101e082e6000544002190402c1e05402406c2c949038009170020303040014005070300a07804241c0424070342142c1c1c000c404902e140d540f030441c444901c100b111a80d00940c0c5810009660904a420380b10042e1001800601c600c10b000c1031410050004500c142d0420806101c08401612144011030007030f402a0000c00840c603491030b210344880070340b07011201103800500103800c2c420103d800ba213030400d501d07040030f4086907600b6030142d140040e02200158070282e24502c504004d80c104230aa40034103a006954003503403108900e20303000e07100c003600d000c02c521100d2510f50f8156410360000c50040807051520b00002401c0e40c9070310100451036014244080b00c130541c1004000706880a0840003d0280013440c140b54407030440c0321443d030400b5030180c140354031440010aa40c0c000e611100c040c155 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 216428156 1250 216426906 216426961
    0x30f04050d08282a0308130c0801020306090702240403030b04020d05040506310c08071404062c060a080109030203030402100c0b01031b0902070f03180617 68
    0x3d2544046140078501d000800802c00100d42090811203070000d0000b050f60206411200480c0340e50101c0304103000504054001c8044000200041d40b00f52625000781a09400507849080c101c0401c061620007402200c195400803540351503045058481c4007186648683d00704903944c480c2410b030050034444022039807051000480c1000814141c1c460b5005030b010f0300884445a03141c0d0907000c07202c201507080240f514002c16683c018510800c8901080f0391050501d94210780d501d0040c14a4001c0c42d0f0030600c01070440c00112880d0341418404c1b0340c000d15606070700c40e601145008681c0030303040d12480640000328107000003600d00c2d11070003c600d0080900d08001c01401d403071800c2c0252260800d403800c0303104036804d11002900034495650412840e400a102400d642d1031507540e02004801d0851402d003070f41e5007050010b14110103101800302d003401600403081981e05441e000306410105410309800308186802440895844000c03000c040031040c1c940d0307886480d4041246220101c1c40203030108401c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 216429406 1250 216428156 216428197
    0xa080c0f0723070902090d021311031003170a0906030b0103060f0609030201030b0a030506220c060f2705011101090203010c0e030d0302030108150402180126030f04050d08 75
    0xc1401412403241d45091040e80d50030f50300c6030005402d9215030440658000d08100f6403001500c0c0200d540000d0707002c6404002920705190309003080c07a0300200c401c0c210784000f04104000340240c01403504141098101400e00c0e042d02c500001c0c1a42e5180c1c001c1780d08255032800540400e034003075801788010b0040c0c0c500e001403681d43c422005186a01785e01003240001c2c2080a00c5842e030800204000c00c0d070713a00070081c10003503440b9130010764800c04003a0b00600d281001c2c3d94a5011450008100c8090005a50b8114181041d071001904c0400d0314650801c4005c0344195041d04520b240e902141500c4091030240c1000440e16001070150609120103981540f0f011a04184941c02010408514100740c007601c4810100c08030a03402c0340001d1082d11515009080c81420040c0c8054010b5801031001700400e9020a000c1080e80c1c94040980000c9002c1c0d44a4201041aa0340b02086030002e2210798029440c2081c0360b0190321a41c0641c0c03045c00d025640424842d410054400300f40c1d090b05a4201820b603c48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 216430656 1250 216429406 216429443
    0x6071d0105072306040503030a1109030c040507140c1b09040b0402090c120a230106050301031704090c1706030f0c130605060703020a261803010e0a030c050606060a080c0f07 76
    0xf940b0030b4400d0f5043d6881d084032b9600d843c003480c003510003064004016000c4c1540820601c030280c03000804541c00c001404240940c0b1106650281c0401440b20008001c80000c5a02e5410680809010948980041e40400c0001203071020400d030701070b90648000711680c4840b0b0441420340104010003545a002c1020005074002070f5024800600c0041a2184019072045251f1700b00d2200317003e0180010000c00c0140041031110141c140e901e020203980f03500e429903e4030300c3c408890900c4001000245240c0007a90340346140320401e60010000c034085d00c2542081e1010580d00c03004040c0f454084c06590000c150841c029510500050001401c0f131941c4d1003103031400a4440c141c0038801c40e001c095249000d00301d4400b01080500f0b51a0310003c0394038241c0d84400000d8040400e408a0741d0540d00c822805019200611204843d14800d0f05d48501614541c6401814004001c0c4540e014140621172210240c1d889204107810040c0060250364444100d000c1c024240b0403614040d0001e121000c00c040035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 216431906 1250 216430656 216430663
    0x80f042307080105040210030c05030f04080706050112060506040b0109060318051e06090c10050c12042705070f1107031b08010c0c020a062105010806071d01050723060405 75
    0x52407080321f0001c5002c21450058040702c038100d0708000081e1062000512140d180940c03a9042809a61280d04000705a03030b84000343e4070243c2100843c0d0031580c140d801048464000c060700541c00b242c007030101e01180e40c0002c00354411842100d04064503401c4200e00060090b02d0021229081800d8914120809039900b002c4c1084042219041c400c150004100c001c0c003041c00d00c501c40e03000300441c00108001d5011100c0d42c02c900300542c01d50041c1c00702c00e5035802c0c040000740010100c0209d8102ca105c40f1901041c601940c07500603030b0782036003006c0070001003036400080b500c0c1c1002e807803c01d00030401e0540c508918020b480e400c010506650940c902d4481340b52100100119a0180c0c024002242003420485039000703d13a0000b904500700d00310604c44540100ca4180d00d60f05c1c0d40902e03034500a041001d080c15a5401c2e8011351036a0801000e0106080d446103820880418810721983d02c030007a000001c0c00c91040300300240c6100313410003100b00c910b4090021018004040411200d6030305040c102540c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 216433156 1250 216431906 216431911
    0xb030c0607060f1802090c09010f050d140708060a05040905063c060a080a03120e0c030303151207060813020619030b0a08070e010306150812030601020607080f042307080105 76
    0x802c000d11000a0300811f0080f0403031701c0641042c1e503076000340c0b10b0001041d5078030b0304506401401c00b40c40320300601c5400e041b19440c43c0300c0c10a41d541c05045060441c24419080b0103500040c0c00b460402d10150301081c400035449801100d030f80460300c0d407880031003c01d0210640413080c11080503850141100d4000f40821594002e0f01c0484400c21495502d029a03a0340e61800c45000300819a03041c0300c40f014034101d902040c88d14200006a8200c0305010340020f08503071049541164041044500200e141455181840c407140500700034480e83c2d06104025000c141c0040c41c20800748203450302403046480f140c041e04c0710030102e000c10b00a5aa0100400f5007c1c100032600a40180f09903c0c002075400c41c0010362170704490803801441c210380d0030b649035440513290f400300050003013545850028016504000c0f03890f4060400c070728152a4100100024100a8050425010001b0090030702480b900d55a1189410662003e0322490039480101c0d00f0b140351030604940c141c80d018039400081d6030362040d00403a1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 216434406 1250 216433156 216433159
    0x3040308041401020708072c090a1205191e0212031603060504050c09030d0806010c03030203180a051e070f0605090a050604090f18120c030504030615060e040b030c0607060f1802 78
    0x2c1230030f40039450305000d11045880580e20b03440f0003610000300b00d1785007212a02c03070601e02d45140342079002100e01c0c0c1c00c2e00c00030381008000f441c0c08040307100281e80495a4910f07420648007424040d10031000354012408050240c160104004591200c0c00d40242c0c0444000c0201a00a20040c44c14044040c241d401002440e8068000c250105603514842c40110b846808140c540000b159487d07142100290001440452003500d2001081032508003009038508042c0300d60020441c100321824a003686009001c004441540080000c1c445229604420700540300245002905c490b0f0200c00540080e080e50300203a00998001804602c0300e0440c0c004503503030340c42c00c00280a622180c0c0c4242d442d03110303c20b401415041e8151208480c1c41d21800c103844442c0d0183c80c2c00c60400c0e88a4035050101c4030203181583d0702501a010400c00d141d0011441c05030320030100c81c00c109500745c1c1004a03480d1034501506c02e00c10b00e00000d1010401103da403003091b00c1d007140001048521309020705421711401c3ca8400341d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 216435656 1250 216434406 216434459
    0x8040b0903041d07110d1407080405180718060905090c12010b0a0e19050f03030d0c0207050907020f0601170a0804090501031b080a02040518032a0304030804140102070807 75
    0x142d517100011661280601a41c44c0940c40c4644020100d29070048501190140810440012161303144402c03610750031081c152060b41410188400b805501c11040c003c0d00400014808108141c1c0160b200030448409032080f801c03076aa0f00540489501c0340c5158200c640c80c000b4004107040c03061401600e031401d03258544994100307003101040084a494081c06d58946103071403050016083c07010740d01c0f8075500050112800d0201c40180d10080d500300040900059106130b104015030304e06441d07420341010700d41c0041c01501d10303001141070700c490341404ce4505042d03201800c0c0c11b80d070078108034004400c1d40040b07900303071202d80f01e50341803004e08400e204c2a80c800c00031401d040c800602e0300703503684201c52030f4000500181680da030921000d440c0080c603040d1070b510b411042c2d40d00e1002c00e0004001120b40113030600b101c40882c841040d0040c400b0000f1080079032088c030007030002954030700c01ca80990b050200103221001c25000101d241415a411800060084040c002440458075032810041000001c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 216436906 1250 216435656 216435677
    0x903111608060a14060f0103090c061809020405130506190e04120302190c02010509090412030f020310091a0a030507060201290609040e03030702031c060608040b0903041d07 76
    0x30f80b015241ca809403488080f440c134004c40d20078a0090541c00b0600010304020603c030b5a141c90324001e405d00d590180300400c081e560440301002540d0b22403c043c1c11642c0c42141080c0c00d24002ca078401d24103801e00b0340c4d82c50791080070404a070384284007111000d100e0300d403403031205032031b0429002e540c0020303502120413507030140005410a00030700a0380d11021000c0c0d02036054170142d07141110100c0114600740e0600c88200640e4003e510307a486240d2159011b140600741040001400804507855a51110b420510500910400e0f402c07005100088070103071040031405000c081190701917903180a80d100c0e40031441803000410060701280600445400b90020080028660f8030000300d40919142c807040e005503000c41085600c3c1c80809030050080c0a031000440b482c01944072865540159100c0016900c089200c80c1b030f0010580002c240e07101000014401c0382d1801c900580400720141000301030843c000000340c49014108169401004605007010511259688501c4c0d01c41d015603040340001c200c0e000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 216438156 1250 216436906 216436921
    0x40611010e0a050c061e0703050c06070305060a0b0d020c011b1407020102030a050c0a0501060303090915050f04110f070c0f091e1e020c0d03061e050103090311160806 73
    0x7181e120054000d805071030342c4481c5504100310342d80812080f50302c100c1c10100030710f0140d400c40050080c00c0c8c0b0903220319a032072074048400b502d0b00c41c00810f4001014209801c001842d1280020001100c60224030a51100c26190403503010307008180d4035901da9880c18210f80030034101c01c0a180b000191035110072110b03240031224031030184034648020303016904c2040b6032801d0910600040104070110425103148600c590b90301402e40c3e0b019807040d00014410042401128030354480d00b64200c0d06050008030107854080418035142c601341d00f0b00e00c155900c1001003440d207011021a0141c160181c0580e030307520054901110b58228a006a80d030402c4a400041003420381482910602d209007800c1c0b4214807541d40b074000113040c0a469001d011010160111155002c500241100c292a44080e015591203101d0080458050394080c0761a82c4402042040508031041e4184c1a1a800e107804550140242001c2e23800d000f000f035075500c0034810070313002c8a4104800003080007601d8611042e0750094842c041c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 216439406 1250 216438156 216438163
    0x150904030c0807060605120d020606010c1e020a0f170c0d05060420100905090a0b09191407020f0c1e061b03030106050d060e0112020f0a0506040611010e 67
    0x110020007299032180800007003580d92000c0c0007098464000807070b10f1130b110b00220f00324200751000b00c0d0440d03116821a6041e550140316060f4071840a1034901d400707800a48904022010003404909107011040d9a40300755100c440740c0700054a00701d001c00c9680c650310041044c07802c1c0003403400e5050f4014105111010325002d48040d40d110b40003c02040517450725118036100c00c102034403c0318400003484583c103441d110b42c0e652403144501070303c48004651600303081c850880002844030030301d0f500e0504501c51658541c5825600020700410190050121103c51f00042c40c0c1a52003107506404074081040e259030008401c03040c5402e0005481c40511000c081c0040403020201010390041c841c10750641707600748100909a90b40b180200c05002c80035107400d25042d0361003a044100000c0001030420076003602e5008220080181714100015507161039202c09115510300b0000f4402c0c2014904610242d85161510014120040203030790b84aa6501d009001c10b05160383c884115400e068140705443d1010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 216440656 1250 216439406 216439411
    0x31312030c0605070306030618020a0512060c0a0c08040b0a031a10051810030603020a0830210a060b03010b0708090a0e010803130b0a0f030209030a0203060c031509 72
    0x10784821070100309580e00d080c06010000d0110080554840000010800034000d0701410320411074981c1107112079005008400c546070300990302070541c3e240700840c4060000386265004d4071901070942c0b21603180c2400c440a1005a20140c50b0b94008540810181c150000600c0c0b4a03006440c104000440c1441000b2100c8814000c56445640c40b0301134040706008000074100c544000c8031031202c80000d40b0000c2e10403083c0e90016000a90b031008140214100100010090500c00d8000d004020340d490066000d02040c021900e015507a1030240140b69a804e000d075445001f4034460024120844c0105038036550301110300b0080b44d030402e5000180400c4450440e07040c2d0320f0381000c69141c4203040c0c1791822160b10008006402031040480082c4032140440e50324080d0414001450755503c1601c00010f1114042d0031004859404010151120350000106070755603c080c2405a19241c01200003810320121000180d0540501001c001083c1c0d0b03003030010340c410700310081c1411400b074214040c0140c41908 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 216441906 1250 216440656 216440663
    0x40602031504050717190203040b060102120f04050d030c06020d050a05010b04060212030c1e0304151a0d03020111130302030d0509090406020705070914040b010e2a0904060602031312 80
    0x400c1c108010003968a42070951006c0da10059a20710710050703002d502240e104803030650351403107218180030856078180900a602e00018641c1420031140f20006159440746100d501d00c1100350004081c2018000c1c0384c03200d110790304000210340f240301c9079910308040c02c4102d400700c4000780b42c44000f013441c403e02d00941c4c0a4800c160300034100f040340719400d8140c0e07038009050550440b905000414103850030003a954103400c0580c0a0945a0a00d4a04031100074030902d5940603c0307003400144070801c0304100061414610071a613584803500c01c2c0c141a4014203042c1c050715901c100010310038003070851400780401220b01c25412900300c44503540c811105401ba19214030780c0b0442c1200441d002c59aa6005881458081c1c002e440c0003c1e42c0d0500780e4101c0d072980100d800581c00580401041c01841042a8010301d16255400c88901d0b00c101011408101a000038403803121180e44440f01c005404142c85254501800401c0b01c181c440402039a20b0f00450110094142d2242c80462000000506003040c580d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 216443156 1250 216441906 216441917
    0x15060203130b09060c030c07030b0609190c030e0f010b0f03070602061f081b1c12050c010605100215180c010f021501030c1e080c0d1403030406020315040507 69
    0x104985030300c041e40f100c201683c1c06482170014440540e4180010040c4c00010340080002520310710f803000710050010302051151103110f040215104109407006040d4800703540016900004410541c028002e8000013901445010903841e04818158010840c621085903031b58505040c1408160703a0744e02070b02505005800240120381082401c0d105905143d400c2481c1d105071039158050396180408505145070000d0007420501c1090819504403180c000d40b02040b01c0c02003095464519100c0c05031403042e410448c0000e0715240b980c40a51001c2c02601d0010100060440f84036402580c4d2003140102800030072003480840c1c130741032170030140c0c5024034a50f80107014200d1034200152240b00c0e40e8040c10b010f6015554003601c6401c003084425003e14400c070360407600c0c581020609040c0d070740f03030900880e400d0300c0e505e00c188217101e00010b03034402d150012120564400040d02e00000c0243e100c90440ca080d200100a00c0100009900514400d1110060241014140e00304001c180c1c1c006807a6100445e2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 216444406 1250 216443156 216443159
    0xf0c090e040804090c090b12010e09010c0206150a0816030b0601080f011406040b0325050c0a17040f030b0601020c01032703021f0b0907030203040c0b1c050a1506020313 74
    0x204130ba08980c003041054145204032565a035070043d0b00d83d224501808141800d10014405031003c8a03107030307070401d8695000304500034007454043e540d0b40001d40000c05d02c681848524000303954500201c80906034500130b030f070045114040404e14903030342c601080340c0c1c02a8420000320780d9441008030510174601c004c0b01031301503403070705501070700b450000901d442d04100204000f1410303800c1c01000398002d480043c241c0180140841a8108502c60285c0d90401c000303040005100c0c03c1c80c00269030003000c0e0020840c90039100d01807948011485940d21040c18402c4055000052186260100c0d10600d02a000c3d520001c419000442c120344040740c601c020541107001c04019181803802101a00d0710a00440300c80600180c800b80204403088590003d290b101c0500e8807050511064444d0413040c2d0707060540c1182059a10091141080d000d030501e03226012a28880c0c454100c500c564000c0300d20341c004c100341c0c18003d06000c00b03014891650045c8881d050030000d00075100000301da40710725010310281a9603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 216445656 1250 216444406 216444419
    0x60519110301090f091a040c06080702030a1b02040c09060908071a031e0c090310140415020f072001090b160c05030d0816020c0102150403120f0c090e040804 69
    0xe000c9a001602e280c3c0da01d0502c500014141603010501c1e4030070703086c26466881c240c82c1c0b021740c907d0160040c100f0080c003841485a0b582d0000181d031031140305402c107001c200c2d607140031004e000780755a50041d50080c1040c2c2c0c903501468002c40603400f03a80c01c0303030b4901c0519911002c809540f5200c40c03140d2248004200c010090172401c5402540d003000718454502403151246a1044508000348c0c0d82208141c00040c0d0751613107150400020400028441c010b10010320705125841c0c06c04030042010706803841c50302c8509182d06003030f41100d5440004119a80d10764107203044c41400b25a5034003281e03240340c1c219440580b1640c094a1745100b1203403101041480c02884440d4400141c42c400ba003120103016401d40071903076581c1409009000b01c119503600016180024841d0307450100d14600e03c6c15504104010b2403113981c041504905040080303825541c0d034455240483d0201701003884101e02c649032a51030f40c038800040c2c00200c8558443d82d00c280601ea194818000ca2040c2690001c008207020081040742 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 216446906 1250 216445656 216445661
    0x901020601120f060902011205091c0206010f050d051e03030406060e1302130213080c24030403030504031707020c100201061d0a06030f0525050d060f020d0906051911030109 76
    0x12600c103140c070071a0b20038123003000c00c251182034501d83c2c990342000c090b12044100b904401e4000c1ea18a2004000551400d1500102c0e01000e008090041c1c80c002c101d18240301c1c0800c4611030740000080700c0386001c41039500c03c5840350025201150194180400010f00600e42052140502d036540006000340c0b00076820404000200700c0c040342c16030b80070300c0318428aa801500d2000146074003409000e0000d20701c0c0c100400101d04800c54417801c08000f0121103544004000d070b0f980968076087c000360703070f407950f060940c0d6a451002002c2d0070307603040004100c0026804900140c5080d829187e541c4008100300060f400c0c1c404174007804101500310702080342000580c900054005149110005025840c2e0725181504c2210a40c1941d00d54000c0451900d480b0411214040c0c400b55040c841040d1400c0c000010440d44842102611741c54542c0440050f04c00d1603411100c01d10b80349841000882c0c01486c0c035501400c411107a40c4a145082d030380890045055001d800c00c080240c18146156a0134100362100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 216448156 1250 216446906 216446921
    0x10f141219030e0a030602040321080712150b0a08070305061311040506070b010e01080a0b06040c0e12010903020601080309060406080a0207020a1202120c060d09050a05070b0901020601120f06 84
    0x3001043c91043c8099103c2c4044400514092000035984a080d424040d00e1160b2500b8840e03229030701003140d6543c096000949941146152811420011051201d14007501d034220013000c0c407a4000c6000503407040489c000301307045403442c1c6801680744d65400041c0c0881d03904558a43c1c000000a01219445105501c07041006103490311242c24a42c44074046a03c942048804a8404850f08018081981c00d11042401440c1e41001801d01c982c6542d0348865036007019102e43d008036150221505514040c040211a842d8090710200100c0e1300d006125001c1c3c003c40c0c1003134001d070056100104100b0b9000c411600c4600c0040c00c01860702d8903101044416100c0204540c1a00c1da09000c54001603640030004402009440f05075040043c2c903004004064030703090031800084c3d20101d040d07901030b1503180c2511016940c2000008003034019040103030500d001c08000604900030090007042c0b1500f03002c082d03c0c2e40802071f4200d401c2c6a0729011400700320841c8010142540c1d4050b031214001512a801194 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 216449406 1250 216448156 216448163
    0x60e2509050102060106180b040e0403110705100c0f021519030515060a1404030c0e150a03021c06090b09010c080403080c0306040204150801060e04061d1b03010f141219 74
    0x87c0c101d81e9100c40c1521504150021007042020206000c00d05a009162202c05404032002c0d1202c1440c0170002040b2182080e511030074000701610b805e00340031004551140c4503070090009001090410510071a507403091014900c0c21204443d4030804a100f8800c06104999840c0700b0044540810b040244035003100700e500013005800911711152020769409880114451400d95211905010b00749064000003010705200340820540f9903134550390442481c04503601070740c0c180300c10011210500da0310740c20424060002e90901244400b0800640b58052058041500030480004068001c0b03c8410055501400148101d40030406905c041c100440d0004801040180b410b640c40c0d5040090b000d082c180000842c040100400545811010b016007c40045404100c80c40c24006100d07210040b49400145a4180c04001046622604d0000f440744003822100380e140d40e0f51740b000d03420804007409002d2400c145420445410306000c0c0c0ba0440034181d40002d0102c130003030078001c1d00e040d551492099 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 216450656 1250 216449406 216449447
    0x2280206031b0412030c15050c0d091502040e0a0e0607082212030e10020a0f050315040e100b03010903050d050603100f06081b030703080d060e2509050102060106 71
    0x782c650310070f0841041e444d100740c81b5044154010b003024040306400103140c41001d070400b0204100c240d10001111a0510744000016a4100a06024024905800601703030703840c0c40010003240b020000da417070600c030725910b00c030601240703407003c50440c4c07100420741d4605d0108440f0400b20700300000b0303801d21010107061590550344040e600c0c0c0f9116400c1c0ca041142c00d0100f543c405402890704003e0080d4980d840b03085e1015454240307145001082d0302e18140108007002404800710722030b002111006400090300600c1448a440800d205980f140d220b8610440140d15024156003e818180680307410b50350182c90366070800202c0c1c80004003416000302982c0c0c0c036019600303004001e001c9507c1040c0001d9184403000900c2410010510b1420300c070b0540e47d500215020074078040b036035400141c0304140caa202008503110f810800065001e0816078200c582000841d00c1001006004a5030120070b01c80a0303000f0701c000d803071000d00982d21790000d07004860050304000c0044c00098040c164802010718510303080c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 216451906 1250 216450656 216450659
    0x12020307210812070f030504050c060a1403091e010c05090f0609030d0201051005010c080403170f07051c0c0c032301090c050102060106020d091406091002280206031b04 74
    0x3900d4142e844601c583e58102c07080d80512031820b90200d00000200e0240c207003085941000d031506030369190103104d00c51141c0e0b00043c0c0010000d100d180c892403000404e6030080d407a8286000303419100c0d084001030a1568840c90380c207030078001c4140202d4210b50300c20f03100e82e8905041082404541281140c03030b184c100c5da04010110054800304108081d241d400d5000050700e040401c00015448219803010341004903091003e804250303c142110101c075800601e12000d501191000c4025020fa01500b100301d180100d000303400c0c0035010401900403030842c5000c0130300482ca44001e4a1440070200b010300014000d64040c400034141ea00005201c0118644400c03040301651041820346001d840c08403900d1402c0c0c20200f00e2942c0401c4040d024041c140007603c40c160940c41c00a00d050f040e4841c00709405c0c1c0c101d01720006902e03071070201c51a015020b44004401c0c00c82c018042c0d6031f065110141d60000c000d00e0b140345801748180e8049440c02d0740c0200708030700d0758440140040203016040e5120740052002c00c070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 216453156 1250 216451906 216451913
    0xa120b0a0509041104050112020105031611070e160f0e0d0203031c060806070503090d08060105161b0807060f05071a090609060a050402151309061e1202030721 70
    0x3861249201c0c50039901101c081501740020344106074404101c1c0d561042d00d4800503a000016240d00c110164198500840c0e000760844001032680c1d000381c042d000705100451070500038034107144212020310401d0801940107108a03203080002524030000b40b5600c000c0c010b18a0711415131241c180c0018202d034100075001803061210000914a485095905d00040140e0394062000ca40d01c07004a04003103043d45030698016468509101401082010000000d50031382c0c0140e05651401c119161a06d0340d00c201480e015918a0f01d9000e51121031140c020006010f940009520050302c1c020360710b1920303225280345c040d21907410080c0c1c01c50f07990384820300302d030420a01085c0151148422000629072410a48112800c0c250301410022446041c04100320161326540212800300c904449140e540d08140145041078280c15000b0002a0341040400219041c0c0d036900c100c0c100e40c020b2012203a103950f80c4600b406481107000c00a4154200c92400c0100481017401c8141c40c4038125020341024045a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 216454406 1250 216453156 216453169
    0x20c0a1e050a15030509060c0708070501060b031302010314040818060c0a030215010b04030c0303080703020c0a060b120304030b0f1f060504030c050316140f0411030702120a120b0a05 80
    0x3c0040c120398908100700410103506000c1c480d0051041c2002e40a28244449000c0691146a40280c560500080e40070104102517106500815a4940aa4480c200407140d02c1c040285204160b00281c00c1c00d682c85500c04015250b60b0240b0b9000094518002c01d041d082080000075440705540300138107203d001442c800520059041510a0703014144000391035241014000042c4c01485d5408001e00081c40080da40010320000d40341c150610683c95a1404400c40c06841040c614641600610083c002001079039080b0b000c03034000448090880c00f0303042d00c0e030315540d00a038480604054446004500c007081440c1d9043d8102c2c41d920450143c0801501740001c14005d1940030400041001030100240545084181c0c007420041f8040c0501c00f401c0380c2400f91407a2b90307004800c0c10180e03903d201c003038546d10b00c3c01140c00180050402e00000d04d0078281a466900300703d404001600403850103c03001040c0038203c5130140323000c4c2c4900e0810b00c4a051300e00018444490002d801154050340899681d8a60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 216455656 1250 216454406 216454409
    0xe0c0102251806091d100510120b06010201060801090b13080702030a080a08010909082a16080c0906011b03120e0a0606050103020405060a030509070510120606020c0a1e050a 76
    0x3000f1440c0c0389032403800c030101c860500842c250028000c0c41c03a6152200891619100d820500001c2203d40302d500c4120300a14050340001c105803200400d00c42003041d00860688241c100360002c002c46541c3d90400c6086e2140c5030380c01441d40207003c0000d0702608407001c4500c0d9103801003180b603003010400c0e400300b80b8281414a081c0c0d02d004c800b15061a1652307202d402c00d0301410080c0018443c0c2060b903034a40245000706d861500720134107541040171456102c101103403003100c029422200b05004590056000030314170702440106001d10130412b1058109026000d00541040e582c040c1c0f120b0200e10840d9900451040c00c43c1000040b5440e0141904540500740d01030f00316001030321034070751707185022801c07145039074046810b06006001c104010f95401080e1034050640d400d011450b0340e0f4401240e414200c054100c00d51004004090944255010246907106404010204000c540396501640c2d0b0b20310403850a54004814541440b00003204171564210300041c460756107580d921603000030000b2640d0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 216456906 1250 216455656 216455699
    0x130314060a0c0513090e0a0213061406090a03080309030c0703030f021623060c03040807030c0b090d08072906040f05060303040302060a0c240e0c010225 67
    0x144050005002042c4200005003486092035031802c041c21204910410007032040c86036080d501c4140d89078030441880780505080c0c0c000c004500c5c030803a44003001c0003054030b402290482400800c2800700c0341802c10407101469001803d41040d00d145a560003201c1e80010001c1441c4d02040c0040289076104104a1015601c03c0d1500611000421002403070700582c00908502c040400c0010001e00c0d00c0c2c421180701c44154003d40c0000804d014020034a113105459414070240b20000780001c21a0000c01c600080e6441480645501981e600c50312040380100c0f0074060740b00f4031040851000401790001040c03818401e802000306030051441c20b203c5c00c4560810710b0f9002081c8020030111349020303ca02d11603c100f4a50030816400e0140110ba030301d001d1404020300480d00002c4000c10706008488240040e035106480c0c50300311021300780c009032000103050300c101114100503015401c044041407000710000103038007c0072034144040c2600c020402e10034001c0401901300c1e4010940d0b1015840100c0d44280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 216458156 1250 216456906 216456913
    0x612010f050424030b0903040f0f05040b10090e0a0e0d030506130c0e090a060b03090730172106030c090c040e0702010f020d09060b0603130602130314 66
    0x240400b0311081d42c01511201c1c5103d4903000000150003c2c0194100c2980d400101041069442c01c06080c91882550844008000502c40003c2e016100d940b100c025218107880501141021800303119000e1101802c0790701240c45a0401d00c41c845950780c000e503000d400504046a4001060a080e0500c105000c4806c0004e85038810414142405250031514112000c000c12601d000d03601c0043c08044000e400c240b10741c078200b0118013211070396005003001d841c1d4140c206549051040c0f01c150b03154400d11030020244240d0f030500c6442842d266210000001c01c155510f00c0800390350300c1461005400e45001c29050702803010700d6002c54050540c90726070043c80c8441069050160405292054500ea0244900707180c4003004046075170700f401c5d01e003282d900c010088401e4032885400e84c05414003c4155111a20100e04a03240d400c10340c101400c068011981042494100c0c420b1214070321085441f0b1030b00303002c008400d5000481c00d0780100012840e40040720149034596442034890248441034078107950 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 216459406 1250 216458156 216458159
    0xb09010207050406030311070f0b090405190c18081b0409050a0506090304090506041803110c090f0103030807022d0a0206040b0705070803030f0a0b010c1202010204080c010201060308180612010f 85
    0x5130400908c0041d0107000301c002003103490b00d04403880c1ca2241810b0103024940364004611400096004000b00d5400d1032000e1000800b0040d00404442d0b6900e007554444020100c001041e11021903c00d9500d4030007984d0380c0c49a40351805000140842c0310003106c180c8940d42010021840502c14240200e0303035003001c5c6075103902d0580d204060302c9002d8480c0e032146280001200c0c50128000520841c103a0509000c4202d0540c8084c02c1c0c01c0404400036290002000010000c000055140c1b8506a903c01e84883d5102d0310354040c00c9030b4900089040c101d503200e00c1a1601228584400303034841c1514204211005c10509901103030039a0050751040e07601041c0071441404000040c80a1006820500011b50861402480b01c20801d10050f20300200c00e95660303c9040964402c038558400260050b0000500401c0210000e0007940300303101d0074145001d50084d207040b0350b10600500040b00d801070300390b0b814051100058561061036440040e40140104001e0300700849c0000c0e054004c1c1070740b1000a42d00b5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 216460656 1250 216459406 216459437
    0x50a06050901061706010e100312051b01021e1309020f0309070503030a0518041103070e0901091e020a0302120901020d05221403091801090c0e0a0b090102070504060303 74
    0x540c25900f01310200d8081c000b41c000f503460005000390445041c0200d20120340c0b900310214448003410b0b0030180c00502d2400a203940d0369044001030000c036400b45d111083c6c201000d40c3c424200d00a011500c605a121121140000924039014081c15031400c0b02c44090141d8504118089074440442201e021002008005d20b440e401d200040040506030040e62030700750801e00007001449222032002003d2113641000348580c4581d404407a030b2007a84115140daa0920700f60103803e02c0e9030a80c0052089454500100701c14402e405400a403038002c0480211010f030854211000c7d402850410040690a00c0002000604681d80c1e501031410200016070340d03100101c089007a02e07001050003a00d80c1c0440840c0745921081e08040d1102500a14450405080428414211b00c00c00e464241c1c01120401b1039a2000440035089048032404d08081020b041119015913203c1c1622000d00e0340070000401c104900d1030f21800400500b14140f0583e0780d080c3c1c03504001411101d443e04141c0001c4c000b6500f41042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 216461906 1250 216460656 216460661
    0x1101021b0c1309080d0c03111c240303390b07020d0909021c0213091a0609010f02010b030d030504031b050d0e130204031a0c03040b060f0607050a06050901 68
    0x2c1c2d030a02d031400d100d000426200c80300c45214800c12900c0c441d40d90840940154070a0780444001d103142c0c42c2d2a5910001001c1c0400c8840c05041c2e8084124a09445684070740c400d6408040a4010459032500651554a00b960001c2c0c11580b03040301c14110229450103001c44500c5442642040465900f032101a41442600c10710300400c2402550b0210440c082001d422400e04000c581c0089009030352854001001e01d00c17070960400d2444068004202c001ca40c01440002000f038500a01081211114072200d54007000c0aa9011641000041082e004d07254801c0c081190606030500003c9240c0c10510701113884e041340d0010f40e5000956600a00040590001c0502d540c0d0b042268200000201034440a8640c21404400404e014440307107170b03001d50384840e0301c04100ca40c0c1e0210110345a681c3c1342080082c8100b14001c03280580d400784001800701056500392400740341c10a440342113550300d0300c040c44916004641001e43c454400e2003c040010010460341d40424407820003c00c01d401c045044909 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 216463156 1250 216461906 216461929
    0x70302010c270311030a0c060e01020c0102162606090d03060e27070816060f080103083a09030305060a05060d1808190e04020f0702011101021b0c 64
    0x110000d001d8100d22081c00e08810b08416607070401c1c0411468840b100001e46000441c1034010512904d0110004885070820b68240d40c8560030303020b03603407405003100049071900300f0030700b8101068000c24003c0c0130001c600c00322044400d55200852030918030803110149042d03030896001d1030b15800442c0c0f1040c2c0315450700900307000384030078140310240b402c1c50614000d4541101203440d0ba145145002c0d4805a101002500c0080c00444c054500030745e070098145500e10000d00694021410b440194010188125039140c1200d4110684504011704034070000f0302d224620b554a1200036103000f540382c2e80c410703803035003100d510461000000d4010039074603010301600d4001704101c1c860340704090100f1003510b4110840380c4195100200040b44c20288601080303d4050010162000070041183c680407000b5400b00c0b02820b046403600082c401d0243e00b00010392003a00c6160503503070003e00c100001035000301940f541c911401000542031110b54002032075598003141404078540e1107100f1408990410204020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 216464406 1250 216463156 216463187
    0xe0c091e01140f070308061309050309150a1209021f0519020303070c03050304020409120207030c0801060b090909010603060203130213090809100e0a03200d02240405030102070302010c 81
    0x40c10103c40f0b60a00c00c041c0118003014040c0a08140010281da1ba00142c502510708118010460110f29040c01070b80d98100700350b181c1c06241c03140120078a440c0c40d441a034200f15200e96540a00122084c00c160141120b4281240c0090031040d0385510306d05c6107460080025840d5a0791512030500110580041d04204164000d40d00200240f0121644c81301d21030300c001d501828025500d442d10310224009200310b40010b40b207a88031000a41c6d03015404201102100d000e00c03a900c00207030301d422001e07003250034501c58465695010070550701c40c0c1c24888510340d84204000000194581d03a516550141e038411903010b1200310341100e1030011403500c01c40345071004803031440410100c0314503541d4103210300c02c1030401445403030940c8611030303402d200b4001d04c2071500c005084841429504e2034401c1c1007103482c03925280d064004404142160416074801580d040d001011f0070741c6090346c1200340891015404088180200800010499450900082540701d120f5400040c2d010050003004041071441c84211 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 216465656 1250 216464406 216464447
    0xa08070e040507020c0d1412030f090708070e0403180f080d0e09042d060906050f3106110a0201050c1c0506040f0e0708060601050705070e0c091e01 65
    0x3c45940050005a0310703100303558485c804c05e0707039080484038541618105c1d10301e41b1a0300c0d1091007008030341010314080e1700700191300560ba0b01d811174450f4540aa50103205210703440700c0c004000c3c0300800302c0d4160b000760180c2000010340030b4a10050f2041c600c2e5400008240345006400c02203036000b0088946020050324041c844003c01c0000103211801c050800f500c41c50181d101520200808282d15041c01c8100c03e00700c1d42d02c0c000e854104050420b00c1001d0710030714030381320000d003441c80c04404036441400c51030031140c84006110040850042207070914462800d80011a60003d08548075100e85114883c601036207402c841c2c48002d084d140008c000f6024034506010035051800b55518980e204060090080703031a80d6520b02141c001c3c401142d0400b001414002801d84586c408140c81043d960100195181540c5280041d2150320500034020601c0d40018810807501c24800d20080e0851044070035107140250b44000105c042c14500d4250943c1d400d24180ca43e00f0351b0304045c00d01030088111040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 216466906 1250 216465656 216465661
    0x1805010e2104060509040c14071505071b0b07020c1003050a0c02070302031c0c0b01090507020c040c0e0d0c030f080c0705150a05070c0302040203090106030219031110050409020a08070e0405 83
    0x10f0440c01240c100f580a03030780b1f980c4400c40303960090b043c002061f0301ba1001103440348202e04201500e0340c65a035603034505510340703404100b401c0d00c075212409425140c88282140220560707038a60ba05800103212800b14051414400e415a40c0c101c10142c00010702d96010600b4145003400804035045c1c04610b00c155400b0000400050314007140550b14889030b046080e030201c3c0c0480054030707101810310006102104040000c40c0760500c0f903000a0140080e6030880c0c54940c00d05040c04100e5051058580118020038105040391a00800c0c018440d8840c5800e000780301c1d0340344d66021429852203800c507000342011512641e041c0040010100a11041f190f01c46042c0c041c10904e001403241d82808000c0000000f44502803058032000800119805041150341c2c0c5031100c83d0034000e00860000b00d21910a0180c4030402c1d114a00741d0109884d04444640541c0e400d1030100a641c081c0320b242d041c2804014440080e480e001c91003c1d040554890703c03500c0d0140307002d00004107848804003c06120344e252606 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 216468156 1250 216466906 216466919
    0x601080a0f080903060403050703120b090c07140a061407020307120509062101060f110c0f0310180c120b06040b0102030f0d020702010801050a1401031805010e2104 72
    0x300c00e1141074000008440c603100c1c5060500491190140d00d540500c103c80900c81055881001040c21a0088d44c0728042e20061540f0101500c0034064015403201801c40031800d1040300000421b060351084c0c1c5103400000d070f0101a24202400d81307000380c82140d5a00701031581a80c40c20015580110544040c51424485075101c0700b61102ea01d2411081110105211100b91103100407101e80003075030250014050300203c01030800754000d0007103a002440c2107a28081c258022004c50401075400300c0a002440492002e201080d101031807000c0c0d02d8801c000f0180200001841003510580320303031a40c5400c400d40b5091001c03101d03000c0e6100c0c200f8240c0d49502c240109081c4003000d07820600440340410390b0a00040103d140d4002c03000305480c01800065004140200341d401001d86a100781c89a40f500d0f070340d48080109605061140303a01d0580c00c04c0321591f0541c4664030400740341450b800a00e461010355240c090031513082c1140c2c400190f1046a94410311044005902ca141945503400c601d401d04002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 216469406 1250 216468156 216468163
    0x7060605010c08070303020a1713230705100201060308070f03090512031602030709060f080c040c120209150406030f1b090b07020301060e0709060e0f0d0308090c0301020408011409060108 82
    0x42d0017030205680412138000d0b49229145500f45035030150b20408050400c01d00c0030301134600038002250700c41030940c3c000745001c5441d9800c1020031260005800c4403445c00040c42400c115041030302e021550785440201c00140200c0180003418002c4a5502030b0f90090301d40034209199039008103208400c0c0d85044400d0100002c2103600b590145001040c020300c0a1012a00d03000c05500410302d503600708800802c0e02f42003a0000c9040300c07040030484800f010204d090000300d82c41040104001416000540a001780ba03400a0414035000f07000b140719002148070321403042c1c1081e088400040c0d00c03400b0b45d0000c0381c60b40c040c0caa9100040f01d115400c0300120040074089100b05d200b0580811300c0418002c1c01d6550a6026800134011442020351524200000406d210054011000441c2000182c1c46503400e03d4000b211001001134580341c0b00c11103d44041da05100010302c03403c414450101c0c0840d46490a001500040c5111070011034148403424410f102454010702e18a80c035848280100300c0c451000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 216470656 1250 216469406 216469417
    0x307050d06020711030607030b040501050f030703080307050d02210a06080325060e010e0f07030816020607050d0221130501080718120b180d0509220207060605010c08 73
    0x1c001030381c03030b03650f8540000040c012400e03440d898041c1c00200001e413a0035030407140f034000c2c04817020001a0303251001c000b07802550122668141c1d00c110001d01c0080c007248025600071f032607401d000b03080841d880b040a0903a4851070164041911403403051040b000481080ca4105080440902a840c244040300b03036640140b42840035100d8030445810ba00030310001c60301d00815000101400a000c542c5c40d018041c0041c0200301610303100300b202541002d10003048100c19a40d126080510301016260010324401c0c400310140c0e4814010003442e00010360400c61502d504106802600014540c2c4000c98020b070200b0300090361080341005141c500b55038426902007640d4003400d0009d1141c48a40080395040c1c445a03041c0c2c0c0c6a000c14002181001e00314054008403440344d1259104c1d680d03100403090048600ca109600c09500c021440b031410340c0070340c02504008001801c8150080d00c1041c3c03e0100101025401084940c009001003c0c080c803400b40001420003800c1c40700c4031410907071b10007201c3d2066 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 216471906 1250 216470656 216470663
    0x60c080906060102101e110405180f04023706030b06040501051606061802070b0705040e04120513060e130507120f090b090f21090111030c01020c0703110307050d 71
    0x754006002c0104044540e14880031803031b4010003031407840340c104c5000c0c1e510130b00a60b40304850044140113880d940c0e1521512036000c0c003071045d4858030350798244502c0b1521000c03030500050340c051702004005280030120742001c0d031400c4405102c500c2c00c034000d03013120b2140c0c03007840c01a90200b1040c040399801c01c0444021180007501030700e1070312a6041c610003c0690b40c204605881c0c0b080500124900786070064100d90303008681b0340c1e200703484144094271a440b0300e102d074090300d041800005002c00c44030300645858807c3c2d402c0803440c00d8000100d08105042c0c50300b104011441c9134051038400d0920710140f90341194000c004010310f0030007010243c0111a5100c004482035266403981441c203242d40c2060000e1a03004055034400d08011009603100d03980040f11044510440d0a40800c100020f10311000040d080b130840b618280309940111004c02100c50400c10620041105500d207980901c001c1001c071803031070040c00806040d03240c0001903201c214000ca219074065441400199500c000e4000360650 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 216473156 1250 216471906 216471911
    0x12020c0118230409062d0207120e18180c060a0503011a070f0c1721070206070f0c030201180e07110a0b01140310050f07110708030403060c08090606010210 68
    0x4030000140240c450510001c00c1d07070341055190403140512100320010304e080603200d001c031400030f61b00701c170102e01800c3e20150800036a14640943d05024200644107203801401c20111400d094000308e04450094602c3c00040f6080d64000d65003990500c07004d007600e0350031180e43d407400c1e00c0a11300512a000c18020b05142d100340300000b21060194908942010b9030001c5c00040303205441c1801c1d48068020b1282d06100a04101d5461010704040340841c0d07031030300d840015411850244c0a100194001d0202207801c00d904008560104d04070048031020349120f14012807131142907100041100d09810055201c039802e540c030900c200c520000c0100e030b0001052034800b0401c0780b040805031414850010140210b62403c00114000000c42c4803061840c1c030a0301221040c0d601080c198044410840d1940410740803c80810400f0b44650b161001c01c004000441d002c00f912402c0003030950348240e104803500395541208940642d04800c106e540040048003405041c40c02e02c0011b5110342c1e0401c0d844d0030159 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 216474406 1250 216473156 216473219
    0xc09010303030b0315010609050f010f0c0b0a061701050411090106090608040c18060f060203070c140a050603130302330c0412030201061a072102070312020c0118 71
    0x40702003020b40d000320300005e0403203219650b80c074003d003207815213000c0c903402100042c0702c03030640754050760384404000740c030381c3e250b61515a1036161615481c030050040c0004c544c4461000908804c0605140d45081144000240da07080526043c03821030010f00c5403e0060155200400465802c0800c40e81201c040d802c06006558691034103400711886504808a81060007042d1444040c65031f10000640319005009407907036440e0482a40c0c3c074052460001c020100c145420300000300301a0695269040c09000c011640362a5000a083c80c1c004848664051003291780f0388007419030405c1400000805080100c6031941006005004040320b00b1200345501910b001048042101e08100e4009220700410340000241c140740007400723031505106004800c0b5103c0004000f072752442c0211000280e111900b0300060003580291070b4024030020001c000d50007060320000c00321b03190401703200c040c0c01141e0241c500002c10718005084207101e252600301c1755004d204140179551117644080e600748110f240c030380c4020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 216475656 1250 216474406 216474409
    0x100b07030c02061210061806050f0903150a0501050603040b01031112120703081509010512030403020406061e0309030e0d240203040b0a020c100908070f0c08070501020c09010303030b 80
    0x40d14a400029040500028002d4010074840b4035940034003030717480c0e0b10300f4465a40c00003203031600004111080000c0200c8402c12a40340590b0061059a8100b58518201203c000c0001c2c00c1181203500d100d008400300040100c0122030703114940c09043c08442c4142541001d0715041c1c241501400006c2245842031f0305020143d07a82003600c10015450012684449076000d81131820b50440c0307a049010a41010103e20640100480c0001c0008040c1c484003050b03103032204000501045141941c1640407c20000c40962a640251000340205232980401d09103900c8688804585091004c0101850002d640b40041d034001e030444101ca5080300e11707003640440c50034018417208540d0407207881e0b134040514020310308034143c0103580320b5801516400e13907171303030318060b80301300381c2c8200307881c2940c2c1e03030042290160852425401070080c1400b812540c1d003480c205a07035001404010b64004e40c0d001f030b4804010880d000701007140c400178010030700c01303000309200f9040410615501800020705041d20f80a604649 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 216476906 1250 216475656 216475667
    0x22060f05040b1b0f07090c032306130e0106050f0409171305040501120302070503060403300207110307050f06070f081608090a050f030307060f0b06040303090f060305100b0703 77
    0x40079032003e40354014550f140302170380e4181c24400c1c41080d9040005a01e029402446140c40c4502d081108002c000c2600d00315a20b500e8000b00000d40c40000c803a01d0140d060b8091086128801c2c00d440009000c038203120030040a1400313245140d101e28207208080c5d00184100d40c0071451950660542c546030b450302d402000d6580c1861300100d80140c6840700000e04047d140300101c42040c066020366046645480c242341d103d00007240c010780840c2115400a2444c1074000c0c2c0340d00724601c000d520031361a540300c48a0001340d0348070310030603220f4a00c41c50350200d003460280202001007104803940c405481c034440115a190081d03990240a00c1842e084003400c1c41580402c58a9540f4080501e40e0213900e103240070782507030f00607a5801c0c0c0640a0100c01189038240148500031540c0c000f8015030520029035211000b0303050070f10080746d1072a11005084410780381c0c54050809035109845050089091912050b148480350340104101424081030201c040c16050700d00f810f9600d41818155541c03402e003426030b031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 216478156 1250 216476906 216476947
    0x61f1d04020706090c0b19050f120f1906180b0a0504061206050601170606070501060b0a090603050c0301030309120f021509040b0301050f150a090222060f05040b 71
    0xc216000245460401015902c01048940720708203484003581c440344064414041c902e40b41038010095403140c0f4586000e8006000b9003004a0381b0140381c030011100d01002d1840a41e41158031110300400d11007141c01040004948044d40d01041060305e21306180b040d90080b00310078615584d56664002c1034941c8900c45400c000d000081c00034801d4660b1041000b0541e071070941c056400520b002e0207d0703110361040c0180902c0000217580301429032522000c20055a002c04401c940c171b50b60310000003c403221514082e00c2010801d4a0f000c451500d015405000e40d503009000855600b410001800000e41225440003a5404499981798022b514685514003105040380694007907401d1b00c05c03102828000e8024043d4000945040c0002c802c51070034182618004d075036119400503600001a8034072010180c00e441600002d04080c2d8513a0b076591420202e0b400301000404000f42c0e0302500007904070008a40780105040d141c0343c0c0c9200c51285008140b030080d8010300440000c006116401da0450500140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 216479406 1250 216478156 216478159
    0x150513140712061d0405070618032904030e19030c0902210c0a030605010215042009040605250f050f04080f060103020301050c180405040f1203050708061f1d 69
    0x2811462904901081484c04644c00c43d510f105038000401d129100e481c65030345011405003a08540d609542d201c1c8450a10044200320080c0b1000b450140400b03040c400394002c40c042e1302c41d24140d00500061280500c540020030018031b007101c00c00c0000906481106007140d00c030400c01609c1c0d83c0c1039a4000782c17000940d0345500444400b6010b01604a05803001000f0841c9141c8042121030b41c0c401c0103980f50100391200031001c1000c803000402143c0403217407404000880b404050307140c0b21500000742581d2015075060311840d07a194200710b0400f09456905008101c50246201c15080c500c000410b110808900b4a041110100f0400e507408141010396029041c150b081d5050000c4038140299074000c24401a032007582481c0110301c442e1440c031704603003000c00c54058250440d80c81c4010300000c0c1001410440f03016418009a01c00b00f00c404201464202c620754001c15075050090300200840005003186100304690600c188241e0501c0920078800303600d50811201c3c0c0800040c00704801d00c15400300d103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 216480656 1250 216479406 216479429
    0x303060f030c091407021c020c060a17060301180f1e08070303060e160c021908100501061d010e0a030203010c0203120a06141509030115051314071206 66
    0x8030400c15800b04020542e500701c602000404d41c0c100050301a030f50169011000341c1c101085105d1582024410601b441800b4011118044200d6000c9500790780700e140c0e024000380203c4081c1d89005001820f1079044034003140280002078002000b00514900400014560703004560013001304a03803413800c01e4812241412400c0403101a003041c1030380c2d902c48901100082d140c51070109204404400150062503011a494010003030068103460704100b805090741d02c1070b0003580c42840e6803a0308051902918040d80078208034112120f64605542c8184c10800038001c180e070305240591000054501012000d2803e142e80c803c000000c5070070100c2d1904069015401c02c0c441204150300000200200706101103461010398610074007100f1107066025200d003031690044c2020341407074040343c0324403041e60000c800c601c1c01c2d50f003078002400c6621401058000b180c1e2041c0801040c40c02d00c8070082c942c414036106000030b0003000e002446000c8001d0030003003408404075803696100c2150740701c24040c10402048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 216481906 1250 216480656 216480659
    0x228020a031a0f01060509060c011d0a14120702041e0912020c03190b09190b16030e0705010305070309020d05010b094006180201080903070b010b03040303060f 70
    0x9040c40002e100001e0400300c0c80715010588007018464038074102c030102d81d549410138601c48104207807a400140c0d031040700d40d00e8054518144104280140001c0200e80081101100501e0003488a0700300802032080d0790002c5402030130216a01040f41c5182ea0b041b180002c0c04040714402d045804011030304451043d10b030040300f0082006001a10300c1c02d41c1146c0869407201940710030191f8400d901d14a8602c1c503081364584000141c1100b00d03c94025503042c054406001c580c0780c3c1c00064014200c802d0700c4c0036860509100703500b828080070300700c540c0c62032134180409a0710f25181540c0340722a20659040580e11000104454441d0340228038055000345040034408407414228040d010744072035644503001100224100d41107117114620058402f05420024810b5005002010500070008129110141520100040c1244100341940d0020141c641d48035555000040400e107000300000d0032680208401d5011075130403c1014110b9020408a41e030301c0e42c651608a000d0b0000c4da003e681c140006100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 216483156 1250 216481906 216481913
    0x19090905071701050411070821070207090f110703080403050d1503020f060c07031709090901051f180b0612070503070318020f0d0222061e060228020a03 67
    0xd0b01420381144a4604026600c9070108001c8030716000344201c41c50001c0040000080e48070025001190020381504c042c0889881c83c403132054411070701000142c00a03d01884034021314800e901c0001801c0c0c2c010880d11144052140c01481041c0024040c040100005001c06200e50103c4107401501101408810074200c41e4550000b104c1c00304030300c03d55020092100608004064441007201c000c0149085803850301c42c40131074a171041c1c030001e803940d003042001600d8807442801c40c0100d406000009107407a00c290303600348240c265103044183d000410400c000e0303280c80000012140b04403490010f84001e080c80003800920950901c911074403840020001d0f00d40e00440514030411040c0c80500c01d42200380500300c3c0603c400d40c8004d41c001c000120071140c904025190140080c4050300038030b116000d40041c1c0016401204103400300d243c840300180150b0f24a10b22548a04101040c031503225420480040d444141d40d840c00c100070700f184418094041d07807117003400b0001c58020b440300d28000d8813401c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 216484406 1250 216483156 216483167
    0x10b0411090901120309030b041401180212070303051b030d112d070b041103071e0f030803070f0c0803090106030c080a11010807090504180611030c1909090507 70
    0x101c90340320310094000040d428034860803800b1410351564403a6440c60031655a01056940600240e810354400494001c5140091143e10110300c3c0f0741c6c95544460090784100216100c0c0e0034000050354000040410010350006c0554003610640c20556003a00c0042000510f140a4540c0880001d0b08100200c000031740b0100041c07000c690507842a4402000040074040c8040454041000860040240c0c10100f00120b1400303410034410300700451822400b000092618200c0d4020b0703243d201082000720400d02c41ba00a8600038150000b07841000e52440d2140400750100410700001c0c010744650307000c0300a2085c0480140c080c0c0c0400005d440f4141a11224020700883c04202c40d030002401c00400c0c40300000510f1480e6941c0f04a080c1070a400480044a402c84003505410a200381c401010405035618012105003046103003900c140e02620b820681c0c1a0703031000c550080158010014409520103503021034030300c01a100008030302c0c0b1141b441c040360801410740c001c840c9c0502d01001e0085907135011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 216485656 1250 216484406 216484417
    0x612070201050609100909022806030e0c030a0b060604030b100602120c030d0f0e010e03070b0a050108060115020a17070c060306051804020301090f120201050f010e0711010b0411 78
    0x1903000704010b5440300d061000407141560f082c0000c40f808002040340120642040c03280c07600c00341010700f400b0302c4100d0000103008054850300c1d45605009083c015a1341c148600c00d01103046070000c0c80c180700001d002c651150074090001c0c21903580140000c01c01d480c2c0c1801c0710000c5601c20107001c1146000011640e2211480c001c003c0103004d0762040ea04991400c0742618808000400614a04800c002d040c400400001b40c2d1948016203504001c105040203102d0a10000074285c01f8599480e00c0385044040203e00a0040704241e240034014400d0305400103032241540c0210082405041ca000401d0340340a80e182e600514100e5400044000ba10400000c0c1c0b02540c13040d0a5882e0307803600c4050507001c0d14002d0082c0c58200c4030503500f0340e40c000212000030b500700c0d0000e0000a880b064036100d0f02c0c00303003c074a0000d0340c01050080010030601d07824800e00740e00004070821403a040d41040a90340b134155004c7d105108104034003801071901c850a601c02c0c0002e1000801c1080003100640745018a500321 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 216486906 1250 216485656 216485671
    0x13090506030c0904085206020d0906060e160f02150709061101051501030b0609061602120705060a0e06131509060216120f050a030c0c0506072f0612 65
    0x3501842400d4107203d80b0306d180c180300300b00500800201c000a0b5250381402185c0000701107802503a9000104442d8402481040884880418014090f050010035200541d02c106103184004c0b0410200035103400804020020900d0144420031041c00c04a2402d00c02002960b4820000d009020005800503c001d086403400d032104080711048103241344c00c8a004030b03422503840340c8428800c426903100c0e9000241d41d0100400c2d050910547c0d41c040340c00b5405c0744403090b11080805000301c06619101d85d035010302c0c00c461001030082500701000b107206802000c00716010702c2083c10340040c03d6560a002d071640c1c0000c280400343c807641c2e110b0042c4018100d078030030840410740381000415028030100b00940c0302c2d1072804011585900c0c0c03070980e40c54207403100700c141da00014003151140064030500c000200325000e9614242840e406080140400020340c1c00b1502c0703072104000d138400150701d0010032854180c0e004003003405421104040d15108460300c8041e5803044c00001d1800503600a02c4400740a140c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 216488156 1250 216486906 216486937
    0x70203041a0904180201020705010f0908060a050f06060c1203040305040506070f170405180711150910140a05090705030a15060f030b040f05030d110a0e0613090506030c090408 77
    0x2c0380711000080d208444d010340140c20801d0305002c1540600900b150f00c40151611b4160f403591000c00e90704000c0142c2d084409030361260103102903010800300e2300d90001c0307007215880e2902c00c41403040b80d45c4001580c4881c5103c0400300c0000c05042c001d4082e40d00420b805000c007991651145080c41240d065000111044140c0114000c0c0303009103a000c3c0c9054810150001006c0001400d241403450350085c942d0003002003030815580003030018450aa1031164005482d0303c40d0078440182400c0040000041808500d090003000d280c0c0421908107402010700000091103880f6000603505112031604800d4152244034803c0003040003805900030303c7c440455040181644400c152002c02c4054800a07080c00c11400c04600484c900c036200002841c4a603048914040780310321070505456155a00a014181c0480c015143c950840c1c1562100c8104907440781c07034481c0c00f5004105000460044009a41d640c00001d07010380c400300450400000b006098841038585450610b02540c0120702a0440d0701 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 216489406 1250 216488156 216488171
    0x9080c0f01060b25050a020a080604110102030a1e0c0204180b0c030601020c09100906060e030d02150a0b0103090c0e01050a0801090b1303020a02090103031227030305070203041a0904 80
    0x101c0070f815585070240c80415007400c842c41003105489540041001c1c0d80c1c9028441c0703078100603603801d1103c6005016010180c80c291915042402000083d800003506540082110001c0380c0c0d400141908a1004c0300d11100c2d40c400d042300e0455000d01a4030009402600e81203503038148140150900a13040c0c4a04140e6409585540c1c021010b40002e90300540541d00503081c0103c2442e06400069007ca1103004020080da66002c0e4071003640c010b0381c00b0401182d038020f8503010a04081c03110940b48100390004040c000a029a403451400006003101803088e0b903002c1e205600d03031081e0000140903800644146038103031a4840d180d5010b90a11031688070350800c081c0000c0700707441801504041031300143c040c6020398581c0c0310280c0a0503920421011400f90010000040e84c8070440580030394000d81c0d03142c42500303646210004807500b540302d280b607001009250050f0110340c1d1003504202070385441c0100d0291030f601e03000e0386180a0f40d04110008000a84050121202003001e407120046c121401d000380b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 216490656 1250 216489406 216489419
    0xc03020d0c090b07030c1410050601080a09020f01050c0703150b04150617041a040f020306130b16091a0d05010b1602090601090b1b010b01020705130c0309080c0f0106 73
    0x103626521070051400e030f081c09a0004203000700301c4015082d0003120a1704510003641d0200e1305100b84414007600d0a42d0360814070620303590060800b5404041d1400402407010282c0014203070303140300710b04241004000a403407400b61000f480301d10019684101d603a5080700800d4841c0c8080d01701565407a000703928162500050201d8841c2c40012940c5584503000c110036800b040d41040a0010300540704903c0207170703842540c2605203144601c51401824000301c42c3c881481014100314015010000b9410801907050211710b4070380d100394000c00b8682c8084054585503000342c610070403036030007101c0d1103c858203610f00c03402480e0000c180303d88201c0820051a80c8604039100d071805103045485903041e229407250014102440126008241410325114070b0396183c0c40d062603944044402d1000c80e115200d4207045002c00d00690042c0502400a08010f0741082c0200b00d0817502554041c04035903d82032070f13011260103a48105921600844842d5039400c89208040e96640f012407084501d6203803110008030f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 216491906 1250 216490656 216490667
    0x80c0f010c0308220804060e13020306010e010c06150b0a0306230607020a1a0c07230607030309050604030801060806030706121a0607050715050a08060d1103010c03020d0c 75
    0x72640c140c5840015840340003a691030b814543d9200032101c00b480c1e12900c049601341000d4402040036a64600b03501c0c01c0c800c184a10b41e0580700c98010400c0c014028041103a800001c6d4022820007841d08200c02006400c041010340756100141d194919464004070704501440b006041c0240c0311f03101401142e99984400303995001411140380004808124400b017403501d900185810380c00140b801007481d0b200c201408090044e1840480c0c01036001620580205003401341c140204590960a03103403079000f201d400403508042d40d03018401c0700300042c120304150003640224603664100b4212500d5150510300031b0507494082c01010702041600c1c000403154580041c180003603a25075039400305168500c61501c805450b0703000d04041075030804030614026448030302c050b0040c14010b800914045251103981d00c014100c4150800800004220800405403c8a803143d0002801d5807901a800c10074145010548841c19406a040d424041c1000304903503d41c02924003140048000c00c60b9581c5d00c54283d90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 216493156 1250 216491906 216491927
    0x50d02060108060705070302150c030a0b1c08030c0c07080309130e100c110f031b0a0309031b0b0a0804020a05010903022404082413051e16080c0f01 65
    0x10143c2c000000600303524850307005001803d00c280111006024401003a02040c50110750550340d10401004001e61584d2500982420000994040c00d615051800ca100d8008210501500f039850000100342d50342910411580342c5120344054901081d00c80d44a03944942c4004030300b510500840140c426034050780c1c401c0f208142e44010081c64035004200c0600c01034001403602e5001e0003018100d112070243c0c00d00c0681c010f1700142c005980e0316503240407008843e012510801042e0741c402131a060000781c101403e002920340018000c0d40c070300680d0245250754070094110303105a0102042c0800301e030b82c000e084503010324800c60303041c000182c0714001107601c0040e902c00650f0064484024482d0085c0304d1400b40c0303000d134001c0d0005240a032245001803a000307110504054604c241d00d54100c0d005654007006030441d20b0300075103205210154503259607400d10090142c094076081d01a480d490700013002108003404280031409402990b4034030007600d07402c3c0d1000d89406506c80c0140c00c0d829600c200045034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 216494406 1250 216493156 216493169
    0xc04060e06030a1b1e03060f0513060e0c0d0b090d1e0e0301090804030f0b0a181401060f080f150402060a11030c0307061b090305031905091003020403050d020601 71
    0x50a148a445500024658100e0008000c0300313190086003108203180811100304841c0640c500440c50742c540401115240388094060038a014207020200c120354416072811500590b001c507036900052141418041070500c0c03190b0010140d0140c5080045d108081d0b48229030100540303a244031445400c0d28411910341c040450b00000044d08110720b0b02a006207890314201400006184045030b846040550050304181c0d46000780144020810081d122440c0e40305aa0641c10b0010f1310165580740c02e104100c420042040c0c1c40302a91040384d07902584088000c0c1000841c9981c0c440d52a800151200075582204e100f07030040403000990300c49000641406103a0140002e441c01a02c42e00c22a080110390030f0004180c007082124543d6600100003030450039020302c42c0055071003502d5608640e40c801480102c01840071190f8104049200401038503d032100e4000c101e0031544191004503070500c00d0101c05130380158001e11001140d94107601030802d0f00d200c0c0003229086044290242ea07a14070901c80c00703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 216495656 1250 216494406 216494413
    0x19080d051c050103050a051015050405090c0301060915060912020f1c29040b0a02090604080a06060501020c0a32180f0c041d0c0f0301080c04060e0603 66
    0x844100c0c4554000c1c490004000414407116400440250a6803002c4c4e00688071580207100c900c0c10b1201c01e106030400e04404540801101d481c103d65450811402d204561046039210002500d210f801d10101414640050003040490b4441108000800070341c00c452803400da0212012032180c0c000c54848064601c40003440b80800c0456003081945e84a160510f030708051810f40950142c442090f2080740140301c1c025202e110148104810003405407030071036501d26040d0030300f8030001c11200c44c0c0d01d9802c02c40c043c4016035501c860310003080051040764000503032880b4442c248010f1003290781c04401924402d07800e560800143c007041110b640354034064292445403012202c10215442c52242e500240007014541800c0344403400181070b084007000429115440904210070300e0501d04103140c0c4020540001410181000e51281c2d17079550305401e120413450400d010400104d1040161207240110100d4660b03a5a1100c0f5159103445480980340c1c040d034107020b804900243d46030315840c8910702c040c008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 216496906 1250 216495656 216495673
    0xc09020f0717040e070903020f0a05010e101b030339030506010306030f120801080d050417030d05010810051b0307051309020a050c06060f01080613061e051908 70
    0x410a0038040021030039030402c0100000544240392840d2644501030a455036503403280b4600501c100c194020340514802d10b0005400d000030703038100381115409441552166030300b40c180f03601590041c10384003100708458184044442050f41c150031503410b014030080d80140721098400042000d01d0319424803503255500e50704000045102c0d07031256500c000305140c00300b4000e6803500c49403c01d1030241c0e000e8a48486280400300903035045803010b0300500c25400200b2010508560060030b43c0124000c50300c440c60308240c60300f103c1004205944a21102c210200b00950756048840c1d5580d00d250b040c40b00e01c0e401d250000c0e42c0000c1d2407140d0030809109245041c0786968942080b1030903400220700d5002501d094101151518461000e00740710007660301d41c250340320165a5014548280140041d216440d0303c19001c04036680b1851041d007199080c0d4402d0442504080100090a0302d078000320317400a9802045200b00300354640a80865030140c4080c0303a000f80f5001920080540b2707008040703ca503c010b20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 216498156 1250 216496906 216496913
    0xf0a08150a060b1303060e060c041710050c0c0d020307051e0138060322080f03090a0309170d120e0303040507030c150c021309050610030c09020f07 65
    0x10019400000d46034000380311034440c00c546400c1d4003c00d500307081c141c0042c1340a10410101c0e00c1840d000380c1e00740004040078541140c0b103003940d21490091a680380e108901c2c0030380e10b040800171007a000302600c1c41130080d8506811000b2040e000002224134503c90a48581c41040c00481241c18182d040005070000030b42402c014811144089001043d40d9a83c509a001e96050340500d1a05d02d03c0c4200c00d6020302c450002c041900200404d03103036110300003c200f4411206130341e04000c520400802c60310a0850010300703001c81d65000310511108080380010410200084c003103031003c2c2107840f94551141198444040c1e1001c111040b07418800d9902c007440400c10980a6000305504403d032031404a85ca1158000d040d046400a60302110b20b680424018010050300c0320100300034140503110116503e44005008100008000c1d010340609a034104d81c810b020f00d150003031440990400121101c9080c51502201184080e1005603101d4501c0d02c8086175000e858000c854109500020490812601c0d48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 216499406 1250 216498156 216498193
    0x513052a01052109010c02060105011d04090203070528060503060105071b090905011b0f0f08041104090f21020c1903170406030f090812180f0c0f0a08 66
    0x441c0e0708542140c10700f940c44100c03c0701425034450940c2c10000308480b1160200a07181410603040700c2e0600001007003001201341d090350401c1c01032004990101c0c1914450010a00b48251500f10540019000d00c405203608003851740c086d480604003d1101e007e6135165070407100d40c001619028000303241000307224080303840342a00c1007801d800e840759a06040c0c0d031420984100c035040f44044407030713945034071406042044100001000c140c0604040da2104100709006207101d034010611001c4c0b268030303070205091021031081400d4044002e8010844d611060915005c42040340d401201c4100c404060b42d0480101448100c200c1c0c441d680060180300c1c052410415a180000d12004402c4084980040801d0301c0c1e070320420071003035a0f00945a40e10b080031001402d851140000742000ca0a080c80480003c0b41d51046070303a01050001c44820948800c0c00080110f0700210540c501ca01c83c609114507010400f09813034001e1003040701c1c159003c0d2002d40500044008a108842c8150002031078040c040f2a40d6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 216500656 1250 216499406 216499417
    0x603040213150b0a1101060e0601020706050307020f10090203250b090112090605190203010f0501050d0b040603080307030e190210050d0615110c0d060b0301020d0513052a0105 77
    0x218040001e64442c1103100242c4c010048150006103c80d4200c10344040038402c6402500c0150303001d4a451516100107907549802d4850300c410814000006148030303100f440510420b9800c0c0c01526203a00c140c034150001340001ca2010b80c0b090160803411700d0030b0410700030f0526859214400001d5424509049480705800604405041c48441c00d100100e18440d0b115407240c861007400002083d06110f1040d005500c150706511090342e10400040c0311500349000308008071791003440c00710368905140c09050040c210004029070440d051060200821040f40c026521450722a0780c100001c580341100e00356604d88030441034402d01c0414082d8400350905002500302082076042851600700b03003150380c00403a105c50744000c442001c51180c009881d81d02407030b0200008200001800301c5241540001d2088000180007012507545528000c50342d01d00f03405940000c1000e5408100e6071800b0756451105081465040300c49001d1000080704140140c6d0100034014000038458640301c14100065404c1d5101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 216501906 1250 216500656 216500681
    0xf090b1303080f03010306050106080c0d0b0105091210050a06140f04020f0a090905060f090f0402120111040302030f060c0301031407230a140112110f270603040213 72
    0xd120010001c16181802003801c00141107100e550703589581010f004840060304030004005a9009101c0d425031000151403010541c0040080c0360b100c5030700103844a100307010405810802c2440001245d2101091040103620040428030480c0c1c0c41000600c1126042d004103088010782d0b00071282c0c14101b1110303c6034101d00c00391005151006240341144240c008405d484005100070f4803d001d911400c0c0a5140c21087c01e032000d001c8a80a08001106500c000303111001d560b0320302c0e0009040d9603403004921724210054000704407060003103262135403952290201303901910928048400f501e030300040c0280b0030005103040504607401e5980f500001621200d035034040d031081000200b43e600080c08604042c21800104d040004001340034020b22041e113500c5070f41c00350300e188403410044e41c00240c072051540902034006124040811084082c0c0112030308411840d00124000118502d68086980e41c02c0701d81140d40c2a4000e00405c000303491004840007500031040060a8001d00c481d6003110000481c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 216503156 1250 216501906 216501937
    0x91a100b1b030f04150f05070206030609090a060c020c0a050a14091305030a091409010f05060a05070f0809030709020306060712030e010c120b0a08120313080406020303070f0f090b 79
    0x3c4556094110340103078105081010010f85444081d6800150210b002102c41c00c215080c440c0640000d0458000240114041e105000014450202c140440182e1560040081010350000540250f956049107941405180c5410000c106450840c064904450180c4406084040640300f402142d01004e003200300d4038003d8200c3c0c03a0001d01d090000d48000301c203d0740c4044082d0b1614089030142c0d1640c1503094050400880103108034074020805006550f01620384036640c5c092500103c8840c46402c50280540b104030415004201030b00000f40700d0444220300300c501e0a80c4820010003248001c0d1012a8030940412901c40040c00003418283c0400312410002403004d8000038190a4072100c0020b200010800d00c40e480090b0401d1098443c0603405541c01410542003c02c00e036a95542d29208841c040b01c0800000d91074503291100d0b1508940c0f1142150321513998070f1000c0c0d580e80064480d44041703010014a0100b20b442104a4940c2c440c20340d9584500302c1c038008a00b4000d6002d0700d4a144602d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 216504406 1250 216503156 216503167
    0xb0a030303091a010303030525020a031805090f04050f0f0705010c021809060105011d1509150c03090102010f090b04170c0102040821070819090504091a100b1b03 71
    0x1030b0f00f0009034000c0d030103a100802d0713918089044000501c0c44a10642035641c1310003215100b01c0c1c0c006400c0c490b00743e0500f000506840501c0000780c0c407090540c80680d12400d61010030507890001300321103000343d10a10480d1154a4002ea0003510340c01740d10840c1c01b46a03c1102d007004070b58410f08200c80c0003400505500c40b9a0264059004114011a5510081c0d4050f50041002c2d580c002d507420564070f0481c0c8914004200240080c03402150740c0c2e00c000125001080402d82e40d070b83c4d03800601c11060412a0140e48095950009403607401c4100010301651800441070b5460f00303240035441d0b407164400b00340e2000e0740d501d0307176547d5040328071407609003040764213105014407c1c20910040000c0c108483c0107225202d0940603803180400c1103503000c2d0001405000050014100b04103130b07142255100207488841d6614041100ca8070450360055900905108507001802811078000c0020210086004d10300d98603018500080f8059100d5000340755030802c000e070344087c4c8229032200c0c1d0000b600152803418 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 216505656 1250 216504406 216504443
    0x10b070809150d0903020c031f0f060b03011805060a062007030c1202120d020c060d0e060f0910060b16020a03050328080c0f18040f02040609090b0a03030309 69
    0xe030040c03868986904d544001120605804210f404100c480071030003060601000c4c603840511101c5904620900790315044042606103a5400410151400825861b140d6035550741c4524070301e004122502c1a145000042100c41c201110820107480d515151500351043d06125004580f030080401c0c8814080d0140210002e044440d00d28000c1c6421180860302c114280100180b84000140c0301019030301800100e00d169402146e11040b402e01182ca582c1c99107072802d050409450840840701e064000c0400700001c0000007040306000e41d40c6a0200c0b40b0038000e0f020f083c0b0881b41540280c50090809012100c550810305860341c81b503600c003401c0b44140503030b80d964141c516000a4000904840700c0c480c00c9030150200c04401c2c80000d440d03c2d0080c464107290410000512034403000a40c080400120074850080c5e1200c0c40e02c166502800070045142800c008900a40041c056400094041c1000040154090050baa0498001440100650701d1560154000c016503041100da9510030200780505 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 216506906 1250 216505656 216505699
    0xf030b06220e0d0e0a08071a070803011e08030c1002160f0b1608010b0307050d0e0313080c0d02010e06070f0f05060106020106060c0506041b05031002090405010b03010b070809 77
    0x46090303000108203003080c904000e448180c48480c0349004651205c1c04109a00000940404803440c52201d00c0c09241842e241e041c4074440e503035001d0710300322002000040c1c8040780301c42d082e103a140315482e0450260b101c0c66000e46900c1581500402e5a100e180c3f0290b0b4200369038000c01c11b8400b1441410104100c0d9504d02e40c110140c0402565090200c004015021500c483c5200c100070142c82c001c82d041d0704001c0104032900000d0200001c00c0750103d542da101044660250700580346400481b6180c4034199036401040141c0d01800d0103e000b0804107685a0510341c4420b44041e505171580c910144a100038480d05410244007964920210382c1a240445c440c0c40c03500d501d0b03a02503800b030082581000350107800c1d229180c3c884e5042103000a0140040342d008248103411075800452044a0080c9880c0700000001c107402c50303507250240c642c549407000b102e54014141d0010075501408140c0c1ea5500d03994680c0400d114400e01c030f800c200800c9000032800d0b8006c2070100b05c014100031903568000381d213940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 216508156 1250 216506906 216506921
    0x70207080f2401050105030109090303061d0702010e0d0e060f040f06120509030703120c0201110f0a021b1005030a020d090f0201020c030a020f01031512050304050a0f030b0622 77
    0x1a074202e110294000d50109220210441840112440e59450600001c0c240c1c0700500c20715140315598a0440c003014400d0300124001c00b840d091340140c4201c82016507082082c29a55040958070380000f8a180c5500419010000c84050b11004000340b518401d1040d958480c049a10881404100126100c90003030903020151105031b0302c031118002e440f03900008448c005809401c0a500034000c1c000000d034850188100c0300042da1000c100e110001c0c0b016805800c221502400d00400400d044601d0100309020f04006a5030b84d003101d05400316454802800001224000d8000750010b4444083d940100c2c01980c000d8640c1c0c030f005181503505104203080718440001213a0601864030b0b0071041d0344c5d0410004040e68411005001118001d50005000e13242c5104a40d05154454907a142202c42d0200450020907940ca0321032810b581616010b030300c0741d0141c010140b04000848000c50100300c3d21211201381c0c4c0e482000c0f4001c0c1d483d11410016421869040904038051030801d140034696140503016 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 216509406 1250 216508156 216508183
    0xf05060c13081614041d0102090a0f080d051315020d0905060313120201110310050a060207060918020c010e0609060a0b0a0e0a021225050708030f07020708 68
    0x6803110980500c02101c1d15155002d0324881d0f03c01100c041c0200ba1000c4200c00302d640d42064502c1c0b0482c82404100070301205103030800a044440034080005506400902c2c07031500c101c0d9980342d400d0302d5203209030801c00f2500601031540d1041d030381541e03810300600007860011072907a9441005a580c0c60400151701e10404a1700c0141c0048201c1c80615802454001c050b0800301c5845003949084c030b0801840030b040c2640a880c50201402c0c140c00706000f0f51042003c00300d034030116582e07460840300d00c10054680d4803445018002d5a1070000304ec0c0c3c03000c40d1300c00903200c803035440850310f41c5403500003011603c1094a100c1100e90800850200840034030607003070303d0404000980914a030007100c0341c2c2000d1008100c10301c1641464101c0d070300c0b50b550220550a86251400080d041e40b00c40c0481f00c024001c207054071505600c40c800b0701c94010b50f8465030703012040c2c2200003040740041c3e0203000c5905015081000b00303502414800724001d914215070166001c4003a104541d403840e65a184e0903d482c90000118 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 216510656 1250 216509406 216509431
    0x604150609030201031d210412030903110d17031e09010504060f06150302030a02072306160504061b0203060a060e01140a0509130209150301051302010e0d0f0506 71
    0x10030440d42c160081c03092101044500b1000b4850614205807910494040303078201c2c49030811f0b8045080c442c03c0940c0c019111180c25480b44a441c5d00e00134100182c5d5000036600d1500547e0005104c1c540000344030911944001e8102552105044001d10b0342c00103004a0700100c004607007030740040c3c0822081e9124148402c008a800c0c20542822000c41c1d000b401c010703003241e06000050060765031140b107025844405140041e500e03a01d213001c0f0320080c090031400a03d200a1080c0c04900d051a081200341011442c0007503031080c0d210415071040c0402d200c0b10460100380300780400c1040f18040c02a01104c02d05000341000ca5110984c00241041003c8a540ba880c0340d941405001101e20003607142e000d4143d0f00c001803020106000050007110302c41c1b00e85841140010300142c1142801540100c2c0d02e51b003c0c00003010b42c100400080c5225160b1501c490007980791100080500e43d02e01224651580c040e121000e101d100741d0184400020b841200342c81d00039800c50740c5800240b00300000351142c0c0c1c040c003c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 216511906 1250 216510656 216510659
    0x2809020a031a0d0209010b07170301080a0209070f080a05040602070f0c0821030a05090f07030b0f06010305060d0209060301020c060a09020f120c060d0f021615090c05090604150609 79
    0x18904000081000c2d5000343c80c86101c900068942c010200c2c1556601c1c0369640d02d404191402100c3c5580081e0b1280c071914000c000054503241c0022a50a050b00c00c039a409c0075aa190070b000c4844503200c0d164000000c807a003010030200e40466004c0c64100d40101800740c82c0c0038084d1100c0c0c0c1144003486049401034070b160400c100b5a1000c2c0322512080c510360b84550b00c0c1d10700b8000e0080840c003014040005940d03941d000b04191510401c400d0050a4040d0295044142d590800280d003403812125440b007140002d00040a542c03091245503c0742c1c000800300440113886809001130303000014011038140d942001201c0540300108a028803814a2480c04106401c00e881031100700c0301d05800c2079008035483c1e06040e80c824000304008020103416200d160300c0358000721110018000f41030302d940c0f206100040d49060b400c2c4809100007014002d82c600c881d0140d856007900308482d1200707405450f00d01c140d44188118900700c00e020b45c01c039000510100f50320780c604569039110702003030b4044400304640300c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 216513156 1250 216511906 216511931
    0x72418080a03271d180d0302030a05060405090a06092603060424150203090409050d0e0105090f01271206140103020a03030e0102070306020301060201020a030b030601052809020a03 79
    0x20542000740040c00f070001c010f2522a00140c000110300e100b50141240c04d0006000d044614442c1a1402c03102048480c4a00b40318000740c0254010f864810226080400003883da0401d4080d05004108040003441c10101d180c403007200074081c06600f10b40342c00d01030040d04d820b00e0070640c61542041050211580d2810010100300071150342200c1c001c0201c00c0d02c08084c3c2003814005a09044a0320504001400c070480e8038102d0441c810301c201e05511078600440c540500ae000646110340c429035807945c20341e100701980195001c3c010303100030982c00300344d4104e0500294443e100d240c0303900050350b032000d05c00d4000300518099402c90f0341002a02407449030307001042c40759600540b00b5201800161805a505540200d102080c0a002c0a02030013401d10210301264420402c2000454104208549070350f15000001d000c1e6100140b0040000e00b0240c00350b895140c08a042030413194000c3c072030208071004180080b000b88203240300c02c0c9100040740001070b64000750300007001c55480c4d564000030140810301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 216514406 1250 216513156 216513197
    0x14071a011503050109090c0506030406020d021207030c022109011b0501020915040305030403170714011509020c0c090907030c0602010c081806010b09060c070314072418080a03 77
    0xc3c8898191811b2440310740c0410340320040402650425035266a40b56910708100001c0d100365400042094400100700c4240f4a01d08001e170300807039489c1e8040c4841060204202c3e611156920741c0102c41e5041c80080c6080209070380101010710703043c1092005440c0341108121280000d100a80e8980d40004401440349050221922201070100c2d00c581424203640322103541c1d0007103000c001c0c80d0308588500c0a0f00f2040710403d9802907540020354591329821480071602811042e0100380745060b24880c081102d06044c000d55444400303850041c014401504204400b08501034455841802001070110108414019810241015400204410181d040020078060300202a16104017150034510b4a842001c920b0034116100760341170b15103038a2085d001400b54407440d0620340c0a40b0640702c0010801548401c0303020884003050030350b20701c0d0703558000341e8000c546403401650050703200c0c00c1412052030280125100d0b0004680741c2511058441040518124541740160b0109050b155501284031044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 216515656 1250 216514406 216514409
    0xf140f1b030405070302150d05040507080d0509060d0534020607050a0507060c11030d0501080d020a050706080a1104060302090a06020705060409090203030f04030b0a14040314071a0115030501 84
    0x80c011a0718629254030340c03685a05803408001e1003000c450031070444a010a07030039201c4034003180340100510b0a152401994905a6100340340c103e018049003400b1182c000c9003918001d010141c449890704404200307060041c00001c01150082c4030286050659509543c03000b800d080c070a030f8041c000c802c81218007030310301a0020444000c020082184040f0030b40d10038166200d40307a0041000c85c082a1036601564007540803142c140d810720002c6040200342e03c003504041d048030928801d90f2101100303001c0481c1c448080100c0a06540c1c00074400300320701072003150500e500400c0140c0c0040c1c04042d204d80200598025408440002c1c0c0100d4400c5007860305848040003080c090004000c400d2074100403507001d00452054042d0103031f45810702411f644003403044030251010408560b5580303440b0b2130301007035116040d00c007024003a00d003c03241e1aa244604264070f0150760592642007148901024240740c0703034810340c1e0440310764010010014500e480a00102e029010032040c0369100c3c80c044000400b1110705 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 216516906 1250 216515656 216515701
    0x5070c0512040f0b0c0f030a0521040503030f2508061309110f0609091609080105060a0e180106150212180f0a080303010306020418050411040f140f 65
    0x8000c00c201c094100a1183d007100c0700c50304c1c01502c1c3c0001c4a0043e051000385a00c4c0701840c0000074642d40c0300382d0722000500090820301111089001c000c90041c2c0f501204682c018a01c3d442000441c81001202803507540c000018003d00b091046d03a0003071008074200848402004c9400d65003805400c0c5403159034a132031401e40020400c061100c54036007200700381580c8038460080002881200903030f00c580c0300300c6581c40d6010341660518281a4008181080c4a0203598001840c0b410041054001809007a004000040c2924445410034038a1020541c2c0540100c0c1c0c100c01071840211090400e02456000b85840c2080c5c00d01b400c00d0410207030403c03a001c1180c26840c9c10400c00d80f010341540d01468041d1290940f200343c0d203d001400861040301c800e40116175075103c04000003080102640047c01500c148420658940c1c1c040b02e000ca081d602c0c2903034010203840c4480c6195007a810503034800001d1064400d0085000200104040d004000c259030303120320007916004003e42c12101c1c000b81c6070200d06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 216518156 1250 216516906 216516943
    0x1f02090f01080613051b12180304120209150d200a080a0b090708160602010b090f0f0c0d020f0c0c0d0b0f0712050112021206061c020d0605070c05 64
    0x1018000904d14804002c000400c071a030340c04c04244980c50300807002c000c3d841034061540d5114903c04000c4443c05d42191201806000d08605240384840401524100c03040314000345104c000c580d00308040008024060042000c1d41c6070041110360700c1400780000c0c28046d02e000b00a02c101100032615510b5899025401180e0301c00c81004100400100c0d03481030b50304200d1000c40d90301c4050880c4c0c144a495070040200c0c0c800c1c001410328080b0010385540880f110fa400030441503090b4000d000103018221049001c3d0442c05000954404225000d0350348290b5200030303070340b030280f626580508a80201e012100405030204488854540400414a1120b0122079202d448050b40c0d403040d120720070080a5920016816001c28051801032028a01c1c10b04501000e000560f100e083c1c030410b5003111003040e882100021580340c44001c000c6203860246001402d001011070740303100c03050354559400000b00c0c0c01c00303804c402d98030120310248a0030303018848941d9010a00c222038206a4500220704581145600703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 216519406 1250 216518156 216518161
    0x30f0b0a0204050a0b090303070501330f05010e010c02090717060405090703080d020c07060e09100501080112050a05030d0504021203190f03090b0a061502061501050306031f02090f0108 81
    0x1940c4e0043c2c0d408940d1007420180e500c4910340301090442c05480c0d002407556080848000ca150303510a080c241c2d01c0f12601180340554182100080c505116204400752000000e00603c0254450384414110031010f040003510810b0942c04030f00c0300d40088a4001c00620340b00d0305d402000c202d4031491600034504440074004ea06010481c0c075281c44140c44000c01280c0005220f414201c1d480e01a0388441e0110401c1da150541c0e13604024000c2007030652400e00c104200d80000b94000210200039056a4060b0344112050382408000c2082041c07484059a003071080d0380ba6800050380403c01010b810500300c0003c51581085d01c1400b100045e4042024141c0d00706012840034128603228440c0e2030002850008400e40203c1e000b90011301100c500135102c0f400030400c00002e1400c58001504482c03008085c1104a000048101d8460f4000d4400f1741d2040005070460782550322a40103581c1014000341a42e080c09524540e02e0014049400246956500464041040c1c40c210349010050502803e2440851 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 216520656 1250 216519406 216519409
    0x81608030906030403110a0308060f0108040302060402130207061a011407030f051303050a030e0a1205121e0a120c0507080d0c0e0301020c03042603030703051b04030f0b0a020405 78
    0x1d000e8841d01500a400100c00070702814401c0d480c502c1c1650f0031800340c0c1c8668540c1d040007405a482103440500502448851010b154480c3d51a1445030340c15034090092a1955402c20030010500e030307031500420f6001e224030170210740030388102c02c1250f181010070b208404004001401c0d034614010803030039a0606018800110340c200701021030710403a500d07040d56075034901c4404284128450b000501544910045c00040513001000c0303080611040ba500151607658592440b0708850301c0b00c000b041ca4001c10700302d11903040340602a10724070358100c044a0301c0001e010403000c6150064603652000420f101c1c5408401811032084494140b15031a24900e88200d540b5451031502c0780c4110303d800a540d800350114003d116090b00341ca04040180292764403000071501d1652038010b800741401c03e00041d1904019a0702c095000c040050b8444091070969452a00035401800020954150303c5c82d07400c00e05100044807002000030314031903d10039004007118248140c0b0303074800600c0341101c1e41c4104401d1005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 216521906 1250 216520656 216520663
    0x204140a0f080d181703030a0b09070c0831180c1d0415091d0303010812030907080d030203011401020f1015090213230a03021005071b081608 62
    0x4070708018140c9000c410007000c0b0480b1540c40310343c100e05d1352010507203d070002000030760160709540f006000b0141d01030204111004192240c0c00850b484400303520001c1d0350440540711070780c0c0000080c0348480740030921080000000c40c0c51014602030f500c080c00544501c0e8007070012502e0802e010059558058009011044a08030007171001006507490311090f0341c1da8102d04140741d0307001c2c42000800d5558440c1800350039150a03095111494140d01e4480e00c400105070380c1260f80d2000102828080341d5101c0c40306078809448115030340154000130504540406c400d8240d0074450b41c3c0182e8079803408242441d14171002e0560360464001200e5003406100000b10340b40c0304580c00c132000501e248158000040c0109035841842d68030300104550300c07200003000102080700d482d0746030042d21038004c003411841509014642a030041c810202400503040001ea10020300400307091041c5820b156841d00301c0501c00c0902c02c003d02e4100050140020340c2e090082c04881c80003100e0005106040610580c2c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 216523156 1250 216521906 216521923
    0x1005040e0c0c031c02030105150c250b041e06020a02090a0c020309090a0207020f09041a0a0b030a0c0602010b1215090319020105040507050108040b160509040204140a0f08 75
    0xc401c00c010801d003104640601c1202c44c1030001620140420b000d40c851a0040c1d0024412548942103100c101e60305003c000044810f60021500600745100d205542c0081c184071107010070340c00c984500c2c40802c0b0b100c800c4002780301901c5290041c80c00fa8408203031044002c00180c00c00030454011500e49070041e2108441503820005052002c124841c00b090101d155018140c0d842e80c0c412016404c1c40701e15001d80e401425a80d0081c0c170030031440220041400f5030341005860051004600d0705280d0301c8250303c03500103034106106403004581c0c0f558540001c0e190a14203801600d1204011604209080e0240700304000040103840103140c03241c6c8804a2516500d50040c00d24111005000143d0010b07028002c03540301201c2842a00800c104209000340201000c507002c8440740702d0342c0c202060030360190009500c2076a10141002241e51040b14004111a040200c0c50a0107014456164a50394a0001d130010300074030b2112070746452011080000120b200d03800712800005655090041d03c0002c01c00c0388 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 216524406 1250 216523156 216523171
    0xe1012030c110301150e09071e030314070f03050d1512020607060b060f0c06070309120c02010c0605090a0204050109111603091e06020d09050a051318111005040e 71
    0x40710702c0903440110f80500b000c40541581208200300110743c042030701c031265003d00f00200c21585900e40720310700d2440c0f40b801d88482c0c00b20b8042c85202000060310030124114100c124401d042c0c108003e9590340c1040001000b0200d01281d030204110000caa1903220740c0501840b000c18142c0c0c1c45180054a00c500191668068000c0c40e001078a60144901600180a0b03d04050300301c607503a000010300d10b4207580000010799028002d200c0800c240034440e01070035801c1600503090345498404c09d8815140da047c1c2c0c0e0000c0341440300080381c1c3e0011481a204851250f400034025201d21656481000308a401c160000f4040c03510703000180c8100302c402000d0365000e0070500c20010180c001d504054640c4415907101c10703203e5600780f812481425103149000c0494916800303d9050725030040702a2990380d41c40c000c07641c0024000364100440d180800703d4514200881c040051144034840c8142110001401c055444c6074a01520b80d5041c2085452a00000d202c0e1030000e003058142414041c68140150080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 216525656 1250 216524406 216524423
    0xa0c0501110c0913021009060504090e0f10020a0f0c11040203040f08031003060605060a080f0a0e0f060919080708030c0c06090c01180b04090e07050a0e1012030c 71
    0x40540307280400000615240080c1010510704d0300b40c036048900b00300301100700c0c0110410310902d08a140140081c0054a1060f26400e00f854241400d000041c031101254241910a501c04007185490502181098803905040542e40301001600504071031028855802000112140749010400c0302c1640c10410390200c80150f03994943d420100c0301c2a45a00001d02149000018840c0780303804258081c0c200ca214110501c55155030340c0805c4458083c500c0300101080e010400140308503090780c0c14a90024024800256140130204424030740381c04840070314086d81c001014403603440d20402001a82d0b843c08110a1440492591004070902034124024000c03540800440c40036010001601c2000c17404204484852402c07465281c0c0d41c0d403403841000d010030012207030100080005541d00003038541445205180c90f2601c05400010612901c0c1c086183c0039051020a4030b03514060300c4030080104080040250900c0303030700809100c841d03601c14909200010504000681c00c1a030180b81240c012400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 216526906 1250 216525656 216525677
    0xf0c051e091b0702061606060e070807030e0f03040801090c0b280306030213020703030f0b06040303201c0e010914040b130c0908010e0316080703020a080d0501080f0a0c0501 76
    0x502c2e400b40543c1c3ca000350b0000d00810601170b0b40c5400c0c4510614140252018401c0c00d0340c80020342442705043e1031101c000f5800f000082e510a0107608403900c4810340d803084458400c2115005411900180c2108089075111200e6a083c056044510405091a1601300f0b00e003a0b04048003200f80740c070b40380414440003620640c0301c141c58020f9202c2401940c0140c0380d8220b4005110500c402940724842c21008645041030840d002c56091081c1c158424014161780d25240c15620162a2008540984400020300c2c1211070015402071009400f000a4000f80c00c0138440f10b441e002c0e041403002184035040090768072040058404111407680007040584d80040c00528107000305205c0e00745040019100d0341811380386041e49602083d103404540aa01c001c1124405d201d8400d41c681c41441c983c0c50340f2183c03400d080e401050740c0e44c0017007508c103100c1d004443c85100540d9a1341c000350000000c0c2d0b00030030358400c01008034480520090403070302c0f4a60081c011100d469a038410400e00180600750410034040c08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 216528156 1250 216526906 216526951
    0xc04151a09040207140f0703030909021b010e06040201020706080403020703060209120a080409140103050703060209030f01090b01172b090314032206080103060c0c0f0c051e09 77
    0xc4500c0c40740054015540d07500e150522441000c110b007900b290900c100c1941040c601c40104035402620307403558400c0252440e0042d508081c1d007081101007804a51503281011036142481001c480c0c0d503d01d0043c01051038207000280c28800395620041c1884403110402c40000d40c00329810060320780c81580180c072a9038103400300e5410350354220f030300d034981c402c21121105011900c3c02800071501464000e10284600c101a00c008031800c5c4402085035000361014000203080d03401900800d0b9015045074900862168004d00b942c03c01541580c100e85c0d01c05c0140074034000000c40c0e01d0303810b2040005101c4426460a400c00c40100080c03050a0061450300f05000d07948180c81603001182c100d0a50b41a8041e041c0e9070319240e03485102068845800c0e5907044081180010400d411500c0a8607500916803031615450040c10b10307a1f60080c01c11000c41c40500008404081c102c9040b80226200e042c000e003003c0500811003840a8030f0300540356420b240f005c4550311441c00c4c0e9031103c460084030307a2000c103400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 216529406 1250 216528156 216528209
    0x6090903030c0a14130320030304030f1115071505070c020927010b1c0308010b071703090307061401121b0815071404030c12020d060f0e0c0415 63
    0x551000c0b140c200012545a41c9001c801741006880c0550720b0f948000f20358000070781188841d1604240c240e0400d102c20000301d4201d66003c050240694400303484405201c0002d102c1c10b02c1e200c171442044101181c074800780107092015085000d0820b0b400c0101d42481c6401031f0121146e0321000703104074000000034030b140a502c0c80341e4101c0014090454194000d9501d154047e018244001c1c1c000c1068030980c442001050924a003055016240e4400903400d10089280c0da034041003040e9a00c840c1a940740c41d918220b82d00944c0f15610340b401541c2c40300094503104080d6006c0c80c01c02407000b81ca010040c48104151500c03454020390200c1c502c001c2e20310004100021002951001d804c601541d12760001d19441010300d688079040c43d544419060341011590407031801a400080e041d0b0b102e05d40309114000100c01c100e407450780010000c4040c01c2c002d50b07c1c1c60030349200007600b05041e41ca13980306070b07903001d82009801030512045600744a0408401e544510f09542c1e446212000600c0a03100d08142c08441d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 216530656 1250 216529406 216529427
    0x405061201051014102703022d0103060e0a090f0203070f0f090606020309060a0c0b09010c090b0711090426031006050c0c061e030a06090506090903030c0a 68
    0x80c000d0010340342c02859070382a00154800c0380d0011082d01900003031344c42c1c2805850b0a594494946141d9442188110210301600e0700c0f10740c090b020105404009640c1c0c1520304202c0380708524900c5100c04000e801303190f9540408130124141400c01d9001d016082c10380d41c4c2030342d02110600700014064890308140121040310700b0702a4250088044c0031032040410700807603041d28001c000703400644d0390b20301d040c204640f13480c07140a00582080c000c5002c28541384000b09610304480c0b420f290407071200e89445044007400c3d47c104c00a40c1d9a0840340900c03903013041411004280309080b485c2000c513182c07140c1100600c0c80c060301c5d22521354000054104559640310004108404080d102c4c10100401480800c0d8401d841c9110b00303941d5504002512449030040390722218520000d0000341810f01c00b4820242c0103060991034951140e1004105503240601451103140384107004030b03110746404040001c03100c026000900480c0340004000040b5030000880e600045440d0300c1e11303600d2810b20403c54078000075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 216531906 1250 216530656 216530689
    0x8090f09010b07030305090a110108040f08030711010e0c010c0602030604060806040602040e1005180c1b010504020f09060105070f080403060501060e0a080f0a0b041703070507050f12030105040506 86
    0x1840008111203070b0342c0001c2c2c040c00d80b080d2030030405a204e04091954542107548001c010308202c1e50783d001c6c107500c2034107502d4010b482009841100c0c040c0d5901c01640303420441d045400590744141400c031400c004d008410300520307150050701d10f6040840008100700904035004e0423017900000854001d03122540880c00030602202590141e050518144010750300034401c50030001001c102107000d42400e0300c00c41d802ca400090461507510b0444202d4081c500c0d00130001045108140540316103461301d10500c44080540c08000140351420b4410402805180c2822030300a0b2040c500300180b503600701c000ca420107900988034541c401070514100c440c07482a40c0000b0200c80c01d0500024a658002d01440034901003141d4070707601e154480304041e0342c8000411421603c0d6124010401c00700300f05170180c41d089402400e042c200d58880e07002c0c040040d402a1410b81c001032001885c0018030806000c2c80d0310640c3c901c4083d010818503030a40107520702040c01070320b10490b6030b02c0101c2d6281d0f81d14000406a40c84 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 216533156 1250 216531906 216531919
    0x605090c06040f1818110111061810020a05030117190803010303030509010903050912070f06110d050309060403053604110304080a030b01200102030a0f090c0308090f 73
    0x1c0340c441c6044803c04510410b4640251000c00902030401c500541c0c1d0b2000c040f400b030b0032802925440e040d0042110205403414840c8850503594242030501c11940300d10001c001040c60481d64000311450402028011042140306024211003603a210003141e04540440c0d040c0e840020502840c18103141800c40780644001c04072803c101041004005541240e000b5203041009980303c22030325080e500300e02001000140100300c02b10040c139201e6002c29460000c0c0341142ca025880300d410400b803007000d42040e004203d82c0042024480700406c03425a5522003483d125003181403003008a5030780d202c080c2c4010300303004003c50704c00c0001c0002c03520780d9101c2104045000030340340107101d55580005002809809581030184064120543c0b2088900a51b806940c5501e880b00e0b5400480060600c000e020781004042c0702501c0781a45404013140300045c0c0031000503a00c0c10031154140c1100c9100318410702150802c0114804218071140607000c0301e0304010a296038415140000311804880d40740250b0050703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 216534406 1250 216533156 216533159
    0x30f18060a0b0a231c020405010909020f01170c0703030f18062003041707020604230907020a0215040f2603040302060d0c030b040e0a0302060609130605090c0604 71
    0x2006402c185908001500e101800c0c58581c2d05103032101310801d040d404d4142c0c5250400082d8240000c2e804c00355442001c0c0e0f049905581d6001609540003a0300c000e01494440da241d20540c034054202514800003402e02201040e00300040340c1005800508401e14400c0114828080c1400303500b02540000c24a4410800005807544040d09041c0b69201903035614500080f40c203c06010201807849142c000b0000c40c255543d80e43d4002c02058034501500c0444c03c18881c00740183c070b0314400392000e4916001e101e6101c00c1ca80003081c00d02034008078064455001c01e42408206a004a13400d01e8103030301a14550300407c5c0255030001c682c8201d503c92800d525003910000784950800c01c2c010240d44484509101341c1c50782d5500c1c03d40d64041d0703020285d440b0004008407405400568884408518075003000f0030348000c1070300001c0c125012048280916001f0151040030180d05100300c6501c1300080710791844a08201e0380c80000960f240d00d004100c01c3d60390703010808800c402c002664901800030a851b9959 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 216535656 1250 216534406 216534421
    0x11041a1c05071e170a021e03040f05062406120708100f06050909090c06040b0a030f0603030503040b06011d010c05010b0d030c17070210120209040603120912020303030f1806 76
    0x107070813032100c03034000c810003004245421001d0003140e810383e510b52450284004050383e403480c02c1d40040d20803036680220400c0840010414400b040c4034044800c0140c80c5060101e00d0019039070086a081c5208034005c00559000000301d00602c5d4022031503180161523665918118030010841d6008904015074034180010001e9100c0000d022105083d0740602c107035100c0403c107a13a204090091a0344c0002e0a000511176100c900e8040c2c0f0007181c1903d00401e43e199030108000440c1c0107500b042c0c001842c000100004c1c45130440d107043d0040002e00c0d003004200840a0702c030f501c11182d41c01203810404660208010700c50250130400702e205004188000544080c90080c105080d006002c442d201e01c1103203400182c104000681c0c007403940150002210306500c040407103100c90403c400781e150075400d1180b032071142c60b00d10510010b1807107901d01640c0307207120007009840341d0781aa200c0343d41800203494203401030300e002c0181d80c2c205040c200c00040c07585075110001c9010b820000c448006114110400825 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 216536906 1250 216535656 216535667
    0x4140a0209012705010e030a0602030112060b03030c06041104021b06160c050c010305070918060e0108030403030c0602090f03100b0a0b04061e030e0111041a1c05071e 73
    0x800200362160114aa03900c00c4508102c440c3e01c0f4210b1200d04081c204009650181c1c20380d02d20140e005043d03c2d2034000641d80c840c126002a0042080c00d149200f6180030003079203114041100d90128002d5081c4190100c49558500d002400144182c20f6024208550349683e010b40340030340c0b108030600d0f11042510017016620001100c01c04060060f615000b08201d0250542400154201000d020b00c162108010740240502030004001c01100400000d02211501542c160151005201240881c9400749185008030181c03c00743c17403900104010070000350400c4000800d250300003405030322a40d4910000b908103114121480d094007841c15011101c020990014004c00c6080310007109194441d14450014080c501032500458501c010f0700b4110540e5031300c0c08030890894640420014800710311030f400d4414023082c031000203a012405225154004040c3e003554418115054200070300344090071480042040484401d80d0b850000c074109603c90000c8a140380c0481150071804c1c0c0d81d00000a10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 216538156 1250 216536906 216536917
    0x20a030b090f010e0c03060d0b010b0a080705040605070f020d060501060c141c1b0203160303031d0a030503070909050c030f1509070f0c020301050c270109060305040204140a02 77
    0x803030002180042e21080080030b049040e2081e4281c59066503881340c5002ca5a5030000d0040e5030f101d0301318420314000910b0340c1080c5000c1e00300844190349a0380c000c1c101910724803018218009100c0e06010500c00c0b254801d054481b12900207440d00407060084c0041a03518030f92803406850b060402c00042000394011100480c8107229082142021044040560b00c4075011960f29940030b40101001590500c40e140091868015001d03444c400d82c501d90020745007000c40b074001a1401a1000308200703051b01480303260750750603068111000003081c85a0a41d29a2181003004050000100104503440e11030030442001e880721360400c001a0421008400c0a43c1048400c95a4424440001030301190141c070301246802d00902002c4c1e4170f4030790b0300c4203590380b0460050200401204103e883d015a0782400ba090144480ca650140c2d83c02c008080c000180c80410b00e00300c0240b49c10084842a039034056440e1086400619001417a91140c5c0b00080180c1481450a1a10030f0704000384080140d05038001c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 216539406 1250 216538156 216538159
    0x81303032a02160e060904150f0510050405040c0603050c120108070e07020a0c09050901140a060f0506190f0c05010905060f01061809020a0c0c0e06090c0705031801050409020a030b 79
    0x44580c01d428241c00e0340d00d0f20f507015068408400c40b000c00e078107044c4094601c1e0071030710580581d07100070300d4045004221450042041c4440d5240c4052122904203200010080c3c401941c0a02207441c00340c4031103446c8002c602c03800c4200f640d688009504010108152021104440c840c0c075200d5944401069407800180100e040e9540c00300c0204c0c4850740006020300e1010350041040c1141850814850020300005001071500d54807400902c030580d0920354050f125001c4098001025820301f007001e00030b480c85812181c010181000a10f203114014640002c21201d146000500007000711000c4030b1500242000034000d6007000c102d8010080b0114103980715842022009181e40e9070b071481100c0c241c00c00b02d502910700781c100b9802d0018040503001484001da80307040014004d44035595a1000800340c0d40040b06180f04a000d00c4407500d070011032640c101080c482044c0c00c0425544030640c6034070a140f00d04d4042090051080140d9004a02382d500400410310700f1522030b40c8a10002c0c01030701403a91400e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 216540656 1250 216539406 216539413
    0x1419062303010513110f0d14131502090409021f02010e01050613091a1807050409080a0c0516090608010b0301090302032a030708090102061006081303032a02 69
    0xc000d14588441620b040343c1004010040740d185400840006111715200c900c0000350030071111044040741801058221b40ca01000621010205001e02c81d82e02c000e450395614101c903505c98000b10310055205d0f403169050718001030381ca0480100040051644200083d00300c160030800102e00c41d42030280c0140719205130000d02c01c40203034081305030884204940c03042d441000c01e07104100c8240107070b010740703c0135114420a9161650b803a5682e88110002c82e1483c50f0718a40c003580480c045d00c00c0c0544001010706850902c13005505550341d0149000356442082080b03600001081486401c00665180d0f43c0601d412001e060703200c6010301c024000c0b0780200c1c000d660809903c40030311300b0144907400045405a02440c03c101d02040e28603204415514600124503801c1540000000c00340300030420644980c1580d60340f040c0a1001a0400300300600c001c2180c40301200c03c0009035004040710340d1002e00724001210042080c0350680c002d00304c1c5134000040d0204442902c10074012905407811018090b0220b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 216541906 1250 216540656 216540707
    0x301050604060b03070507080c03040308250809090604090f0302060603010b0102151f03050d0201050106031d070603110f040e15030d050d0c03060302120d200601141906 74
    0x500040d12410f01c2481e030b000c4010400605c0c00c034440d0000c0e1081a10800001d0b2600c0c1d4060308251450700150000d03210840000b80402d09400060340c034a14200c40d82e5003035201c0e80d083d41c03145c000500030111814080d1000000141c056a0380780c0c003ca042540c0501c03190300303184460400a60300c401c1291030318020b61815410342e11541c0006240c9505c1000c0c82076190950b558240c070103c107500e22038407600f0003004608002c000603100380001c0701540d01e82c0e400056070b580751031001004d0301c1d81440000e101c20704a286100305003101260010545116003400304000d011141103c00d18828040c01c20f44041002c24040342c40302c000702c0c0305801801c05a010007940d2103103904142d00c400340740c840c2202040003001401078600c115040750042400740e050014400e0303501d401041078100342050480040c4c101307440300030407950040000c082c0107600340840140d02c180d00409507aa40c1040c042c185d102020700c1c80403507084c2d03207202480c061250307581c821010032a03031440c0241c60001c0c0d8050100c844001c6208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 216543156 1250 216541906 216541909
    0x190905040911030f0c0918010b0303030903070317061c08040f09140f071704020d0c090209150c0c13021303150506040216030f021006323604080903010506 68
    0x40e000e05c5003400514072403480d19a04c00c20f4001c4000d01c201d80090f952158040030340307507400f0300c00f0b035200710044000ba560390001460000c000d185c240382000103454191003844026192190030f084110703071090410f00b2444150a1a14050056502c4800e080000104c041402549600a070140e9480c031900100141c6400044140000d0203c552100095981d4100701038241801c02c0590054000b50a4407480700b2651035481116810f034014800d003e4000130324205906081e44d0211220320312a0000d400c4c0031415140980340d109400400384500c0000e0446802402d25170304442d00294410a0300800550300e03d04001030320301c0003210301a240e20b03210000d640e5007024000ca400e404040d4a0598140300540d4041c2c41c2c1c4004241c0420851181c0c19000300c1030700c41c1c1d200c0c00d8054402c3c0c03114441c4d400400b00150a00c0144280c0c6540b00070143c615020b9103459034108590460415103aa107412807458810341c4094022071200034806040300c0a10060000300780c01010861015402841035030b032283c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 216544406 1250 216543156 216543163
    0x10e06040303141321050607090b180a081606090e0115030207060209030a03031b02030f180d0c0e06040501080309030a03050f0d0626070605190905040911030f 70
    0x200240224031103103c20000c0740c0315500140004d0302c2410213482d841ea25900399008241030307401c078900e048600d10448800d00800b08440341c1d0005880c5000c118403410856074103418065a03109000c02185a141208075036114859030002e891002c003103803440041c1c03200000f81c0001900c0b501010564000300803030315150104641d416200301541890103a148001c0c114020f51000c002500d0056092004049a64040c400c40c02c07014000e40d80400c03c8508442c0e00a202c80c03140c0ca079030040d980104080380c0f0090000050b1a840130103440300301403812041c1c000c1078072203544131002071a516000c00086240160400c00600600040d1401c000c16070302e0704840366603480791720480b5526134020081580041d111780000c0818844800a643c2030100b6183c00509a03100f0b030700b080c0c5135504416040c03001b0340300b900503002a980e0380706c0086c01c015184c0a0060a5840b0701d020b0f1200c003d03443c807000e07041a030040818400400300a03104000c0c0c92001e0424121100003100b00f40d20a00980740012842c11000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 216545656 1250 216544406 216544409
    0x5010e0105030f25030b04050f060a0905060f09070302060406110d09061d0a0801090503071505061507022706210705010c06090819020c090408070b0403120f0b010e0604 74
    0x303162502103d204040070084c1d004d1984154802a00040002a008640309000324412401000c9500d1469541030038600d0040a141c26549040030741c80c04985c0029469411421344098030100e5241d01950605058543d0006500711800240008429a0150214481303400c800203441c0c0ca4810048200c90b40c81d8544200c000041d10360011002d588108940020038070f0004000b04502a5200c01941c01d44160742c07002d641e150000f0550505101300340301d41c02d05104d5000380030051803a001d800100e12112a03441e480d040500481c807102152a100e0704210450b40e074100314a060004220881d81d5480c0031604036005004100800c0200120700c83d540c03128010100c05031100c6400d14004658401c522401030b16950b0319031101001080341035000b4040c850702e5080071000b80c11140b10107860103100b882d516014201980030030010030111000d4403030b10f50340000314143d1610340e0b040450760102c01c00b1851429503d021020701e54803680380e120540102081e200c03002d0520a441c2007100900a5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 216546762 1106 216545656 216545683
    0x115060203090301180b070f05090901032907050306120123040c080f0c010503070507020a0f06030f05061311040b07030302040e2508090a08030a05010e010503 70
    0x280a590207400494080307803c40900e0340e842a59111004180504120500300032390a014860310444511307010060401040e540c407800e007155441c0e404400300864030744640d0706442d140c1103800240d104645d10344030103003540d4030302052001e14210f60740c0c0110195a00e640c46000c0d0000407540c0d8020600b9680d84d0b51142c80d01b480c2a0030002e07119001003036240e004040d803500c3d03840c001034101500c83d421b01e03001d600c9498200c810b4803036000b071708002548043c0aa00201e1404000c0e14007a00310b5400703a50070b0000c06181d1103140c04881003621441d4010091000d1240e032980340d50080131006211160341c0d07240941d2950303610b0041d00203030030880000340c00160030803542400e00303e8140c000f0140c8080c80c11140c40f414403101d40000754101501400181070001c1e00004041c4200c21207583c0100005a0300e29000c810314004003802d0284c9020f14003504004150703070900090101040700c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 216366906 216546762 := by
  have h0 := BRFrame.cov_init 216366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 216366906 ≤ n) (h2 : n < 216546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
