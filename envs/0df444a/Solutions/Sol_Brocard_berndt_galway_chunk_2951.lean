-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2951
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:13:29.929993+00:00
-- url     : https://prove2.me/submissions/bb62bc32-9957-4bab-b24b-d1a136a46c36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 530575539 ≤ n < 530755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 530576789 1250 530575539 530575541
    0x110607030203090708030304111909061e14030606100e0a030c0f1208030f071e020d020613080714010608100b0a0f0503060703090510021611090f07120b13 68
    0x11140400c2070446a486948171860707642d91200b214082d2904540c0c8220100c9850068103406040c0c880c0c1c401c0103802c6031039446e486c08a80b010f500c440c1c0340c40d0400403041c1d03000000303106140c003d1144040031400208010003107600c4500040210348503404281010030b540340100c0000020407406081605815101c1c41d0481700380e1081c1c02550300030702451100103040b440152410844603801b4035540e045840740d007e900d66010004c0d040d10180603403410440091440d4044690481005170b00030540a004030801030704244018094488040003224540f01190a500488024542c05a9403d2124400c44582401401690445001030051310700c2482800ca0315007141100711001c640010040d070b940c001d811140c655511816401d0303003002c0000307a145802548500181400f580984004107845800e120032640030081c0035960103084113107a41800140446584860401e4503511401d061a001101e481d240082c054802c0050340001010030f0400358100c8500ca41d07015101c9104640d514000300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 530578039 1250 530576789 530576791
    0x130303020709060e07050d0b01020718050618012114060f15010f0e0906131d070b070b0610050705070308041401031509091110050325090b0a110607030203 68
    0x8800c2d608106021548141c00182c0c0c5024041c07544a15141410b4550181c0241503a0b24001d41980205140085c3c001d0030390342c0010b000d9003c50000540d61400e0410044504c0010203005000b0750a500140319410014019104a51b0481147c248844081c81d00c01e20b5500d03640d4040c04c035070107508140047c20b0000196140195a0382180d0345408c035030000112080c64064109200081e40310b0210503550a042c105a80c20203006802000f8201c041100328059882910015403102036126050120860500c00d0001034441c0c00b2801d841d04c00c1e1501c80f40751599015189601c900328030000184050f000b5401c80e058941d10000345d686030f076541d0503d0701140c0c000c0d1261000f01c49031001c6040741036100e4814142c050000c0380184020310f0411001c0c4c002041c0111003210704401e00301c0f0070141d82d82c464035115a01c0d0400e680d46681c901e8043d0087c051120309540003248000e00154a804d0160414891429540b0340d804240d11240c1c03044044446801c1240144141c1c007c100c01d02c10150ba01d90009c1d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 530579289 1250 530578039 530578049
    0x60f0304050d030b0a05102d0909181101170403020a0314120c0922060f06050304051023103f03030b0303030106020102120c0405100c081303030207 65
    0x510801c60b0941c406405a0f070000c14803643c019100c440905c80c0b07107040900d0014030f012030314141034849944024070780300a19480725014002654608080b140d6441f403400340103401c40380c005002050511100201903503588a0003061111003125800582c2d1140c00001c00401d4400300c41152800e1905019445004036881500051483c0d034500000d0286c2c0001c490089681d00007010003551038480e40c854070b81003104420ba000d0043c3d82080013a580c094402d8550404409001400c0d80c03502d001020b001c82203902080500405104200c0070841c0801d0300710101101400114030b038001c001001001c8104252102c811076000306c00e108014a9810010054420146034100204403009a6401c40c7ea06044100c0c80d441d020b0000020b02144480300d05000341c42410046030b104904d00000e800d6400903040300300180e6021903010b1002e84410030f0340d50088905581d180c13400c0d00301004036103010001740c82c2c00b0602806120000c104442d06085600d4819a0f1020003109030326882c000752101c00901c64 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 530580539 1250 530579289 530579293
    0x80a052a0d050703050d090c1d2203090b63040b0f0405090624061204210f1206060e150708030a022a060604110405060f030405 56
    0x7400c1c802d00030003c9a6020743c05458180c05d00d18034002540c05440702c440100e030f94002005000403402600c0e981c40e1401d00364a80803140620b40041e0000200c0c01d03000d0440303142c1e8408014100443d130170041180c01c4c1c515041007079543c0c1e08180440729030880c0c00301151400c42000803400e070000e04088484e0340c0c0901c5117070b00810000301104803043c041c511681603e050841c0402c1e079a2582c5000d501182c02100d0251105004503a4240002d04403902115081a5900500304100007404c00300782c9800308004101e03070f0b410100703103000124401c0d0240700d84460304040703907001180a0120710100004a141540d12410001c81c540701b0003802c06202c826600c004c0703681101005080469030080805680f40c03552001040c203007002c02c202c0450403c454003445010104401030200d05103c00031840740c0140e0790090b03600c0103034142200c1504202c5a00841c10b808c10741c9401a0f80d075012964a0704980119004035400340100d0140d41d0324400d6502a80d4042d030001500242c182101d030103148100e0103101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 530581789 1250 530580539 530580553
    0x30c0204051003031b050f010e0309120a0c0b0c011803020d090e010812030429061008070f050c030d060815100608010324090f05060a18080a052a 64
    0x10b84000b9050b554000140802c0c82050b8031800c00603007003946030302c450180302218241484004810301711071800350205900e403c000395110040c28030300d640080200c0c2010051001040c01c2e10744034500e449a0180440d0508000385012111400f504640d00b52020340514080f01580c034a006556100c86140c02c07400710750400d80c00107116170703881801812641920094121840c0300a82c003410750340010000c45a0342c0856031801085a42c02508072801c0903488140e40081c1004000c01007880f005003410401c0051030000c212000e540042d10350401505410102e407582880e443c002d00b1401a05c84a41c090352420350b00058031034000600042007200c015a1702d1541d11245030410340c0860390301414001c50b500d10010400508400e40311039810b41041c0400d811034031940f071480151400e000040e00c517016507500000038030500b88001030300a003a110080000004a100e94440c5001041018000507070209000382c0c0c00f802002129801c0499100d50340a40100e0088101c0064410842c2006885060 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 530583039 1250 530581789 530581801
    0x120f07060e1005090f041104080a0312050403050a140c2d070b0a0f05070b0702010b0306060307061b14072c0f01030b09010902030709091b062712030c020405 69
    0x80a40b08019503a0b1582c0c50080310f07409009011840884880d001946c481030b0103004490000940080c0c90204040d0940440e581001802c000080d106030700035501e800e05200c0007a4000c0200e42c140c81403418055a114120904041d0034041e0004806040c00340b059603010031155141c24601102d602e05114030341065009a00e50781c0c0c0303a24020f6101a000800070800344d40c0c09041d082000011610b849494074100343d85002e030315202505c5900140c1e440f9022007006140500846034030800580c0180300f030500c0d0010080c16481c1d150010740360100145403071410701ca0611288299921a1720803541e109903182c1445140c1581c22588654ac481c01140d510344280e04a86018010711812a60124507425501e450310106400b41c4118801c0d1f50300d008180041e1020700520300144180720000448141c50b05042c11f10101c0740d09000c00c40d4504407401d0041c50740040c44074404e01c407640029003d123009881d5500e2200c5490b0000c642682c2c1c500d00706010190711036490032005d80b00351802d000d1030300e0382 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 530584289 1250 530583039 530583049
    0x1801020f09032506080a060305100f0513121409030303250305010303020631050d030b09091c18030506011502031e0a090e15040507020703050604080306120f07060e 72
    0x4040c021103d548003075080102522440c042900081c0115001030101d990303a0310700b0310341008149204240760315405952401c0c0807520805501c0201e100e561411031306280d40300c44109103040c0b001c0c1d0a00450700c56034240002d420003919034030300002c0d003100e6076400c00a0350000c0000d07020030349030403102040c0f20081c2c555100340102412294150024121500c0780b02c00741000d43c104030782504012111080d51200c0101c01e40480c03031514012400b0b88071000043e04002c05403207010001c54090801c074010f0200c0c4440009907038110701c6030707404400b8007003d031014220381c100000f40b6400c924214a440c08814880c0100701581211385412407194207045160b400da85038021901e182c6e503001c110001c0d80c850660042d00a09500081d490600386c02c548450011101c0340081c2d0f0369685210241903084c00c1030800c0d1140c260443d05900080c25498a160788207130b5507944c000c200174000000440469010340b00e0442d01c0344200300c0320085c1c80f200d03d4604419669050940318140008840da0343e041c90034200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 530585539 1250 530584289 530584333
    0x6040501080f03162103051006050901020616050c031809060d261c06030507090608070b0c07090603060b03061b0904050c0d06030c0f090c0e091801020f0903 69
    0x20000141d8240a01515203610f80004c5110036100b00c6403080042e070030040410307045078290f8001d4a000802c3d00303051444030407100150b0020410701504101000b0035a8000400c0c6c1e0f441060b102d0003282c0d541b801070044500340030300d42980c0801d210100751154000b80c40c003484501c442c0b09440700c206a555090401802c000c00900140070414541c0140d00300144c0c0d0383c90f4445a171110810360780f91804044130880860f41074025400d000d50384450600400600b8440000200700807030043c0f244a05200049484003030300e110b031707405100c000283c1c8480c9000501041c0d00500c140c220400c1035590706c0c20120003500316400d01e9442805480b00003184612001141035001c02c1100c1d80300e05040c46041800020f0401811305041084184190303528811385000d5900070f584110b0180c1d00042ca06a844810108680c0050307624908000081c0e205c1035021000002d582011103004415403070300a007220f0071150500507440b90394000100c860040074003038010185914148d0441d214006010000c1c1c0365500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 530586789 1250 530585539 530585563
    0x6070c0f03080601170a060302120a0819030b1f0e03070608070e01030204080109140607020f0615061905130e09030d0207031e080f06040209030a081e0f030604050108 73
    0x140032051901081c4140c060326444081810b00100300304c0104494140082c003156101e41d00b5490301010300460030060121190303920750100502c0002041c1c1d0710410380780511104100004004507520f00fa661007600000c0040c82d002d4008089050746542107094503994070403000129095031500303072030745c1000146a0110355007030340d031414151640502110210070400c00241003507002e10002c20010401c0c420940c90380d200701c0000c0c1951b003450540c11b0405e20300904e820300355046009074803010000881d03001d40c40f42807200c401d1803039030450002580a001d0888080c144c0c61301540301c4c10b00d0540000c014064070001c0703521500e2050362440710030101c01c3c040b26903102c207400034002200b681c040c0e5006042031910074100170994294440003412000480e01c104400284403c0c14450311b180a03c6446820a205440c10342c40c01c0080008650740c1d03c0e10100c02411400001120400640e144013260364204004100c00c1d61044410640f0300b0301d070815107580e80f1070b44ca00310000030340780400954445060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 530588039 1250 530586789 530586803
    0x80702030a0906030f2a0215160e04020d2414061204050a021005030f01060e0607200d08090a050307120b0a06270615230d020403080c06070c 62
    0x141840c0e0f044001d081032410030800c05494040070450504182112841240d8160300c40441c4c1001c1c4400902e408880800007030030303100b090184039075141003462403800d41016060582949540f0000b040081c420103d050000d1407814041d418200302000001c0c01d040c0110a0342c0c50038179214502d0b250002c065101d100d9000900300207945040740c038940081e40c024000c400f40ea1009c5803940100d038008400300c030400c0000b0800010411b1210101c15014054034281c80d200c91044074910104006105441000d40b444801c41d007000e081c043d184100ea80201b0f401382c81000c0b0780d81d4a2070701c0354039908030700e041d076200e000f003a41c01080358140001c0301030488400411000032440c903a00d8407040d41138054004264551203038400708050311002e090f003100c0c1501400300c24110142404040c00c80f070309074200c0c880e2407154a40511a00c3e50181202c2480c4800e00440003110078083c4440d8900d01c1451010502d00f400400d0000900410002130064181c0e41e4007030b1000d0b565025802c40d100071144400400c61 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 530589289 1250 530588039 530588057
    0x10e10091e090c09031e170306191502061e06010f050c01110301030515060609100c02120307121b0f020f0405010e09100b13050907090e0c01080702030a 67
    0x40500c09420800703500c4001281c004030703180c480303020a54140080020120791410005c00400c010b0038034820818a4041e544040e0303000654030140095400900300110340004008541d680d501c400f1001055208950240ea030256500d91101070b40b13070b54140060150080740c4c00588109035900d041c3c405401241341103403050351001c0040d1a0702648200101c1002020320600c80f04600c00d04c20342e9802c5003010035864a962540c41c00e20301c3c041c400401000c1c88000e0205025841d26a2020703540b1294084441030f6680072903140c119080844010003941c04454103610010041c00400104505030144100b403210103800c540a0390728089042c0c046801c0c008000342c16000ca12800c003003c502034402404407d00b07161820003e01545c40030b030031100c81034054009001303080c08108480c156842c1c00260034000c21400400148103000c0c1c2c40ba1200d800341d101c000159812000380020000340000c1c00f01082403c130032488a60b0b496500844503804a05008040394a2a0000050f58031511a07540c2d07100075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 530590539 1250 530589289 530589299
    0x10207080c1507120804060b040b0f12030702040204093e18030619150b0706050a0902060c070602120405061903060918060506040509060412051b0606010e1009 70
    0x1d0040d4810904007101801d0000c43e001400000390703481c442e0745590f24605281090300340002102d000d0031079030b44141d14161240ca200d80341d032040b4480d04001140c030000b0150f181400e0508501c10400025401480045c0101c1c0c4500e580d407202d05040c0b490f2804804682d42d40c00182070507624117044505001c103070405801c1d542c46100003000c082c0c0701d031030822078401c1c0c8920200345414400c1e141c0c0345200f11400502000c80e00c140c810892640d18850090004500c1d003440d0000030321130070402400082d01d401c000780c0d03d41840d410582000e07601800c0165240440800c080c1c8952840c0226401030048072114801459200d041c0c409980d00103048910b000d000700e500c44501800403580c1018141c84000000f2110814421446007030400d866103580232100b0302e40b4104850009241c64421440c1006004d41c141c0001101c03a401030344059200e00c0011800300031341d43c600801030b50f042c0054901005400403400411814003e0b0380c05e8031460383c0000d81d00b040060700721000d18850f00080302c40c901004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 530591789 1250 530590539 530590549
    0x818010e07180204091a01030c0302180114160804030b01090504032007031403130506042d05091801050a050f061905090c0a02060115050306101724010207080c 70
    0x1c040e1102c0c2d08010b00d05961100f0207010b448505564048642c00b4400040710755030940203591015045140c218a0081d01d09070b658605144114051304000c26030200c0c9501c5030420040303400004045508a8914910b8648460140d00c01c4c0411980c1d94004000062204890b0041c90b000795030580f100740001c41c659912140381e6032480d50030981c91080700000000b0600c004800440c0c0c10000d800786a484080c0b8052860640290b4829030051501304020440d01a0140c8040d107901c0204001444c1005400c4865610103056001141d0180d900e20502c0283c010030701040d642c0709500310080c0318030398030062180c0407100120b92180d55000b007034001400600e8940910322403104e03544601740005444401003210a50200d81c1ca01c82910001a400b240c10f404006050050915900d580c0c0d11080068008001d400098419405200d05409001c0400d010708500c2c09071040a01654280d031034848042154088040341011082c1c0360261069665403010130042c040d500914010000031203144203200c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 530593039 1250 530591789 530591819
    0x1080601030b0c090d030f020714030309010309080c07090204050406080c0f04021b01020c0109021804150506040b04020c01150b071709011b0308091c1b02120d0818010e07 75
    0x10202804c10180b821940d603144a0030b43e16000755621003540d5045000030345031010302c1c3c010100100e4081e0984846035000800c0f034010310020b1801241d032400c01d02c1c0103240da0080404038502800340440c0860705243c030307601400031140201d40600000e0343d5020400d8a42000d80c4c3c606401c01480c1c07000c0714690078a5001051070010290f0565000e00c9d135032584508a80205409160694403000d1910551600c1e40c40c3c107500e0004030003840c506042543e82c2c2c4082992040d0b0306100c1e41c0d15817000500c0d5507100d070b004915400d0003800030f41d0b5910032070007080e008180c0d2009065200e091a200441c03103102c480300f41d89129600c00304444000103035000c0100c813900034410b0f46041002801d4400140c080c1d003803a072600340e4400c2c2c80d600c0250804410007030401c81c1c0000c0110511080075801c0d280303958881103a01d501e2001d51302e500600c030030b24000301da001101003015034001d104058808a0325a072106403203215008081386503000c0c00b83d01e0700003801e80d10f200c0c3c681c0080d540510b40034410603029003070368 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 530594289 1250 530593039 530593051
    0x2b030f021b0d061a031005041403040b0307030f140103150606020c060a051303060908070303110310090e1e030c07080a05031e0405100806091e010b0a02030c030d15090501080601030b 80
    0x100c0340f400b95400007070328083c02e418140d0011a1520203020400c0085009009d00e042048061418a4102504803010b070100901150401da161404856042c40e154409004c0304100c50707a1507113940e101c1c2041e2445c0c0000c2e41c0c0c810441072030901c000424902c04950160000d100074021850030420500848454105480041e20400707007540020004200f482412056440b0b0900e46450b405a03040c041e08a88580d01c50300c44010041041040720040d880e8040161202c000000a5440414110350b10b040500c0d04071010400c4607600186070b08000201030b061005212080b11030f4030352540d50b41902c45606030030040c10b543c000d001d880800c07031503110903c00e528120103403582055a80c0001850411080c4c5600011981d20400d000706410402ca50320b50000d88082c00c02460039601c0d200101c0d02005200d80b403160240407403840c0381c141c400d100300d40726000c4e40b204590310761000280c0361008000030382c051100500041400201c4010a0103100c0c101c0d03440318080c1c80c05070f20715199095188001458 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 530595539 1250 530594289 530594321
    0x3160203130f06080f0415020708121503011109090708131203090c140904030f200106140114090d030302070807030e0424052b030f021b0d06 62
    0x41c030041903109600c510020302c842d506068034507190480191034aa4040c105100011030041080082a040c482d00c541d02040c40750010fa882107079040021141c06220000c0c40a034804900b402441140d0241081d01100120000c0101040513581c0c8801d41c403407038500b43d0300204081d00046945024413502035001c1d400e210140c00e901d010b9034804401040c40090603011aa90360452400e014290401a001d804090341198030140070b03c002a40c0c403038008100030200110081c84049152144402e41c040a6040b40c0c012f40f10580c900103640039110038020341c0f85120410307014035007a61050322180f1107004100c6003607140100c0041800003ca846190039414180c0820600300024001740042c00042c5c020b030b030f40341d124084490800041e41c425015a080d40f500002071220008007112030441151021224445007100c01c511294030b46084403550400d030f203403019802061641101a5000c4400c0300d41c2925010041d0340040031a0b0003a47d100950040307202c1c00c0b103000040550344a20010600320710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 530596789 1250 530595539 530595547
    0x70825080703060204080607030b06071101030b0a0305010e100203100e060a0e1e0901060605091e0901080a11010c12110109060e0a0309050306040206030f0a06030512180405070503160203 82
    0x200e6149010182d9108440c03882e8009400c10030703005c1c14003115820080914051000c210084001081c500801c10041c1915a0303a484d8900160302a41c0103a07800c40e0301514910030140d807810440c0c02050140d50b2400e4900582d514150a40e10300d1088030300c0390f840c400c0f440c9203940c10031554210540004241c0743d000b0001c124003049034041c5000c6144500072100086000c00300c468901e0000407406090071300c0682c1090b100340320841d0010291600382d4000c3c0c45031080720758910210812006100301003030308204400001f14400d400450164450b50080c034500100c2c0c120a001120f4441100c00c0160195801912941d4014403980084480114443c00403447c4000d03502e81004407642c0300412401a44004110000c061b086a00c99009000c2107020b0301040c42d107500450030034030006100c400d118240d00c0016801510315840003001d15005011126020034280809082c0d078018050310f5023981c01012400341e11310b414040d00340701706c5030356079220700b5a2190826140a02c0301d140414055000502c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 530598039 1250 530596789 530596799
    0x30327090218031b0a0b2a0a03090b0306030c130e0f0706020c04290d1401021b0c01020a0311010905011401090c05040605070f0c050d031709070825 65
    0x10020307040c00e65161010580d070386800740800d0302c0c10301c4031018003111480d8005202c4e1169900c1da0890304446920381083c1d035801d001c1da400c0e60040300e080b11b075000506102c0d0460040705e600140f2040a07a10a481d000442a1651806186400122038241d850b500c00d9605a0040c1802c4006989c0c208210310046001102000103d04240c00c00c5000480ca40c000e8104015040d0304108003a0404000e540c20008410305c9890b609000c02c01e03004500946a110742124070039101d59820080b56500714040d000c00250000445000c1c0d449035540b07011410200d2181f29105030702144003200050140c00070300c21b0707450a550690f1090801c0d80d0303040455680d101050b010410070b01641005012100f405031940d03041440d003200f01c0304049040410071a003400203124140d08503040700c941c580c001000c1a9404c42a01c0d11013109845604060f03013100030001c0000400d90018200c412540d024a1000c00d1661406402a5103003010f100d0034001c1d81c07100e171744081407040c0d08407280150041c03052161025a191 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 530599289 1250 530598039 530598041
    0xb1e04020723060603070603020f0301090504051f0204062c01030b0406170c10020106060804030509220510080606060d0e0307020405091b100504030209190e011d0703032709 76
    0xa04410b006030042010000e0b40c0c0713400e020140c003411141c1011070400c50010300340303101400140030300031141d95540d01180030310071704000100100784105851050f1000e0404003002940051003034002050005074681c2000c500e0024a080036021403c44800104219004401900d00c42c08504d402566902012600c80104010a607030808114020002401c12100f4081803091000034035046914245040c0207507a0300404554110350140741040d140c170880c0000a1503520340311104040da9100690b001d008880d95001140310ba01018140300c00c81e5918001951900003c80f003459200c40104128141c0203070b5139110b801704c621031804580c103020181d4080740803210166180365455002c04003100080d404201c0003149404256541c0780540e01441c4003170b00d54011400700a11502d00c070390014000041800c0040a80a9040e600340000c3c1d8031103821900820220054004184107072241c502440c0300040d0020481303905580341402000404510050b9500078851046050b15101d0b0000c1c944907a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 530600539 1250 530599289 530599343
    0x8070905030f16090b09010b0c01020c100b031c0f05210718090209090c0309010b18011805010b041412030708040e090a020d1101140d0603060b1e040207 67
    0x10740d07002003200c3c0f2950184149101000d074860000c1c181030528009140e12200c1d1003a044a518004031516029210340d190702900030151604c1291058000b406000f20384d43d041224890401e40668115449000e492000284094504400700b0300c54841e440c0541d21071402003201c000d034059414400c0012080d2201c215905484400006400c155101c1e480081248028003c00e00340c402186030100f1341000c102d0007880102601d074040000700020705072480c290448002442c00904109159242c2100601400800c0c01540c00407a00d09480c1082c41125101c2c00e81603800b21000301d82441d20703010b01030001c040115001d6400400c4864640e00d02c0c00c0c00c1001e01203040c07089006035119428985d001e03a01d500008c0c00c2c4002c80d03112101640140c4c07640d40b01b510b0001d401482c108145106400140c3e82d11005161a01180310000b0720344d481400303507510400c141c0744103c50a01c0254024010031004040c034403070044c40c400e100c180000c4685404e82c01440c990340300d581103030011119800315640d10b0136 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 530601789 1250 530600539 530600563
    0xc060706060e0c0a02120a1724030c03070b070c031a160309022103160308090c0109180e07090203090a0605061c02060d0212130302060c190807090503 66
    0x14441d907040c044103015100180e440140710450b81d0500d00002402983d65110307680c201480c00001035201c0b402441b50841c0d000525580014500e103060461015404080600c0314560b840c03406d400e03116151030046400190b400008000307180c0e16040c21140e40b0640d200c60001c41d06011a0301c400000038070281c0c00b00000150000c074510709880c0140c050b25140d07184041c0c0208041c500f002c12001640c1e841c0440e00c010501040c00d22207144000c5e010f510b58882c0240b61401c02003c40031a204055211113503501c00c010b0720301a13940c0c820840b001500d4000290041e141c280390581050b101141181e8000311020035254100c5400316550000b21003246c0c01500e034045543c2000c103e400030310000380682900210169090481402c902288121084c51000700a106e8200040e0311503151002e0b406031011001002001516400d1424200050040000085000d8010040020b000008881c103540700b103440821842c0d01c2e0151010221802c0600802c60400d0041c4003a0204a41d1020020030b60407203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 530603039 1250 530601789 530601791
    0x70f05211014010311030a21091809020103200702060703120507050405040c020606130b06070b25021c050c0f0f03031f0b041e0905190c0f0215090c060706 68
    0xd4110b00744170240200145103e8001e9006042100c006141d03d2421714039105c1c01c00c1c404044004038101140c495013581d1003c0b1415070140ca808890030180d500518080b4400d8904018121003561422000c45502c1110315071140700b0320003000981000c2c8010005030340303e0310344040b030107107000510402c0798020344525000400c0494140924100303803183d1001c821840c00249014034003c0009540922640080403403541c0301c0c10300c540c0944a038003d444c6010b41c026400e041d04d2030b1510344180e07601c1c8a030140000c054601984800303e00d002040d59061048594029003000c5500c62058409034480f030140d50061050b6502a011440d0512001010710010401380d0f650341448506210100e80c0c04103061309000301c4900400c2844004c1b8122403c079448040c01007800c80038010481d48641d190b500c405001800c1004016400a82c003241c0c0707040c0c02c11080704004d14081c5280407104200c13a4210700015038040403145421030302510b07000b0390000e0300d131049640c02a1002e000c11156000035900321101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 530604289 1250 530603039 530603041
    0xa140d05030d0501090f15051207230427020f1507050a03020f070b0706050a110a1106070807230c03210108030703020d0f0311160302070f05211014 65
    0x85031780d60141c2071000c00c10240c1808180542e0442c1c034209074007441030320310420b0010514690b0320710501031000280980e40344980d42206070048032282c94980c01546100320725040501c088091f105021401c11424010108060051503080c01500008042a140d00608407900c007141004040c00070302d000c074411000303015184100c0c40c02a141001e2020030047c2608003130402d2044800000680782c002e60040c1020400b9154024a1001071030f21214407a0f02040002e80e071100c2940000c589034a444252045515a9440d4501107407440c0050b10300c0c20000d8111620708040d02c00155828a0f24030380c1c180c40e80c0c0b400d4408110b0301c1c610b500020480710762402040b2861003410794000814010140030000e14034150f500d07030300203484000c0270301291b0512412184121149202e5480303c416810940729990380e46210307085a06480b04042000c400510a000001c43c03d40210300d403c004448018042c00c0364950b82101001c414142c040002d02c09204a070f8034899021160b0042d000101002072303540080f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 530605539 1250 530604289 530604299
    0x301060c1b061d0a0f0b0c061005150c0f0d0e0a120203061f1e17010603020f0d08121f120506041112070b09010f0e0a140d05030d0501 59
    0x440c801d070107503055842240c4040250300c0e04040080881038100d2114070442c1c140c04000398050001c1c1e004840c040c0d42e03206002c07550702c6400b001004030721038030300c11a5855543c8644005e00b242d030301d000311900421524580408101c800001d0308a4103000b20641d45007003003400c1c2c01e030714016805104500007910283c1000c0b6500302244800c028103042e40014091040c244c0120f0307030301c02019208800e1801c17031880d49002c4401e081c0c4214094080c038074001c50382602a01c150801e061441c099604201000041300c0050b4005102c0c10080b40e6002d4980401c41001d0000c0006910403040700340c2e03164404010420f801c54004588507c21030390007581c81a000c0c402c0c03104008800c0143c100f080c3d856803040503080032a00028085510550180314800415500b40100360350045482c1c42804601c9400d1000c140c00d2a000041e01e0749000a0703885048190020004440003103280c51450381101113444140305102079004160400840a015040042e040707641d41403440c1e004036024000c0c3e5540d007005000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 530606789 1250 530605539 530605553
    0xc0d0b09100f0c1106040c0620010e0c0a090506011403070e062a0a0305041a04150305090d09030308010e0c1303050706030f0e0c0f040e0f010b03060601080702030406050304170301060c 81
    0x710398070b101c00616103440c055542c82c407d0b07000c80c080d4409000d07610201c1854038500320208070540381140001c0c84014100191140d0752400001c80c203101e0100410041141d651500c40c687c403981c416994200107543c0c044480410b0f50018046004006001c40c07040010f032144030060070000c0a89012162101e400200803004030604148603509410049242d4007080c0c0c40010f460130f86680c2004541d010210380428041d610640d800145030500c980c4101c000550994000f9206070802c0f010f5841c03450703c4c1407044500007031700d002c0100407038541d000500c9501d142c410341c80d920201608215180481d0b139545014002c0c6558401c070341030351200b82c05104441d458041e07116144a5070405000d101c1030300c40d03855203d5a5449115005144404c07034500d03035079256013181c1842040101600c03003d6424140c0c06000c1c1240d028800c3c02481041d01080083d4410b148640c030580e503076030184d810b0a042503800c4a1a9201034415900c03000034850004030070b90303003200950080c00720ba203401c41c10564a240102d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 530608039 1250 530606789 530606807
    0x1508030d111318140703140108012702120a05030703020f030304020a0e040f0b010f0330080403050f030a0615020f03030c0901030f050a09140c0d0b09100f0c 69
    0x80078a00d018002c0104580740c026020302624001d20302c0c010702d0100044050001d002007243d10000646050030f10502d0b0342c042e8410312980d03030f07031021200961381c80c0c908041c20380354101690f000b00d030300c0060300c03c0c00300b0b031950003c0480610080c004502545904602441e042c2002c005a0342c58100050100415404000c0b15407000307160400f9500314541500020245c1c0c00500c07462449600160002c1d0810850a031b00030303a00340d07010105920550311464403003c07a541c28041120117010942e060110ba000c03d500c45101c07441080b41441000c0714241044560100c00b45c003c038140802480a610410b8618001e0362042c489441c000601e1490000000d40c9400c00c580a8000d5420611840354003007404003c132613010104d1828103035a00c80c001c004038014a2195040ca1009152105200030105903412a001c03481c05242c420201500b0070b50034a4440340341401349a40240002c403202c0c001031060070500d0303015400307000342c0c0e04602c0754042020a0b14011101c2c0e1800940e610039058896800c40411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 530609289 1250 530608039 530608061
    0x60b03060a060e0609041e080d0b0108010b04031101020a120e150903070b0a09050303070f02012003090f060705030c070f170709050429010f1401080f09011508030d 72
    0x184591031500d0018070110a0207070045000300d060b0400681800702c45951f281030300d0344000f6600c41903041800e000704d1642200c44481e81c89802e250208840b036229412480c140c609a24109250038030b16542c44010381094580917066025070030190780402d031580050b8001e501242c64101c10003c100c000c004a130b407003428040384880d1081c04025020b8030009000c0c025a504101800c3d66001d0860303050340c0310401a40800c0d4140720008282c0c0c1007110790965a200d80307100383c90b0080001c1500e200b0080d010300581c1040e94a50091080c6956803a029041d40441400034021510308042030b2102c0341181d00c5464058015806610701f0000020b001a4890086c0780c48041c111060743c100b50150b484d04110b2180040c05900c5202203018840740c002b80c20700010304045e094001003d00210216031000920a40d162681503100c000f4030a0b20f84d242c244040701050799070500603582c4034000390000e071000d4003000d07a941d030701c000b840d0741c10b40c0c0400c030b031005414070b40011901c8240031100903086c1e522032440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 530610539 1250 530609289 530609291
    0x1207050f070209091c02071403030301060c06020304060212181b01090608060a051206010f1a07061d0115050906060406090b07051005070c060f0c0212090402040f03060b03060a 77
    0x20810009110505407491a54100c41c04080c0740c40b8084c905151610b1a60300700c11003001c10903400411034000410074112100d9480510042ca00300301010380341e000074410030300410110703946800080d160394001c41e8030074071981c001820282203918030b11201d00112560a001c0381c211030b8101401e0400c000e281c005e100c2c404461240070a4110000304003003100d125002c1401440008115030b0b0b5100b004070b0010b8a009050300000014021318650307a01c0d0203200c2c103500021140301c0030804140580c4030040d07203840c01c40d54918200341031b62040e006015507510026011b80c0e00c0d110b420709600a0103200003006200c0d104e452014180010009900701c003400552260404010070496950004d115104890b001d0b0501611803c8605200e030901c802e080880e40715601e40710400540320b40060f02c4d00300c102c2c0120410084401210003140850302c0c122480000f41c0e0203a0f1861044842c800000c06007032001070000360070a80d55046030004882141c00c200d0ba501c3e00c6080415243c1000c01030b46a0000a10300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 530611789 1250 530610539 530610547
    0x909061706100b09040b030a14030405180103030f110307050f16060c0203070306090302032514150f0c0403061134030c0804031208060a17120918010b120705 69
    0x89240e84900c120009607005d03e803a48145251075900b40000011280c210b04414090400700c894a07460382d100e406082d1103207000103e00b11801e04602c0c1c00d541030b030b58140c45212030406880c8003a50307005410b013000d4149200800401001807414000c01d405420350030002e044002d03a01e0000300202801d82c00903010086c020307540300050b81c0c0000d07d400881303401c00340006042c1e0050400300d04601c1303459452010b0840051244d5101d10141d81161410b0b03014414030b0032031500d05000161140c01000c03070f900c65070b500034010410b0f4281c0b0b00f011903040644525000c0c42c007a030b20f0f62a20250394020036080c0b00c0c10800f18103031060150f1501020305251030403100c8614003103c00d0310100041c60a07800541040980b01082040140050841c0d000c3c0d600b0241800c2c014034036440083c001801104c07e0ba0180d02400c5000a101003800c1401c42c2c000380c2c03000582a4207003809000c912035080b0410303c41d0300030b1038070700032580c4072211380c0c41c0a01030844002030039660300a9000c00e2400e10fa01030606410000100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 530613039 1250 530611789 530611799
    0x903020a080f070f0803010e011a0304020f060d0f1a04090807060902010504050a03050309040f29131d0c01090506030a15080d02030703020f060124090906170610 71
    0x458121480c561101d0801c0d1510620007101a143c0202000140451480c08850007400010400380d4103c1e10985200c10390390ba2109080407480003020301c018a03010b000e10115005152030780c42001840c00c080c03e45401c1074030014801c41524a2440744840f040e03620b81404210850920300091101ca00751000d20103c04a56a40c0360144a95000601604c1c1e175061803400310b80c4603400b00d40080000805030001d103070300c03030514075102e5110b40031803407159103413184c0f120b05841d06002c2c41300302140100c00e900254411781c11001c2c0da41d0383d105800d43e210b03108001410884002c0d108801c040816482c4c07191843c035a281800345003415441a0030305210903080d0421140d0344000c12281c0c006600e890200c3c0e403900c41d4468008a02141e0811103450241401c0240c2140e4008050b19220307000b5402c9400740e11141c40c04548035103080c0614040e8800b003c42140d0101901c0ca15038480000c4c41c80c050501c0c0340d54810600807510203801511410707107419001791404204001c1150407186c1040e03028401450705d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 530614289 1250 530613039 530613043
    0x60e0a03122705041a03150a020405040c0f08061e040207020312030406090327120201021009030503060a050d0c03020f06041d012c010312020c0a1715010608041e15060e060301090302 80
    0x47c191003400720200600050801d070403601640e0003000c0140003405000c00388107001d41a50010751016001405000001d2808e14202d903c246190308041e02e8105400741d2441444081d40c0401c20998140c45642c1008803100034140045210b14010000059941000c0c900100f1004500740402016403407490704081003003410001104071191100145030036019440103030b0134000c190052118043c98400150b042c19000303001948200070484000040a803038000b0050350707040e607010281c03030020343c101c0500c01414101e0048405290040c0000c2c1000e6481da4072800062080e04041a540001001000621514024107003100d002d1304051610750f844a83c513034884101480050280200d98840d040b18500038030400ea0600000703060800c00300d460340b0301e20900e2960151000401e04c509851190466900c5044505803010b580e20200203443d140c460105a50410000161513403441c8101e80c0000e20780302500b00c85444d401070100e1400d151030402ca40419006001a0107a410644c05800080e40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 530615539 1250 530614289 530614303
    0x308070311150109090311010e1506060a05120705070503130e1027020d2d0506060d0e0102040e040506070e01260408040f03050f0601060e0a03122705041a03 69
    0x4c61100025082c0d40c07400d0403036100a40c420600415481c1c24141c28800101140c5007003192107035000000280c03100c105014062050f5034000000560030700400d024038400320507454001166140c5a410503003d078a901d4150303405101d8091300c1c030300810000c101160b40c01d00c0305135100101c00159000f51380760010005c0c5040300140700b41c14540010203410848803440d4165030f0001c0149a040101101181081c0c00e001070000040080001c481c08000762146c0b0790103001d02c6030b03401518483c1410302104c84078001e8144100c17000c0c010f54080c000401c241841c40580791003140900001c00c1507081900002c1d04503400c110045040262000c008900c0040c0e81c051003002081c80e4240052584d42e41c18014864000c58114040078128034038008140407001841481c01c45059041e02c110380d0342c450040e102248030020054025000703120820210301e00040841c820313086420035105900403160f10075254208040400640c404805080c00300d410281f14007403039403902080c40450101c010380000d644540d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 530616789 1250 530615539 530615549
    0x13020901290a020f0601080a08090603130f030906180503030306120c0414010807170705010c050307060921030207020612100b040605071a04030e0f1903080703111501 73
    0x10450201d00c0703400000080e59442001600c06641d120b2814000003510703600c412142072050f228883c008103401402050003147d80c0d51205d00240b420050406010a03504000c010008042c1e07800380c0d41c000301d050404424007003882652050304130340c05e10780c014010a00c0c80381d4a442d1092107100c203214984001080300d411079401c544808214104400e03161404009028040c1c202e4100101001c065800c1c141660603588020251040182c55240e8590803401e000103400b801d1740120030800955004140210007a8000c4054030300e09801e60702d030030741624020801103880c40000006d500058460480202101c401c500c0c080d45010358940000342c481c014501801d07034045000e004a0088070f2404408401080000341240e12036540342d2004d030494204600940f0740c00c0c800016111880303011240e60f48550790540b100d1400003581421300030090200d2704c2ca1900f02081c00380624178681d5410100005510031009590b950f006441c00a00e0980c81040321500756010711122a280c01110181c18117660b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 530618039 1250 530616789 530616809
    0xc1c0f11071103010c021902010806131d0c0402041206111902030d060510080f0405100908090406050306040209010909020303090d080a0206060108161b0c0b0403050613020901 77
    0x40020800105698044005001000290740c0c081101c0d1036650380500c03908800070007281c1030341441640c41c4c0140300250b88042d0400281107005600a0440503000301c070290000707042d032403503840c11400c4400c0100070200c0c0c845100490200f04000f04082050540c00392015401d09107444d030780d189214010000140410384900e80200ca803050881510700d80700b0a44082e51315480039113400307900d0f548100c02d4004c1d071509140b03022580e42480d030740e000003c04040d902e402c0035070b480380070050510702d0141044580303000d04156104100f400e030082d004034070b0040c24441d90b42c0902008000490303042d079002c5402a04858108005070b5110100d1354112070700c00c034000c102c15500340300280c01d52050861465010001c5000ca03000c0c00456006000c18001c3c5408440040d11000c005540c03c403801c40f9200c0c0d0922000d540544200d1145100640da030710002040d800d040219aa00c0b05141c02c203421003109540041810001e22004016030303908801d1112400c400c0e211035401140316103c050107486050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 530619289 1250 530618039 530618051
    0x2030a170c090a030803010f0504050c0d05070201060e1005041a01020c121011040311090f060f1929030108030403330c17090709150b1309050c1c 64
    0x82844002c554040d64010000c00469881e8642008250028001c00c80307010107100b4041340c07d050a12655005072241e0301c2150508581080301c0c80907110042000085548503030001461006028040780500000039607000c10506000c00e0004a03142111240c40785150420352030040c0e600890003150500003950700b00103842080c1c1c4018a0a400c1c0c001c8241c400c2d20349580c0e0301000b040000500301382e038881c0607140115a004020081165010344044540300c20035004502d50b440c20101d180121207000c1d040069110740517107480080041e5901412440e10b101d86502d017091300c8040e01c0700809104020885c255410f12800540d64051408003d001c1083e80d1041203440f2007900c1d8907080c00540d4281240401600401500606000d01102002c40c01c0c181082c5c011600ca2a14035109500500080c541c00d07140c01c0c040b0780604019607020031508500c3c0e201207284503103280180100e01c140101035590a00c1c00076940200c0e000103000c1280803406020f0040800000d0ba00b0042030b550f02840443c0c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 530620539 1250 530619289 530619301
    0x3030f320601051309020418150b0903010921020601080a0b0601050f0c0607030c0206070201180809041b08061f020604060b030c0a060e0a0b04030c0e040609020409031e02030a17 78
    0x145102e421300f00940c003001184005420304080c1c0041003600c0c1000408014070407943c682c03105a0b01c041111185542001406100034924000074104076a402000400d0050321510b13080d401d40e8401100e0105002e01c1044a071107070390100f12080c01001c09030010040030304a034440c1d02103204003034200f50411200003228036400400710b003500c0030005c480f82130b1060740c20541d40c054010020a25001c01601403e000210064018800c0d800030201c60720702c04d011040182d0340c01000764462140c180d4410344c0d504c040358094804050f090803558894851071134904007001000078101c200004014514071804101c40c50641c0070601c0f58005174082d4011603403144400000c1d0401042548594000d0342d801400100d1541c0803001c41042d4074140d41c000300711600c3d8009040303148100e0002030010b85d0701e150200030802d40042410340c81800381d04001841402d80c0d000030b0540f04206e5042e000a5904100da018418041c3d02c005108001400210b00e41130403c00e0141110309046a180c1c1340d5010b490000d00703 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 530621789 1250 530620539 530620547
    0x402030703122c03030a11120703120501080c0d0f05071e0611060915041b030c030b060316230303030c030f0a0902130f020c0a03030f320601 62
    0x34542c0000042440d4500703000082100e40304031401656101480c0c10100000c801d4100c444814034040c000c0c520317061030500281c03181503e000c40342003103106a00101c1c246c500d9210140c001a44240e40b4100d003e07285902c003405460068101d40c1c0660044001000d6030740d6401c10303072046158002a540c103d01800d08045040003000e0b80100ba0941617202c101102500c3c2202200581c0c0c00c0c0c3d100c04094020104d440c550300c00c811a56030350143e106407090110141040b0303102d640b040c4101103a40b09249440f50000d81e0781001d80c421501909031003428820000e0315030711503030711104c00d50040603019103480209102c55990703c035150b400f03100e040d46001c1c03c140a00c080c03100004003404680d13803410001000d2629520803034050000003200f00c003080c155101c030702903a4a0b09400810407600e07000ca000d0142d008002003007a0b000119401c2081c140406001d01079a810140292000995520a81c408505031501101e5451091044001c40c07a040d103800c0e0303200700c00200007801104031030b510440161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 530623039 1250 530621789 530621803
    0xc09060d120e010306091116080d020a020c04060503061b0d180b0402030c090702030a03020a0909150e0c09060313020d0213061430010221040c081f05040203 69
    0x1a00007100d200c620032090b034218502d501c00100c00e9030b003000101e030384880030b00440d4101c0c4035003008803008002c042c403299000c0880394480c501500e0464580990704210b203049032302481d03500e0096004224035540078a410b120b128014038094020f0072152610070130200c0c0200e040c8811903a2800d020070301010401d943d50000355080300381400300c60807004d2814000e686e414116800c9100c1e1264480d01d01d1242852032116025242c950001c1d42003800c403078429000307034000154503010040c01c4440064280300501451700642442d0803401c881d2403c1c00100c00002c2c40081052403000410000745803562640f008803940302440c0c0040c1c51078003186100086d440311f42c2d80c030080e61002003e0701c10020b00c45194010000c54502c940c24228041e000402d0101110000003801c440d10300d04104808090002400201185804400180340c02815040e40e240200c241020318060030341d4004000801044036140c0018081d880001c0c025484514024510a004080080c1500b03440c0d40200e0110b4408205a07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 530624289 1250 530623039 530623043
    0xb09040906060f030c0312030204031a13021309030f08010b040315060902040f331b0c080102090306010812070f06020c060c1c0903090501111c051e0306030c09060d 72
    0x8840029a24100341c044501d17907000039101c000e4200b42209059010740300b11400c80e0752041014943c9008042c0c400501c040050400c09080072014507480103a80d882001c0c3e03c086800c82000072240a90300f401000564600c00b4a428488101c1c01805217101e100146e400304ca6006401c0c40f00d6050440380c90012b040f035680304800c91400800d0103e15503240310741c07100c140c0c0d990000d00500c0301309000c010300c004241c1e401c24136841c50340d103e40105080d00c5465403200c03420101c90341c1098448107965462a06080b90b104115503540860f801010f407070280031550041c0a600020002408007080c441058440c2050080040c030041148900f084980c1c2c040d1008000d180007524910304d8000c041c141e09a00c000300300351564444c40e50710780008030640300d01b6030f1a68159842600480c1001c0065541000440300803c02d032044121604626610910906101005584a0751544511426001c42601100400300207410900c01c01c070040c0c070002402d0105a00481c0d803410141c54060200d030700c6d1031040b840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 530625539 1250 530624289 530624309
    0x106021905030d1119020601030b160507050a080d0b010e0310020310030813140415090e0309040207110306090a080a030f0b060d1424100509030a03020709050a060b0904090606 77
    0x5400d45002612016152004014005004403184441c5c1261603407070034040144820040320200300080360b40300c103484459042c0c2c00c00d41d02e4004192621850041b58090881c0d104a00084c41c1d64800510b01803180b01a8003030070301824854560000944446402d81c07120f11a60b408800500c290501c140510b00668002d420160348112013041c04450444500400221480d58004450103003018400d00c2121880c0502d80304075141480e4200707006d4511410178001174403082c04460300e40e54581c40140055407296041c520f8aa14070b01c141030805000070301c02c0c90141c008c940400085010101104e094420600d0009050070201c000803008150302030825030000c2001c15860034052466021540c00081c07a026032036a07945d814030615100c60740e10030041c220300b4082c0307014441f07050038030814a00341c016060184c01c1c02d528001081c030300448418250b005a00c40c030000c004003070181c410550006d40341c000610000d42040f4202000303114241d10030b030243e82d95004d014148491603001602070100424 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 530626789 1250 530625539 530625551
    0x1e06030f1e0c170d0804050c102309041b021b13060e060316080c040f020c06070203340f050f01050903091914012303070804030807080106021905030d 66
    0x110f074220f0000d140c442400740715042070f010105004c1c9045d54401c80d072103401004150f9101c02404003c6014110a00038003000f09214400f001805901c0c2107450804034000707454282c1c19040205543e000030102c0303101c4a03800845003c03a0341c08030310209100c0070301400316134106000b00420070300540d600842c100d1519001c3c01041440107002c007a4000c02c411001caa810640641510b10500c100c0d05c18080c2507400541000f100342040c2d00b0a000e03a18802c0801800c14100240840c20701c181200c1c40f00050b0000100c182034070549102250089202502c4070103800c8034146172158201404402629040102d90000100002006002800111030000b40301d00c0c07d065849555a070400c2801074801c8030020346042c48051610382440803a94440410f1040001040041d590101c01303890116440c0b04200c50000c2903e581802140108065564072a0510740383c10001e005c1e0700003400101c1042140c100400007281d002a40100c050340c525044401507031545401c1c0e145101d048148000541044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 530628039 1250 530626789 530626799
    0x15070605041101020609150a0c02210702010906140702060928050f0603040c06080402031c0801060e040207020a05090c070b040b07020f1f1a090a1e06030f1e0c 70
    0x6254110b00c8080c0c0803103400352940b00b42c130364480c600c00d041807a04a510b1000a050031005421402581131640180c7d02924a5540ca050f9519001008101000c0c400620301c0c00b1542d00107035a0009241c00c3c40c10840640c83d00e295140144071b1480c011b40f082401083c100450b50714211811541201180c20804203c841c0c1040d1400340824407403d48110180c00300c0941d141003060071640700756070003062184c0607401c01c14240c441c014003130b0090b0b0300340c483c1850304091000d600007406175011168480c0d004540c50454000d00518101c851a4003c50050004000589800c2841025150304075100d203e10313590340c10807000034011008003134098a00d10050009008400340880d001c3c8919600342c0700d10344c007100d090a903140582e0300c4a0713000c82c0b50003440d1804a101544140040706515022207064070000000655009041d01d580303c009a5a8450000d41e0801c4035483c10f52041c2401d0a02880380345450385000d200c0d4091020700314260341082c0100810080052081c4a0750110241e070300341d07440d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 530629289 1250 530628039 530628053
    0x307030c1202012f010513020a09050c16151515081807091d0d0206011208041706180127060908030403120e010501030f02130b12030d150e061507060504 67
    0x3644c02c901170b5180601017100100b102d401911216005000620458a0180342c0c07002002b008001e141140020311081c039a000174050340d18240c078011803200340341219011800d000c03a210441621f0303d254980104000002004140c03800c03280c25030800800c203a17540d842840660600c01d0200426019500000c2805c040a034064204844600601c441110710350391b40594804070200042c02591201d0010890701542d0707e919121284143d090500781561030801d040162100081104185c101a0800001d4240300d129120301c0354008000b0f00491500c48801200086d19084881403106000d40305c1041c00f18581260321a41d511503800e1760b0f40d192a040040861002c401629452400e2418020402c0c0d414010700381aa600305101c01a101500d50800180038004101512415164440800540c0c0c81848504500d00742002455892030214000b1341200c107201d580c022149082e0800f402249e00703150230941c0c0701c103060707417240401074152700c80240c24050854018903807414481040108104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 530630539 1250 530629289 530629367
    0x403210e1b0609031c0c020307090618151e030b040515011403100c030b041d0d031a01180b30060d02010302032a0403110307030c120201 60
    0x801855001c2aa841c1c50420805100b031005031645a44444003100b45121100d00c01001c0148506000302001010703804641041c2c41540040e6810f03aa51004204403944010031a0049070a5141005032121407a84540d203a407850003038488400c00076040584094900c0d455074095070304202028151b107494070300f0303550f500740781301e8800058a010b17000090340f2520891880701030036000700601081e140040700e00e001440220318580800d61580c40e03c0100392079a100e0701d560b2602d11140c004400040c03140c0d50b440c2100d840919000c16140210141026894540d040c540b04c200f40b07004900d82103801d06e54031108240d03801803215000c2c0001c3e450810310141c6c21252101024000013404260002480c1c10032a104840c0d80c0d41204a036201d540042d07100354010340d0701204085246084c80106002c40139084100e000c25004400000b5040c014846044101d030b0010b5001c40c0100724803411a500c500c00f41c6480d1080340300d58100302d0404001c580c00b03541c002d4a25420b00780501e4049030241e5640000c003070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 530631789 1250 530630539 530630563
    0xe0114130902100807050d0e07080705012307150f060303030b0a1202120109140318090103050d030510120b040b06030604050d0c06020d0e010c09080705180604061e080d170403210e 79
    0x110711140001c0f6375020318414a02e88041c4c582c102916000317240405030650100b001240e1080b040c1c4609040500c46100c0c183d0106503482001840504501e030140c00c60312595140d43c80341818820401900f81c0c1c03088800d0f185507041d62030900d505008890103003d049603440051000c0724003002d00100400010107028004881000c4840100ba9102403013802102800050082e0b00649103004000d030080d00f010343c0080d4044121380186a80cbd180010070440144800c03103c0c03c0d110702c18001071182c0380d165030740c1002c82180540447c0c10181d40c0d1958404040d9004402e20401e03042e00d038107116035603040d6640903621038000e11486000c40441070080034000c001d0004910609804154180006480d4050b510098104039400350101c075506c080100081c812a4010b0f21400d000c1524413115500407451590203641220042c140b006403410071944400000420103507803003108a19440104045d042900340c2010b042482d10242004501c0b003200c142240c00505050300d00e408283c00040c00001c0513 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 530633039 1250 530631789 530631793
    0x10020c032814030705191206060309060609180f0327031a1909170a1808010209060a03180221070821130e0114130902100807050d0e0708 60
    0x110030000c0c42e10a0009072500c2c0d0010b41c00340248620721115000701e0b00445000e0620300c5040d007440e06207109a03001c90704140006515806020100311942c0544000b80510034400d0051524503a00d603101c488103035001034415500f0409007030900d40111707814403408990b111218840e1b880c0500008100c941c521040741c221280d0360070300040030342071031266000315079207141c03c03c0751818121240090039001c0e80656455511a502c1c0070070081120007080d150580d0b80301d4218078004c810100c419a8085d5101801690041094026036038031481194840c0d40142400502100d0f40700e01c4070705001c02000d001b900315950a91903513014103410303480d400c3d03c5011002c483d0307000d46403440c0d60b0300d96113043c11180310400720102c41040030800380081e010401e0030010070004503907140759842c0d80a00030381c4101d105401600110341c01c3d0a014190890010a14805000c000c0705a40401e902d803c00c0704075a41003149540115003401e00c5001180d500c0840603d003404903a08040302c03945c4030041c41c07050341300034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 530634289 1250 530633039 530633057
    0x130821060306100b0309070b03010807210302061306020c030a03050a0e1b09041e080903010c08041a0c0f07151a0a09020c01020d061706010e060310020c0328 69
    0x41d01e00090101d1003907601c841e07800016483c00e000c528003604007611840305070152030004102c41d21001c0c0514001c0000900505026145c56000043c4d80c62030340701103900035800b803055004250001000d80c4c1050b002600391100303514504000009004000c60000540400521040b04540c150049800b03104e03070601c104481485801d0856861000c840400031000d4050003d00e020f02e0300301c0b6020351090140c0c0c007807000100c203039130558109500040c2c12200110089051216420b091103a0200202070f81070802c603e05107030301d071242e14000565803088070107044000110001c01209c203503403248518045881e1209041e1410391400e03510480d000c03035001d24110f8100080360701c603980c02014460141189244500385030081c1d01030750005040ea06599003c2121079a00301d007a20a180080100d030001d51442608250541e04140c03060b8499400c24400400740202581c0103e08a50340d100110710040c0d80e950620f15482c110b01030341081d922458440610840c40c0c0c003101001a030b40090541d41c0e0b841c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 530635539 1250 530634289 530634301
    0xc0b060a081b04020c0109030810080c010c081602131a090c030705030a0b0310050108010b01140d0e072612030403050a1b0b070e0a060207120b130821 66
    0x480c15040c86051120341c4441501d84003604919400c8680000c0030f0070140c0f4101c20a1380c1d80d8213485030003804900003460641000f42c68500800f41c03001404462028244003101c1400007000550403820240468038005095142980c02141d11f0f040541d01408c1c0040250003c0c881e400200508001c1460003201800100640d151481c8401e105411403041181581c4440c1c40441e05908011702043c040e0350354110040c80e56404100304010400b14000101b243d41c14818401d00b91007184901e00c2c140300e0019580c3e0805a07001042d54607010704801e00103010313021408018a801156846102480201c4056013030282c81400765210900c03441017154a010740200c0700c14038a102c00c4030701400051051002c40300c0e6034416840600300e000030340e0034200341c10420f40703c0d2041c4610544039880400d01191040c48030f4108103001000429003070024211051800f43c12459155030924010140b6071201d00040b05089600c160006194102400ca0b46501d11210300d00548980300140040d01082e440019031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 530636789 1250 530635539 530635549
    0x201060b070807060e100204080115050f01020604170d0609020c010c09030308130c030602161202030c030f0f0412030509130203010b162307051003020309031806090a060c0b06 77
    0x1ca542e4031820851400d035203600c9440c02441c4104050700366004059003120840a180003500140c0440000055680140c6083c00500b11013940443d007e082d1402044c4480c1c0e80119569074800d07003003601d1a070118007042c0d50303402c544250740c040b00e962440c00d030300407030320b00c0c4691b010703010b84d8680100801581010900a41e40356106c1c1c8030042c00240f01000051805d42e429040d441501c5c03290319007a14058890340c0d030030140e07000100600040da200900b10002c0c8020700300840040c50743d42c0003840c5403109814809881c0c0c40fa45000c01220000010382541c50780000c1d0444000f00421040002032941138a001407156224500d070360b1042101a07280c1020301051701c01c40303040f941040c68141c508400c1d0344800401c100c03a00415605001c1c01940000c00c0c2c41d0b400904100200750001a02c50310b030500041015103030f0f820f0310903000c062044c0204044108004111100515440c40040c420b50300400040c20b14890145801d401216500d0005a0681c00a403115070241c0301710144a0180c0c3c814003400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 530638039 1250 530636789 530636797
    0x1216031406150307031e08180a0504061503020c15040c09060905062b080c0c01091203020a2018070f02010e0613021c0305031f030b010b031306050114010201060b 71
    0x6685504140c000300300050f02504403055101144420f1b103000255902c802078941c100e4840240c40010341d2400c00124605581000b000d0003040b0340420015041160268003500b0001d2094180751340000c100030984002c2001441074104103010312030600d4246441600304400344a14180c00307081c1540130070244018000d8a02c03800000d0409240481060107480c03d418500d0243c910030b0601da440c1d2404201c10030002c003481c03020701000b4091010072100040a442269101009a409072888840080d5000c05c40204198000c1c2d0300114030070b000d413114900d0441540b00241d200e180707541c41684074281c18101e90700c0307001d440d281c0e0b4000c04031152041e82a980c010b400e0b1203c6411034400155441094103035031441d140040c040d6201c3d106400c20101c44034101c0c00081d00401c1c8080100b02105084015502c04c5172700b1180d00c043d02c3ca01d50740e00e1301240d03581030042c055102008400500c91005542401c14a03036004a824440b5580d203039040c600c213181c01300c049030055003041700129184004504035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 530639289 1250 530638039 530638081
    0xa03081806040b0a020903060a020c0f010510030b0702032506060602060613050c1b01020301050405060d08040303232722020901020a0506070201050717060603061216031406 76
    0x40c0485903070390f541d11124410024074250f4000d500f80840b400c503842c10410076200d406184401603940411401c1c0070b00e0600113020b020202c1c0c0c1031000f000a280800015502101d07031010f9450410740303621106a06500510020450a00803100105000447e0b44600440302d406040f0410800b83c0700c10f0200c0c1c982d442121100d810100c41404204060030640c0010340c0142e03080709050034030345140d40b1502c1803041076018807400c1e0740100c014481c3d03150034400c0d9600010200c03004030003000f0950743c1d003545004600c07014041c0141e136204c1d5101c2c280b5940710000d81311a20407195580e440034140554120788680300d10420207090303580080d9181051040b03084c900c0c007804a00440028101d10b0a0040d510290a050440c0900e0001000003101000018003030f80c50f940012861b86001c000007801c000e102e60701c84510b50310340c405200b040e485410441c0d40008050301c5142d0320752596620700e440c1203c070b9134500a000c08642e200000740040300c9108280c6255860a6845640341d00401c035418442c04a98 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 530640539 1250 530639289 530639293
    0xa09110d0b070c0c120309090606020102091003150b0403050d090510120b0307050901060807080c090f090a0603021009140904020319050703060507030f0b0111100f0e0304080a030818 80
    0x1c42c4045000346085101c4610440c50748a1035903c0b0b0411005c0072254480844c045802031209010030406402803401800c032a200840c02d2070010b400243c8050340c581422070a159858950b107490340405402c4d603029000c031700740c0169150b69911340340d907a521880200c0000102540310214491400207d02d0a040c011036840a00d082541c0c03041e03000600b100302000f80d061088413400104d9842c2e03800468002d08040d11003401504c7d29680c0540f414100078080c1e51126000c0242800075940c1c1c01c036036000304c5800e0301c0f000da25a40d101c0c0b5500c02460241c0000c0e40c007480d0540034030204c65000e10018280c03080000903110b001280d03000e000381c03100c0503503000354075170000d580c00c8040110000e46070030802c1c01075048840c5107541e600c0320012103000780e520200194543e440c03000c1c404000e02a054082c4020318003000d8080801c00703015100c41890318046031042c0c039400c0154040d004c5d50410520000342e001603980d035680d954081991118060007c90204d0440000201c64841c2815540040131079000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 530641789 1250 530640539 530640541
    0x50910020c0604090f0b13090c150206010306020307120e16050109050612071b0c0e0606030708150102070f0f06090f06080106050304030917060406060803040b091e03060a09110d0b 79
    0x800740842054491781c140d0b0f107100582c030680e19103000b070884440820b03001032000020708002c2c001d40f642d40c1010808440422607101000e60004603641125000300c40180c40b83c503104821110103000380800a5050b0408082c00290040850410300794900c0c0b11040342e00d9030b07480c001035a1109040c402c00780d20104c14042d025203201c000d0403103036101d0035601d090a4030300702c80c078000e002400010310151116001400103000405c2141900d0f40c10903003c4038040d0031880c1c050b40040100c04024034500f0b0000a20b000329920340d000300542c4d4040e04a61200000c0d15481d840c20000d0341d04540300b1040022610500000c0b50611044d0308419900c19680703811450b803d00307105594960002d8800c4007049910040003426110300d00000c01012240c0000e8800790510f41407007000c0d110203400100858100b003004200041156003110940401030f201c0040100e100900304072803110303a010043e00343c09000300704501c040c00ba5125030010b81c451400081c0b4140170074207001890102a0f070061220318100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 530643039 1250 530641789 530641799
    0x26071106280e0705120601080706031a3115090603030f0f09090c020307020414100620070623030606090913020a0b1b0d02030f1804050106050910020c0604 68
    0x340000d02100300c00022241103a136102e01040141001400840868120600604c0003031000c0c44000014010b910b81801400240c0e0001c02102255040b0b41d44070301c4401d18000420440943c00881484060030049401010311604001501c1400225513040e03050a40104200c0424031481040d203415540300c00600603442011b03114400d00c49124410b02684282c0010300ea002c600910803842e100b9809181c807207550344184004d0f22030f841b04243c48a500d4a0401140788071304d20000d822103090385410a01c2c1d000209014040c00b10300f10548030b09000d004004909207403c21440e01d40824464490a04000358940d060b84030300080da1401d6002c2010003591605213040d41c100d64011032003591042590005600040802180e6808210b91000104100c448011460108006418000c014004d001800d03540252a4801e00091322030700e6034041182c085540c1c402160641c030080180040145503101c02c3c0c044c2190300515600741c0310341600c6010381e860724408100301d1103d85010b024207080600f44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 530644289 1250 530643039 530643041
    0x30f12071b030c090c0e0a032f0904440702120609161205060a1d0d1806110c010f0e092707152607110628 47
    0x4862010741241c0c44000480441c8204003030301d0003040103c03400035640244081c090302c03140800440512481c0b04035810404a80008542c03612940301d0b07450300700448000704035040344400c04550075811000c00400c00c820010409112055170510000800d9503441c0f00440031884c91034842490000720102c02d00400140c10480a8000c0c0d07480100702c403405c2013407044460720341035080718101495484010101003014030810114003800400e50318070070f80350440d180c80b641c03840040c00e6555556035640307a44011400c0d900b910030a000132541550002034221030000c003003208003400340d285001108400070b41d00703018004680c140c0302006c024190a1400e100103440480810b41068240062030340e040c02c00c1e9951082c124420314200404000032a01407803560011810901011241e81c49402c06002500c40d1f01c03040d401c094000c0c908030314001b509021051104180000c600c110034844000d0110b01600400301d51017443e0300101710f8105580d1031507250f00d025060400300c04203c1c80115810300c140c0e11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 530645539 1250 530644289 530644313
    0x13030b130f0f02120f071406090d0813030c1d061f0809010f0c030203091b13020306030a08072411040501050c0f070602070801061a04150903080d0902030f1207 70
    0x410400c0160044d000203820001c030f0400a24030ba4000c0e92040c0100c0149a0713078020b5907030064801c0c3c0e040290885c0410302d49046100042c00750200480c9411700d466812480802856100003405034855940000451000700403040703e50428101000490034105113032040b40180101e458015401251041501c60260280c01c402d00741d5210220090221a14011005142ca0540c3c00680c0d91814901141c18107640c482c10740c1940701510380401030ba0b900c10500004200d43c803080140c1e203440310030000e8500448c062004104c9000031500c4400e01c031783c1800000c0d10322402000c14042080b1501110101ca5007524182c950000900050151703510a202808040325268200da00c550121b01095140c140103611260050b44003020500c0141e600b0b0207600010f10f605001e9900014503454544080e00540c00b821680180710b400026140344119224001035810840c65961910030381440c40c050131203808164060b208021071951010703000500705a22010100683d800c000c0155100c43e06008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 530646789 1250 530645539 530645543
    0x30a02070518071110061509050402120c0c011407170604050402030319020c0a120515070e0f010e0d21110a03030c1404090207031202130302060a1413030b130f0f 71
    0x11411190b489170104511408010b009043c0942c40d40500c03051009000409a0300720364040e2f4014081c0c008440b070200b05140d002250034a4968480d203540001c5401840d0f04078003a10072074241003d00600704e421803007143c40e0b42220000001350785e507458140001d50b401514000d416034810800c0c14005c0d40c8429940c0c2c7c0400d45031042e20001c0701c034503001600c0078109401031012200e0340f24220003002010011001c0d403c0e46a20301c01d00f186403894015010a03888048103008403e20344d0131008981c4240201c420a6400402402ca450034a051885049940e1420903109074000f016250b40e0a010310041150300010f84010702c10040c0a650490240a001c812001403003c8585850301811540d4042d00103030030086070044e29090799080c018203041c0400d03109403049104200150441120344180002d698042d02c1896a030100c040b02151140420500803145071b0380821b0300300e41c001c0d581e0300d2001101c2c000c2250000c26143d98031360003001d500d0907100030814401c150300080000d02c98480c0401c068 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 530648039 1250 530646789 530646793
    0x1090c06080a09020a0e090c010206040b0402060a03020f0a0309050c0103060308040512030403020901080c010e0f030a0b04030e062b0b0d060f0605060a0305070207080f0703031d030f030a020705180711 88
    0x1030f40c558045400c0c40056040690750038402c0e410009004800c002259a81900340b00800302800e16440328104207074003400c0039003c1c0c0000510254100d0007174048886041900020540c5d9038080000180101040c0b00d00300c8440c004c1c00c40003445903101e4019103050301d80141003507242c60301d02410800d8280080035884442e00040c00f000015030b0394451064000c09410010389441180040018400c840c44030210303100308c0f81000903a000d030324002503c400c6140e11080d24084e548450900b071300e420100014443d0701140024401c0c1603c4610200b0401e85103102c140501c11205480a01c0305031450516103a4100300540814030102d445500903043e070111006002812039140c00105c0d1103940207117020400720743c0380c0302800031071541001000010400b0002502c0481006800e9545030f00103032001030200300350344005c036149500703088420305040070081c12640e40f1042d50040580701d8020b44105809806240d5000030141400c2c0c4100d07001c010074007411202c541c2c814909841e10301d1103c0d81d0100354 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 530649289 1250 530648039 530648051
    0x60b0d050a0f02040618050d0b0105040504030921060f020301060203070f1109040305040816060e040209031903030c080f1b16021509100e030307171606140901090c06080a 75
    0x1a0140300620103031080c2d035640303448810603c040e04c43c001b500303a0155000340350441504011a02e103140c01c605544080303030040b800d6261401d0450b0030301c08642004414001c0c03107d41500954a44841100309445804107202d599080d45c03c00e400c0303000034895000035030002c00200002485800344454071a00c51112101c0c501d01610200f445a801200c0460200b880040c0c14001c1d0f200c04c04c844802e040010344030b01c0d0003030304092005101840444200340100c1d0046404400c9640520080042c544050700c00d80f28807805040060107407100f40481c40200d0080400b1805041c1c00300c120500c0382c208001a0019007040254040342a80848400050030003007400320001a030340e806640346480040041641c482820714100074404404a4641c018051640050101a1004003d03280520f0f0000301500c0030414038002c40c1c05a2007514402e0761131102e615600d800304207181c1c0c440c0198584d200907080107966401391043c03c1f9013034017501030402c1110310400c10120303101c0c0c1d4240f90301000071074000c144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 530650539 1250 530649289 530649311
    0x90a080703120c0f02040f0c0e181b19050306040e01090f03052104050109120206100e1806090f061303090e0903040e070507050c270601020c10051215090c07061805060403020709060b0d050a 83
    0x5030220380033400c2c0007d0400014060249030900903003240f0b0708980c0007085482155614102c080c240c2718001400e100020480d441900205d18500645811210721400545400e1038624028941000c040b81d4440c102024034020f14400100343c3c0c45030780c450960700e03207080c01e1100c0c420300000002c0525540c0044504070001c030700001c0c040c032402451220020461401005162400c00c1c60040403a01c440400060220119501c045202d00322004043c0700c90090304c03070340480c0d0f00310312442d00a0103031103a40781c0500101d01e600c5401001c44501400545051000c03500800c0484144000940100f01c407405003180d0b4150075040098100e58140101c0310100d450764081111600ca100d04c0f036021032000b080f045840180d07000c0d003ea0004038031051107010007014000500c1c1d82000780808001c4640403400d601001091380c0405400c0e40d0202e1012506990b9203003540e51420225012401802842400130360300746c15004180a03201c1044c032042c1490103110300c5400808004144002d04c50b1201c4140903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 530651789 1250 530650539 530650567
    0x170a0c030503040f210f020c030a080c011425051c0c031407020d1707050a11011103100512011b030c0c0c0b090a080703120c0f02040f0c0e181b 63
    0x102c82e01c40482e0f405c40141c2e049024065218822694096402000032800507603404144410429400320407140c03900030600360b19004210a444182406d1a08011700501546050000a00590025204083c491810000c58007802064000300074801491442c021310701c2d090f08400c2e60800d1515000440c0c02c400100c407441c10310705561a00140c1c20403034a0103030300c541c800007801d621040c001c0c61420741d0a142d0f01c014124450b02815404100440b0002c1c40c40d281c2c00c0d00700c0702811100d188290344a0604015104000e8010310481d8481d900040f2131200300302d0180981c0c422404000340584503000e540c14182c0190030a95107807070400c4104049100041c4808141c0c2d0301510a4400c071a80b0391444109201c00305c800c0350000c100980c0124400c10004102c12141148100c0c540391180c100411482d01040b0382d02120300c000c1d48207080c600794412000342d40d80802042c038010307581e0355119512002404428205414001e07600c0743c481002400384081c80d6000c0b404048900e00da107103400c001400d028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 530653039 1250 530651789 530651813
    0x9030109140705040b0612220627030801031202101508060c07080a051e070b160306140609060c07080a02010206060a06051903020d0f09170a0c030503040f 68
    0x2079080c4004004044040300400144001c1e140903101000f610f10380f01c0c0040e10380e0088151900e40c0581540004494202800620300c00c11200c000c0d50040001c1480c0c0714014184ca41403499680c960300c10308132103241101d09003ca40c5501602e41000360303400c507110100b000c1c0306004000150303c614804043c058095101e900c902018920a5040740c40c2080c0020303040100c0034280064062040c046000461600c104036a8941054140995580c1c1c034058a50100c0ea1070080d1610400404100b4105100801810300d00c070704c5481d42c00b0014855070990a41c103c461600a9150504c3c46e242988200c0c140700f0000d00e1000780082040b8141100220302c103241c002941c0011a0a800c00c0070194119601004034a4000001725440700040c0e00700f0f04000c000e030003800c000301441d60800d0b40e50742d000c0b8002e034106c4040041e801c00074441c92091a80e284003070151050100e4035010712042d0403d40381541030950310038801540d120303e1000b89503182125a6000900103540983d518500d640008501078110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 530654289 1250 530653039 530653043
    0x171524040b190e0405060c030106270302060a11010605122e0203180f010b100c1a0a0b03071d060910080102040e090c0a0602190606090e01240501080601030b0609030109 74
    0x142c0350f9484c00d4034101e0b062600291200d03145038428001801159006183d045010418440051294003481c0040080740810742c0065003004000681861042c0e202400d0500e1300062070080c00f04694800c02e0000e2540306042e10205904081c03440000700b0000c5d1882c180e031601010b070142d90402c41c00c2001049034010795072044120003011715109104c0090003485450354012000f001025a0b0901003001c410b070380078850701000b1080c1d081104104248a100c500d441200007001e03002e2620078401001410444c107418420321a240000400540724500780341c3e507046425105601c2e4445c0414014180d20141c0140400101c4000100d20b0782c00901c0500300800d4128404102801c00c038860f141403c000781241402107040c0c10f014826180c0008400c860f40300c101d0020310840707c07242170481c02401150443d0081d00e00f00940701b075055005421258100110341130241e840151181502200c150300d00c50349010610003000075025601070341c04030000b11005042d5914186078000020b0031901d0326201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 530655539 1250 530654289 530654309
    0x90204120c0e0705040905130f0303020301051207050d120c0f0b07080a0203060a030b06060c150402210606220e0a06050c0a080c090406171524040b19 66
    0x80400e10031040e858000620380c411044032241003100f401003041c03240c0d000d0406500c0d280d00c0800c002890326082303894081d03081000a640c5074694074005010f50b00a1003010708c141c070a0f00030300010201c0480c00d00125400100020329001d006d650310318201e42ca80390a0390500c60501802d00200c0c40c0801030440c2e1900c280500b01d918038040740d01420b9174801038081c2c9240ca1060040002c2911000c0d02030b01625080180d03041c040e59110000f0f00741c0d201341020350400713000c2e1400c10480e0500e003551003400707148203e4410150324400040070800107812045103402c2d0b441500800c04a043c0103c0080340350040b030300aa0b07080380ca1017142c2400e860710042c1154840c0d10000403401404818896503422601c0c209803140380064001000309509405082141d00c5000090360000c590394991180780100401c9500e010b4591020942c83d858100f03e59030b803a40d00241c603000509401d9090001240c20841e805020415003c0005000c0145040c203030464014401f0241c032031a240242803c2c2c5c0050483c910 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 530656789 1250 530655539 530655569
    0x211508060901020a140415030b040213030501050604060e040309140a05100203031803180103110403021906030c0f0801171e1015031115130308030f0709050102030d1104090204 77
    0x4042c0c21102c11205e910386020300003030001d04058901d1082d000442e01d00407505041380c2000400a1085da00900b401070000d1000000b01302c0190041440395408a034100041555460b035100358407402c6500400041845405220b040a0b02c06249403000740600a5622a40c4802c0400c2840021100340c1001d60b0010041285000602c2140c0c04000e517001301441c100009005075015503140c031000e4505054a800c0c04d80d03403070300d40382017614011a00103222003030b00c4243c0c00c40c16401c0e05050007071900007400e01141e0501103015000b40546010b07556680d0101d80e07c0e24030310000380850701c40301c812540200f54102d41c0d03a225228595440400540c09055492007100c640d101f00d403190307410f8170760509030700e142040410040000f00c0c0c049107040e039203000c500d400561469224415194141504a83c03524044144402c01019511a00142440c0e5800c0e845040c01a03a0340c2c040c920444d8010b80c801c001c4926003084a070480130b1088601404a03040a440f41000010f07030b003041e0088155886d03c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 530658039 1250 530656789 530656807
    0x9040501092f01230906090310020720061821010c120e030a03020903100507020309010e06032509170f011d100c090b0d0605090721150806090102 64
    0x5004001c8204242480d14089010001d142c200a0b82101c15044411000c00d80c00170503110b078811210121401010b4401d0103004c403150034000e4100e10f80c240c4103000c00b4a42c0791420b1400f5042c05a0b5100d0007000c190401c4280800384401b0f068003d0f020788c020803481c0b001400b032034125080c0c107400100780c5c0010074062a6032800070108101138110101b1582084c115200264021084992101d07284c0b5002d44d0b5001c640d40402d2030001c000300340040b03692400040058441e80400034200d1440300b40e1320402081c9194080001c00e020642b03030105041625080e0b150600382c00c025112255070035060200b05230782c1d146149071a80c80d42d8403c4601e90f2b0002010900c1c100403e10030031100f8224048203400c1c904c4c00001c1e242d035403500540305241c400c2c0c0d034045400e5440c0c003c04004008000c02d5003255903495034003942c180501050b104090250483d10082070241e0b000c0c0b02c462003081141c41d4562102d8003140524405415015141c1c0350003240c1c2c0c0c0c4045422103044c032105219801c00070026070344e00c52038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 530659289 1250 530658039 530658113
    0xb0105010e15091c0b0a0510060302070b06011229180103050d05090102070b0d0f06060311070816050607110c03011b08070e06030112050105060411090904050109 71
    0x750340351038420454404404407001d034041c20b03500348040543d10000c1341c0c1c88119003400c94108100e03024042070303144020410800d0240e081030b4072030500c001d0741500c07041c3e989909805a010302c12006154800200000300c01354481c0300080300351440d40d480801d12400308221690210300031000f0030059141c009203c5854100240c4a46110403450f04a0a0350740c5581c0f074154440411045040030000005840c2406a20801007040545028005555542c03440340f9500c00502d022501e4507185401c05100162a5020740300307403100d012101e004c0d01e103000b016030784070300c074503400300010030101112983c2081c0810004c208891007892543c0700c86410240c1030140a00e0003c1c0005180e209a04080342b408195aa45442c0051070185003040400354644080964450b052030410076089a1701000014406102c899856585802076000704050b444590034402a10540141d40c0e5042504012600c01c50806030725155106000741c000041c1c0050300c1c2c0d1440030303104092a8403919400c50701000c00e0b01e2030301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 530660539 1250 530659289 530659307
    0x3010b0a030f2f0f0901050d0227030f0a0302060610051201080c0a0f1401031835190e060c01090c150f02060c031003080403082a031c0f02070b010501 66
    0x184010305250b00b04807130b04954414440c07402e0400101255000082d0003903019500d45025840707940c8100200c0500842c00b5a402d8450701c1d100303124418401400c0c1d640840c020700301b907400d40d01070550355961070140721400b04e40f40c0c0c3c08400c0190070880c092881d124881080c0c06000c001c0c02900c6005103c0c02007060880ba1074010064010f00070804121241c0203a8004031140e10a003408590200d540401e00c0c0c0103182c4240240942e8114040240d40201d12650040702200070f000d2000c0b010038200707540e0143d0103505c0004007041c17008510790000c00d000744c1d46d04040d003600a0140b813401c3c1c0502003070b80c25100c1504c400c0341d02250f01c80050103014410028448150400c1c43c02034200c0d4403040f0000e44e150809051742049071000000308982411101c0b40c88091508506850350702e590340e15040807641e00681c400d0086103174000d02041c085010300d0000c1d008584500046040c075a001d08685804040c80000c0c1c0351b55a40c50003e0a00c416460006d40001401850b4640c542c0d8034020000d020008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 530661789 1250 530660539 530660621
    0x150d0b07030c02030a120b041415011404120221030c06011a210c040909080d0606170106050a03060909140c0402040518090f1603141203010b0a030f 65
    0x24480c0c400219840700c1d5030450003551b010f001c20700c6043c00020034001d002c4288200d210880c07010412807501c42002d05010404002e90303c41c0e030b210b40c80402c20203150051380900600400b40c00154009031400d2950038a00d800001c80d540303604842c550103180f039a4010803141c0d0680e04080010821000300d00d101e2100f85010004003072070b2407200f0b01d031441141c1c407901d8841c2d88802c0c0d00300810f4aa0300d004040c1c4000e40388c4624104a0100305d400e200e20701303800803030784507000b241805030124071284194540c00704100c641c0303007555541c0d0030450182e0796908030100c24800c02d6502c0b04001741c886006c1c001c0c00e500718020750b4095a40c8184044d014104550f0102c41da0103203004210030007481d250089400c80c0c4820504003004c0310740b180c081482c00e01c0e00f0b46011039514810f1201181030841c400c06e6a02c1102e2180120140e0f13116030003500b507100c051031014240300c100240300400001c0001c070000e0a290070a85800039421240302c03150b0303085480342241103041d50310942400e03032454900203403005000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 530663039 1250 530661789 530661793
    0x608010501090f051c0803010b04051e010503060d0317010b0d1d030f0c03070606030606170d1e0c0b071e030204030f060903050417160512070e150d0b07030c02 70
    0x541000024074040c0100d114013401450045c1110b030030140000700f00c09100740c1c04120580d4a595a60503602d45402030b000c5e0303c0c807401e4500c0c40400900c1424101c50710902040c0c41d1241966190f904104025000002c154148881800342842c180701d00000c0f035010300310341c0300c0207074440d82e480d0500c1c0c0807501c2c01100c01052102852807410803860020549030030401d0004104d40d01e40400e045181540100c42c0000e0031107092560110802c0426003001c4147c400145440341d81c503101002442c0c2d00c404c060210400700c0d800c500c2c03540c101014030b007a01890420341d080c141c0f1301c84201e50311004225802c40b119000200c0d042807880800070110310401c0756071120700e001c1d4246800d5032101c030003448a06d5002442c05540d14415800c0500070b005950040074202c0b1100004814080d4180e19000080190000b02d43ca10f400460300e458030103020307861002c000c401061803e003800e19000000c0c00251000c01c1008000d0b0101003543d40302c03000c00b10558800d0828501030700703000d0005000d1300cad071000c4044155 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 530664289 1250 530663039 530663057
    0x5010516030b1f020123010503010e030f09010806062808060d03120509010e0a0311060a02040b090d02030102091023163302030f0601030509100218060a090608010501 73
    0x180d030343c0303e048081c0550081c0c101c0c51001640b640a80c0108464407419007072000c105030001c130398109181054125041031700284030082c0c45c2100304e6203070f129595a402003200309004d485190351080c0600d0340d11050241240307192040340c5034180c10301c0e1103051011030301d445692100040300ba44100c407690080b44c00e681008010505d5a809010300c084e02207030252007507507400010440c2e4425000500c15004079010341d4200c07080360030b005210790100c104414a521420000c1800f0030400e100b140d003160f96a080d0b0038240112001085410b5412100581c0d15640903c10318416658850b00010510703020b44070345074611858030014420109405038038021080601c01180c15410307000084a48950011140d1000e000c000040c4254604840a1000c1c6481c3c445e00d0820050507940214091910b50b400d001060350f803d40110103441c81141c00030569004000c104880315219005040703014110b410041030f44640d80c01103210b54100070144030010350f4241e01004145d41001c0002d001d00003e203019000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 530665539 1250 530664289 530664311
    0x23060103140105010f0309050a0b0c190e0d150f022b0b010816030e0715030b030d1d0d080c06060a0911070212031209030d060501020c0306040f0f0b040501051603 71
    0x3a45d0003141c16005042d2988220340c100f06003880400311440c1e100e0789000c0c0e06d0800c044100126000202c5054442d1405690300503458081c900715000d05400504c0c220f007200641da40d80c248119400c4200b080b2a85400005001c040d027800a07000d5029032a841d0f4580b86c2204c44001d804403008400c0c4100d59280c4200c2900e2640e010b0111944480c003040d5400000d05e00351004c500a28144a60300c0c002d02134510046000c0300400c14030355209069581c24406030000000701902d40c034076800b0b000d001c10300c000d007060945062200f0010716804018030f000000c1c05191113900a40e407150401410a4000340208100c0d85030101c0c81070701800071940200049000040103042602c500703140079110300d9903282d100e21410304c204221010304401a00340189400e141000d969030b60002d1080b11001e42c205103010940f0b500c00108019620700080082000d0b46440c0c48000080d5a882401c1c0ca50303503030910360321b0003103840000c10a0203144038100010343d610b041c002c4a02c00e50300b51524074041608098003650 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 530666789 1250 530665539 530665547
    0x10030e030703030203090a0b0c0304020405070f1e03020c010f0b0a1517060a03081b010b01300207020a060f141620130e0d020304080715032306010314010501 69
    0x7003595414240180d0380e85560f030310a0f14006290000074081c01b014810080e88502c1300c400743d070050388203490920080e26a808180d80a99081c070340000040c890249160118a1000d032220410f49a4200140b40c103070035403006425601100c1d807407038146032a00310070007903410b04000da4402010511a40c001a00000400400707240c0c100401b11044081c420119055603100603134500156407109030326950760f40d111600350400c20740c1d400301c1c10954600008a990795028659100c8450300c004284080048148000e2010a14000d0401249a400d100d001c00503110050380f0710181c070054544132072481c00368100501003456030300005644503051200c406c1040301c2030400c04c00c85a00c0191086c4d180a59200350703c40700c440050459011084030b50850104603035a00102d40c58001005440c00c0610042d0281d80e0303803041e48200c1030341da0f001400810290100c050144c070032001c5441d012503100d8146010114441000d0403440103e071101c0700b84501581c06228440f0060074a41c4c00522a61500740060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 530668039 1250 530666789 530666797
    0x810020901020714031903030b04050a0c0507080706110a1710050f040e010b0604171b09071b02060d050619030213110c0a0605010617040519030c05070803030610030e03 74
    0xd8a00756000002c15141e5014016401d4120410718945141d146c80d05009014203042c10500b4022441c0c20007280c4085403d00441c200c1e80f403a03849291270103515036519021076001c10780a9400c5940d0313100f0510090b10b40402451032620556071a9504101072180c904040e0000e445040c8200003040100004d4807485030311080048201e40c0080c0200840c201c103405003070010351191f403180380090042142a40c1c000085410707507081040318a2160030030070f106880446800c202c3d61080805001802c2544212000340c0f0800f4440c0000c2c000500302d5000c500340350090a10322035555110340803c030b0142050041c1c4081411090120450b052668000c540b107550380811b10019191100c2030754820a0040d401c981e000c106c0041100c22206031800c2080c0204400e00031040015030841030384280e41c108960150040750000040c0000e100d400c210402d00030b1189000710140444485c0c40030101d0740a0001200510b16803014581c1e07803800d20100100c02c241c20625006040c900441c0e600214000801e036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 530669289 1250 530668039 530668049
    0x1303020c040c030e0f030409060902120c0313060207120f0509150924030109060e04080d0914010e15061207050d030903080703020703031704050a0308070e03011508100209010207 78
    0x1d402e000380340b001c401070300b00d06030704101a01c03c0b0020b1004008002005200315241c103a400c100722a02d03460403074260312403544030114050303056000c5001040c62400075a000320300002101ea100b03803070385e4610302070740c10030744040e200c4900c0d081d0141c0c01c61b07400c101d945403140c4c11403038880d251224000010b5a81c0343c1408045010b07400101341251140c490f085030074543c000501108154103c1c9140d550259070007401003900e082e080600000302040d0780c14129029980c0850904d0425031a40c041100414990800341c1c0e040a221181100412003889044004503101d00940449080c040000d0309404028040501a070303041c4644000c8070402040800554104854070407609885060459020392240c00140008200040803010560001041d8007280d1081d111076103c6608030715100300c0703441f0407500902182c0002c84000d0020341300f0300c480d40c3d1225032814058101d80c8a240401c0c02c4451140091340d001c902d0003014881002c02304420307651841e40560035403801c007060000075104ca88501c14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 530670539 1250 530669289 530669291
    0x306180b0418050312220b180a1203050a110301030b07031d03180a0803130e010501020c090411011215030501110a020a030c0c0803030c0322020f06090a0914040b1303020c04 76
    0x800c54911b41600d1200500c4c001905c0400745c0708007810060000001954410310422102c803180440342d40109000c5000b42d081054000903055008040e4064500180141c004a555106142c65202488003450180d406681e64400f9440c001c40c01908903055411701758051b241040c03031504900000000c50b01010146c041d4040303140381d440081641000650011000340c04041755540704000c403d00050221807840e41004031590386d0b00010790320342c01c40300e1005400c0b00fa8840000d0200c1c0d40b051032810300d400c041c90590611a2885800b004072245049521501a0401d20420600c8401d000b02e0303003c5400c11515030301d0402044006035641c1c02e40e01c802024046030603c5101441664100c800040454105580d81c0f071504a401d060740758021a1100545030131580c0000d00050754030406840039a01518003402000c410b002c021858104010a59003d1182200800c0700030380341c011400811007000000e8280c2c1071903d031950080b80010714811700d20441041070008030703a0000d07034982500800d0340c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 530671789 1250 530670539 530670541
    0x13020901050d1b08150904080c0f0a06062c01030b090a0b07030c1e090902031803040f0603060b120f06010309060e0a0203161202100306180b0418050312 67
    0x2005032824014200c0c900002c42c506950341c900c01924425050160300f20b59a50f1034240d030b411545d030b50401012501d640d002051740e400030380014003420081c1885030002c8101c50a01107582011440d10f0040c40040f0b500c41d440c1c80041003003404040c401174240d0300c1c01111700029459505444410b03a0140b201400c258a02004a0a0050103000d10791195412844440c103074600444080e024000d000c40345000038000b144001c0c000341d4070044080b4154050354648949500d0304031079a0282d04041c055844402460544e0412144100010030050000d02e4041c04814600840075007261042d43c003403146801e041001e0b40341c0300b01000c2d031180e1151080a005131242c41380c0380120020b002e160b0000707040354541002010111000242c1c04400e6108400315440320b004003215144409041c402e50100c002d828461000501d402c07200c0307039241c4c0c40c6460b0000349143c0e150740550858000c1011810140d81d20005100c0b542010f0180c07900c45100016012049a19a5192a074900c54802c490182401e0b01c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 530673039 1250 530671789 530671807
    0x30a0906080907031e0f081b19151505060c0c0f060903030a050d020d02030106110c04020c0a0f2a15050403020901060c240f0e0a03050301060f030b10110f07051302 72
    0x60841303491360f001302c8200c0d08c900b00d100038482d03c0c0f107455146c103204d440f031540c0c0150803d6640c2e079481c0311541c1c0320b080e0000ea4170031880c50b00c020340044207800320229103048010686032180009458081c4140d03000304002907600d000e004441001c9070341c041c0200420403580000d501c000085940e1004245410b55030303100a103900700000d02401600c00c00b080e00010000400c203500441000e082040401510302e000d940f84200000c0f48145503089003103401c00d85051011817402503120940070701400908520a4024031003110a000700c0a018140081980381408100c0003d00082c1008141d0700700a4542811500015036a66051084408100d505c244013410440000c104040700e0090302986d80f110980314001002400c00004080c02040c070300450b0301e8070120300140a00d459a0941c03625131450f400c182c0c0491f1014540f0b408901403545660040105407100b40c05034000c0005551075a1045070305569480c00c102d42490705000a0780300c400180120341d02c1c070a000d801b8041030305005a40e14044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 530674289 1250 530673039 530673053
    0x1a0a03080a051306030c030f050108060105042a090303020607050f0904050411120309041512120c050604032606010915020a06050c030f0106140304020d14030a0906080907031e 77
    0xf003603140c0800c2c40300d43c03000200d25805400c2070f0741d10403031358a060009201c0803000c0c008035102440b5140099120a00404c1141070035401450511741c07600c1030582e254034036506a2082c0f458000c43c400043c1d00d445042040c103605000d6640c1280d02460010300e0561014000c070860300440388020310aa40ea800400c00f006203405400302c0200003d02a015110501c0b49420b44a40180b01400c5c0203d0900008070090000d0042140030307a900c4081d40083c000003038440c10841840310f80320070248141e1618590200f40d0801901d40f24910070303641c44080e03849000d8007444080075400341c51074000301d0f00280106d5a801070b41003c140c60721802c0800915150706012841c00c410f66030050100340c90101840068080f00000710b21070362405000c5040c590780c4040c101e1300080e285030941016003080c00480c005150107141020403501580307101e8102136030084160706542c018031b6440007085e04d90100b00010342c1c00c050056441a4444042c1401a14540300d4610003891094080d800b000c0403480d500c10000c071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 530675539 1250 530674289 530674297
    0x3140a0f0b0c0c01051503061008031806070f0507050f09131b0f0e040c050d1e0c05040203010b13050103110702040f0f02070312050c0a0c12020c0618041a0a03080a05 73
    0x7070085c0103e003400c0060111403040e554007180240510000120f603005420402c00889070345a005518091716103419521108500b2907866102c10100900f00c089011410f00702421802480a000128540401c1002c0d030148440d1282c00340b03d1107420884020750b03100e020b1031240e4206d159080b03050003226081c0d8184d03407160442819080d2000011946400188400f44605d210707050b016076030390701c0e034040004003181c0a800401c0c140c1007000000c03040e5042c00341d030a6100c4c0704100e0811103e0b1213400150607604242c015401451f00800c3d190008009800080d00820081c00c2c10080081100d8020703926200380080a4055a02c1d49182200c049250b03215a900f41242c030703411034a034101460000d05290348028050841410640401d04001c1c001040fa810708400340c440c590105100e980c1e0140000b95015000154010f4150100320b6071688402480300328405040c1505a9041008000807600c40c8284041d13413100800c0c6000d0a603c4200c082400c1d660000400f40c1c44811400003101c0d20b01c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 530676789 1250 530675539 530675557
    0xb1509100b07140706090e0c0309030412260a081f090b060d0501080303060a08010218042318160837060914061006030b01021e0703140a0f0b0c 63
    0x820300c1400100c5e20b90200c54a0141c3d08000c0784401d164031003c4907049140404e81d03001e485c42d0001c01040000090000321071103490301c2141c010586020215005901c8907880c1d1604826220014a03444a13a900580c000c0e4003c818155105605001804103002c4441c80c2c010108469a00c000020582d0307604029103505181d42d44041c030056840b407c58503241d4000786c40040c054110710302c010881400600a542d0612a9507804450f040307484820040680718004c082c0108002c042050514480d80d00d09241c8140c034241e00e20103a1801130002c240c500f590f84050980c56112400d0188440c01012811251414104d00c0015046640300c40300b55001740c0c11007481c14115254000d090402100390085a11280a42c0424407610701030003444d80c40b03d0049a00e00d01018516006002640c02680040110b0b501841112131114280b440c0300c0749040302034100c85030b51380200001c2041100300340d00303904082801f00240125003103e94800100c821050340c024034403c0e441340041d25010210b025182070f52 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 530678039 1250 530676789 530676793
    0x3140f090d060e010b0904120e0604090e0c01111603060b0f0909011a0108010b0901080a110f04090e12120903161202071410050c12070b1509100b0714 66
    0x44918a4404002c018143d00c0045550a09141c10f480746000080144220342007102c860040100c07010448101c4010080182e200c0d0080c80041448a41c6200303800350942c41000808051f03084d540050048070b05070003064103075400741100c00442d00f0240c05080c200ca9001c1d401180080800c400244100d03418810103411181da1002c01186d010b054008100600100054440b00e403d00b400446030f51009024906480d24204407000b47c0b9489101d003940e010300406000948114001a01026075009503844030032850045801e0145c42003620401803103001e00002480100c1e41044003d81600500c0a113449030547c110010307040280a0003240d1001c01002603000369a071441c901030200c4501d64111300e00600c030703580c404991100204107640c959440102000447c3d848084122050b90000e0700d0f08005000b0013a462100701a644044e041c101c3c441c5c064017980b0b15003002d0b6000740000301408188511410402d10070b09040701d104100c00d075407965100c15035034001800c118000c01340d40c0040255078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 530679289 1250 530678039 530678059
    0x60f1b0824042c07060305060414071206052206080303010e06011b0206041d0609071209030903120818030a17090307020901170d08060f042c1c050703140f09 69
    0x1c3c4007141e1101a6601614100a0b80c0c84000610040f60482245a100d40803480041580340f4007903840152443c1d40d9010200d141038070703000814000c1d0381d0060150f424190341d450706010425030b4040e00e03004e0108000250700b50b42c0f50161410b490303900a1300300d9041c00007100c105910744000301580000203802401a598459840480c03a41c0390498603a004210460840480c1072441c0c0f0300d01440c00f4220981d034424280d48201d041000818281310100c09200314420000000781648903240e407540c40c55140c104651420b40c40100180120700d4220b80e0a8104000200c08150000c0102c9900b840c5402c0342c40b82d0360f444046540c81c501c10042c010f03502403d803e00008040303c070440d900d06800b0f42074045d00c82050054000303030f84880080e00d0040d4040c41a18000a0904042c0c1c0019650b030740d0825060840724045030003085400191031504501d070040d503244407803240300210300d4003410746910b800d5107000401d8500508075601003691051001001806450100801080e0392510b540100b480a030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 530680539 1250 530679289 530679371
    0x10050609192301030e100218130f0507090b07080a12020c0c03010c0201110d090804050d051612020105030708070509030d08041106070f0f060f1b082404 67
    0x141d29402440608620102c00b0380ca112548a40030703061040c195040100f82601c1c44402c81d10180d00300071140d895800400780f049100303540d04918010351441c2160005200d40d00c40c2e84c0c80c0b0690328000c0000040c03010201040003101100c1040703039201500120f46903102c80244200711000200d0400d48401c960002ca2030340c1105c08042856140c0c60070450003041404902c04080e802e0342c50f0a05000102c41003440b40b100002c040b50400c1d50b43c140700b242410315103619640000c1c65190501c2041d070309036200b40c82490240c0c1e04400244c0280000d00d1001b43c007840c4030360008000340301c000e0001c2e040041c10004a142c0310b00030401d0781c0004400500f60b0710720894407a4020b060800843d4150391001c500b400790111070402008403411560807500c000c404035007a450701d180005070540221203036071b91194070540f010f540340b15014160301071401041c060b40100d40002d00850002d002180e090641d050008960307041d18800f18061902a01d000c81c41c0c0001c3c441024801c2007015904081c110168190300d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 530681789 1250 530680539 530680559
    0x501090905251115070f230a080108060604090f0f0512190e0d03050f07050307061a10023d05010b092407110d060c08060f04051005060919 61
    0x403190883c2030440309002d04241c1030b950800c0050f00e504002c214a508100b070b0103840303000034603040005032048202e01201c0083d00702169202e001001c00190400340140b1105d0420300c140c0e504003804441c14020848262241444940c5248006062645440004041140038000c84410400075502c10342c0b10b003c00c0c600b8840e552401e0749044000364030444205018600308051541c550b4041c6d840ca41003c2c404080f1001c1948105000c0e01c1601c82809031304e0014159000d070300342511000e004040c00304c02c01d2051052049850591001b50b40007162451002c0c0c5404480305541c0c5401c028044075070000e00e92500c4000940246252001c2c02c1c03500106060501e40e0060920200c00e03144800030341d014051103e00f455403901c5031482c0c442e040041c80b0114a4040d01801c1c03003030340100f1000e1030000c05d0b40c0341801c1b1110b252419000c01e410a003000b6080c541000809484402580c1c2030002c0c4c43c107406003007000000f5005161042c20081000c0c0c02c96194101c4400d108081089079001d01c44d11080519 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 530683039 1250 530681789 530681807
    0xc0c0c13021b19021207180f050106030c0804170d0212060a0b04030f0b0a020c0102210106091d220c0503102f0c0d03090b060a050109090525 62
    0x104500034005890b07400032a000a02551004030500f200b280400d407682000407880440313120421620507440045a0207650310150710703440700c5940c8001410109400404140c5038164445000d05140c01d500ca59110f8000c0c0302075900c10790001585d59204e090960751002ca014130420b00d05640d03c0400c13540c8800142c440707001d015901c111303216006a0307911581d292140c030441c00000d0140000b01d01031800110b804102c0ba420042c1c81101605048400031074508a8010740110360900d03800340700000c408c454401440380901858034144511900b4001a02182885210710701c405441841c00aa100192003c41088014080304c41c1c00030100c0e5818083c06001c21402a00c2c801e024800b250034016a0903c40c0d1408900f40b00e40c540c81d80d428045660380003002d04211041820707010841e9243c0c8400c28803002c80c5000e903c0e180002c140080d03060102809030020107d40c00b901c0c00d040148503607a04410701c1021036400100c081100d646000b03003c092612400348481031103000c1015070103440d420030490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 530684289 1250 530683039 530683057
    0x106060302392d0106030203030a0e04140c2a1207060906050c0a030f023103080406021b0a1a0313080f07050f15071101090503030702061b040e0c0c0c1302 68
    0x203043c8650464440307508903551840700940c140d208006c0c000001d809a400110380480090001985185030368540404140c1141c00a804071000908502e1f0391941c2d00402110749403107280f8070700502c1d80c840081d681e030069110050610f02c0204130242041050740007003000c658015028801414427206a45054000a42540c003207810504070308200110f40c42504e0340301181e0386007a1501c02e98419410000340d40b005950350400c2003501e0200104046a00900040220747c0c000c115203003003008940d074080c00450b05107201e01c052500070040400030f014442c10081e045005503941e42c841220051000382048401005101d0200e14400d8014a200c0074000c4540a44261910b00c94040d070410380301c2c00240e50740040b5607154404219054842c1206007408400f1000000f1101c489071500303032031034004a5402c0c005034801c608020100214900b40e1940314088883e00341003a0030601091501c0d0f200419915071660f000ca250700070b5410802c031903c11008042d041803580c246e02c440c44800396200c5003039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 530685539 1250 530684289 530684353
    0x8070309060503060f040903020114190e06090709050c1605010c0e1c03081302031e07050114030703150315050402120307030801181508070602010606030239 69
    0x400641d0780c0c024000c032403141000402690056190300c040000038036000100742c08641da98050040610000c9140310301500c041d0441c0c00940755600c448106451f01071a8404094100800b0b00c40180b500040b000700b0340782030440129960303485201c030314081e000740046911241141c50882c001d000c010b43c040741c50094150b40d142842e040341c205001d002040d005c1c0c070311950840300f811034020070301c18210150450003500c80944100081d40000f80b0700940483c001000c810607095134100f00702e0030410200102404c0c241360400d84001e036050440c5020040088041c50745464001d01101e088407100300181d0350084011f100410028900d200400c0b046804074000c00888038601c1d1041c2d0004142c61350b4030390543c2c5000c217036070a0412110a074a1410040c0c0d0200e61034008000c0520f40c0454518042c1200900511a03146040302c0282511540e500203014140704121017200e0904410070120100f0b1f40120701c1260b0291400681200740c410300d0101c4c6280545d01401340e581002d400c091041101d1208 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 530686789 1250 530685539 530685557
    0x7020c01030c17100f1418042102030702041d070611030913020702030607080a0c08130f020321041e080601170c100c1a100603020c1009080703 63
    0x540848125482a901203542c20301078042c030702e81d800d483e80d0380810ba41d44503426003582c3e80024548401c3c20340280140d0003140600b9101803e000d0444004440a414241c00f14106511800031050550003c1140600c1008104400d01d000f00100c40603d54003030030401c25043d09182400480020070441107090141c1031001a15520440b0311040140d40c078001b41d450702044804000306030368840c4050054503001e02141c00907940511605204030800c0c0c442050a251024030542214484980c60341030196541c10302c1a118517415503403410503032000000808031100d00000c3c0c90310141c3c01c2862002c0b011940000400a0814090800c0f1859041c3d00c6108901646103083c0e003800900070300e00240d02c40001000302c201144d00810903990180c3c292003407417103503401040123201d40d140d00320081282d0320240c000300094514401c0c41560080c188000078200145050050250362080104060300400d40e021425000e02003440700c000641020010308a03645003c42c0160019070080e004980510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 530688039 1250 530686789 530686813
    0x207080315030c0f01020615030703060603052404170903031611030c090408030a0b0a120507210218090114041208011e1a040308070f02030d030b0f04020d230702 71
    0x80301a1380d900e0058010384440d0341c48800f9100b040045400c51030745403186540010105007144120005540100040c0031600007496652041c2d1701150909028a03070b2400070800801c8000d2110a41031588851b0b090b9a12805000a441c41c003800080403000c450b41c1400c00300308825560041c0d0010010b505881c40002040104000380300d0840300680780081c100001031402d4402c0c0d000403400c080003424084040d4403181a400d23007608802c41281c0ca13a22120f010300a1702c0c20444003914408840b030310321159640c40d50105109400800300740c1c0103014004c000c5520310000390010428041c015007100300c2403809003803607903a00044c0502503002c03071140f900114440346000c00303104080004000c07244080346800546d01340e0170702c2109110f0b04004284000300002d0540ea0041001c280151008d540c2c080c1180101410200c04900c840c05152424152051743e45030340d050f018440700100d0300180c54150308090b000160408111004454090920240c0854070b6080d40500500345a0b0840f0a8030384c1c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 530689289 1250 530688039 530688049
    0x18010c02032703120a0302030109060b2b110d02120916030b06130c02030d06050303190509040e2505100519090f06170a110403080d0207080315030c 65
    0x240d04154a44040c150044008407460581e80c401e9510143c2250a20001e041c0c403130a00b42c02a180082c0002d03000801003200714554010740d005460803030300c014a044480401c0c100f065201a44144002554883c00c0d40e034484141e01654031050911070841c3ea6008072810b83c0300a40c004100c1490121110020a1300e44500140b042c079001c44807a48641403505548980006140090200c0d038000111410581c400e01d4a014150396640c01c0d400840d1261040c0c4594002e403507036500306034002e078001d020360340300b400301800700b03640726003050900982c0c5240d120003203405030000c1d90f5580210320580300d0050800100080400d5a00c5c20030b100c4443d0207440310104900e0308094590705000401c188a1503668400d071131141000c04002e42030590896a4032030000c0c2c0109015031114000c1030410030241d0351000308802460707201036650700401105400c805038002c240070358040074180e940b01295070b00381c42c071141d41120ba81d2900007217565120b04e0444006a4003001d4008610300a018003e030018980c144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 530690539 1250 530689289 530689297
    0x5120601270303031416050309010207050313030218190b030a02120d081501050a0302090d02090f100e060d0321090b01050f011e030c0c080c030a02010605010810030f081218010c0203 80
    0x1004000c5012445400c801c41347c0c0d80001e020185955400c00c45007000881c00c000510a41401e00c4e01c0c106010b02d540100714684e8414980004204002801c1110003032840d800c0b643c0c51001c0100c009900c10318840402d10b009040742c1e00940102e1444000502c0e6400003500d419131030920380e0745000c207644140082c600d4086800c0301074081441480140314a901940140000d0800030f0454048010182c0001e02001410394060450956000600410a0240071404003605201c3c0c04040c030b600b00b4001190110b010810007808110071940c0c01c1051040e061030501034044c02c103205002d069464203005001a90a104d214880c5194541d440d4141d401a0090720b56070110b45941c190961641c030060f806031201031001c50401c0a42c0b827082d0700040701003000d40401d080a0005503160050100302908481d42904400d0501409404102807004e80c6120740c416250f2201d80c10a1070308041c60000c60314042d4405480f000c1c0410410882408220040181c801e500007000b8040c081318020141d80305c0c4a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 530691789 1250 530690539 530690551
    0x70c0807080906071e1b0602070e06120304150219050604060b030c1e0a090605090403111c1115130f050c030f150601080106051206012703030314 64
    0x8240040c00204180802804800c2c102a154034034026031544c2d244003240c001007415806158201403c0148803440c1451000d2850102400e86907905004001e5500c040910441c910044407400203502603c070f004014948103114011a61110303200e0b1503008500140390720350001486030480384142444182c0c090b036a2180c0210150440380c4031500d40d07101a15100300e2981d014070070b20006241e00d81310b03050b4404044c0541c4414403802a00710302005500040c40c3c1c0b02c165a241040000e00003981d441c00c2e00c039081035041c10000c203000e180409032403c10307020041d803009444000701842401e540207001482001c251800b5191000980400d9800096094030520064030f4690403050002e610214102d00e80c034000d0b0b08880d002c00311080020f15003500b06000c1c0105400c0700d10346403418542d00c0055600403000f402c01c01419810000c00802d41e00800301c80305103c40405000c12180e0340540d1840340c61300b0011030200b40c54812a98032030100f0030b0703d10049001a1506450030b140800e00040580551 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 530693039 1250 530691789 530691803
    0x11d0c03031201090207050f031303020f03031201060804050c031504030206101401030e0c06030406020c0d020c0315071e050a020709020304080a180902071a060301090506181023070c 80
    0x10342001d100b034000350086c0c44200c0c1c9510400303040c4014804108003619502c902d2035a03044403581188180310683c806503003600c1c01b0740e00600c00c100004001509041c10f550140c03615003503651707a9040261910301a03890075500b501800b074a20130300c40a4284c5051089001e5001c5032055221b1021160002209100c2c500c4a00c01c03040349000729600ca500180c0e0722402a4007115401040c4000142085c5d00640d011508650f0026403018040c100b1f100c404100200ba00207408541074a80210f80c41b00e44002c00300144001100004610602407610613400782042202d00c1c8804000640240090703000c000c11070090312403194000f4040429000700c1c2d00c19648822100d0512801c0072051740c00003c407903588483c01545490202d0b101e01d151000d012007a01480003012503402401050920f128040d1a142c02641041e507600003003680043c8050b008101e0422040c1d84015001d44582031038942042104c0c094205041c1c0e940f1490280c1c1c4042c01c51041305000b0010341c035442820795500205590040c208 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 530694289 1250 530693039 530693041
    0x40308060f09060f2205011203111534020604030201051005010e0402030405031b07090b042c121303121803110301021b03030a050c1e0f0c011d0c030312 67
    0x9051540d5907005143c14203a144001d1034a840480c020355602341c00c040080090044400c0c181a8005148054010a1000f80c040d80c2c2c40c94401242390380300101a0103030800301c00840c0800402044800607141d207050071100454402d004003c0d203441d003d03070701640190300740000300f4001441c11410a045650586400e020b01c0004410b01010b500000d00c2541c2c907000900c0510612103882030071890b91106000034190032801c210707540007191042c1b003255014500c1e22150000c10340e80422034481c3c0d444c0c4403008c070310983da00707003070291404542d01c101d1001c2c10360114092401c5402b107000501500c4c4541c01c03856103051a034100319401560300f582200c2e8500302c8501040484d401104040b0f40d4540580058a07010196124010021154a405c0c4890344000b00308402c40c90180319032600a418084010702c0c124240c0a0050002d01d07250084107200340004000303014040c8001200d000c081c4040003031040c03e4004811080b09003c3d01c043c144140110854440c0d10715020003140e451040303501061002d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 530695539 1250 530694289 530694319
    0x3041a130f0f05010606020a060c050a050703120f0f06030606080f0a1b081e0c04090c0527010b121b030a11070b0c0301080106090e06131a040308060f0906 68
    0x101d401e0340380c080c0d0b14584034400640c04103c0a00645000e0512a0002d02c02c0829a00d0301f4002ca5030107100700c00402000b880070030312143e84242180c4940d605494402c001240e80c9400074001c021a0b25103506642c60068100a0307401540c1180040b640601c804008040c1d1300c0071081e8499100c16403008154100392400300c002254121042005801000490161910760b82003d243c40802c403a0a02045031000c03104e02040ea0801c1504048441514248134240240da1003a40032102805100d100325000001540003c042c0f150889108030300c25050551035a40d41e0405500341e03c5540070036202c1c00b10100190441070603104101c0100c090111061540c1e848940200040510303050644c62010204020001f10314000140c0740140d584050b150350b00d5140c08002400c6400e5036011341c01c1d00d800c107007034800901030100700180e00c2076151905144c0b03150b4507d041600030308004401e61028008100344020325130710400312807041909a07010703004000003004000e5a031404540f1594032511289189003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 530696789 1250 530695539 530695553
    0x105101e08030406030905100e1b19090f021c140105060708040506030402040b03060f060a06140403060b0103021c0506091321031806150b070b0109090c1205010203041a13 75
    0x340e103002d0b078240d075140210024482c05480c0c83c1e20700300c02558850400f000c5d031100e82c1c40a01d4ac10b008120392558800c907607110b403010004840c1c41141c030030550344c2821440c0001190121855803c103400c9502d01c01e0300e0341c10040014400d0220075130307044021000104c1c0038180042156009a080301503203040c2480d01007040600c2d80010310132600a61140042d0203152020020302d80a0303404502d071507045140c04810300080c0d5000303174844000c000a90800001780101041110181c0341c118801188a01f0802c005034060b10540007003052548009a40b088410000e61015000380e0040303d40051782c0d201d15080407403019940350060604074485500300c038400740905c0c0f04410180c1d242400700d641d94490405c50074400002105884060301d80c0004c0a400700307000010406030107000742003401c01380f0030b44031508008c03014000c0e80900e5a80342c01b12410700c0340c0c02c0040002000c0c1106031080c041850310707007a1302079041a501142c00410505000701050100203100e8412030300d0072255490040310b030f00c0d940 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 530698039 1250 530696789 530696801
    0x3140f0f190204090c0b1b0613110f0a0803031609150f090e161e080f1308040b09130b060906180406240804051c050c0105101e0803040603 61
    0x3e9109a036071144200085413412000010442d1070f6940c1e4030765030300004101c000446000c0025286d000751041050101504520281450700403840c90325040c3e40001280c184500304407030592100d01c100c40050500d900000940c4125021801801c04110b80034054407c3d403018015040900e5050140070340e41441100c40b8070390308031f0030700e01907200541e200c0d540302541e40c1c01c1d80c0440d040c1540750799441110b0342150354079601041c48803240020041030400101403074006000c0b138810400080100b0a007800c0320040307400d40781d00030f0002c50340c8550725100a00d50b1b40c0541c90480c025500442550310000039481421941e00300a42298a011420001c22500e5809103899200d1554010103da805d0344892040714054107209120303000062003641b404e000803080c3c1c40c1d031004100c0054100070004a0108218001c8608002503603000da0010300155641c0c0074013502e00d4010340c40c20003001a10640a40c10f042101c48131051010032821721a1200420a02401010f20300c0d4404c02007007005911a910076 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 530699289 1250 530698039 530698043
    0x109050a180c090e15060616140703110f0d030e06042304060f0b1815030405010c180b180102070509070302070204111c0f0608010603140f0f19 63
    0x24800618180c12a441001c0040c16500e11a110b8800e11100e00d15100f020766a42400700204051403400c0214080c0074402030405005610114010050115060500000c1075202400c1040c0044086070b60303542e81d086200035602c5c00d031022240321540c10304001e50039201002800500c98007216460584059803100c0c103454101301c0401c4006400388110455140250510704480003104504003000143da0a64100311070401c104d1004000148400303046905088102c50803140303000c4818000f40c07202d1800c0140c85841d2400108000400c4419030010104400d9900c4840c850703004000c19100c02542406070581802c0c04200b4000200320502d100d00c0300c45030510491301503a48803030108032050402d9803844042600400c4440441c41d041c054005003403d114003a40c00d00828040101400702280c0103003542039566440040c84142c030f0b8200a02500585000b032200f1030740c0e440c1c85130101a000100d901580500450300b46c0031080030030282c2458600c2001480b4402088825a000c402d45440c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 530700539 1250 530699289 530699291
    0x50c0d050a03030b27010305010f050903160602040905130209010e1608041704151b02100e010903021509011d1807020106080d0302091009060f1202070b0108030a1112030109050a 78
    0x5020317103e094000041003c208100c004000030b514619046095410041070601302d581081c0420050306000800c0d109220102400c4880d07030380785424154024400d54010400d10350a01c0200404209901c2e62000494400c1d03990090580c2d8030a400f1140d040140d0394080000d411042180d5154851510660054040c0e04006848034281440028680c403030713881045440c1c9034041c00382d410f94000910180069012080d020010300c0c99000404032103c0598107001d0106840110115901c1034144101542c0c0c0940b40084802c017103030a80c03509810050707005000a8450024140806c0c0a210b00104890b015102d4201010301c10315580882714001d000104565850744005070b0804204406201c00c04681c0300103a482c00381c001403140f250200d02a14090003101c0c0006c006581e441018640d401c141c03480c0100c81d0942c0140b0f824040d2182c45405081101d01c0400410154404001085100b0b510340710301413503510f005121520780045d00241c600c1d0180500040080d4902600460340c05020000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 530701789 1250 530700539 530700559
    0x3010f0207110102070e130b092d1002120f130605040308010f050102160510121505040e0601080c040506060409140a1508210702060301090504050c0d050a03030b 71
    0x5a040200d030840c0400b5624001a054140d2075540c040c442c100181214920000300d610f014803858503181c5000c0740042144840b0400a4900c0034103025110012403805503101140401555000e10f0454005032030380540580f480f41c1032005400d108644c40740c405004181c4240d035803002204280e20300100b80407040c0c25082d0500000500300c1c0304442c8100d00c079451394036965043c21b58101070385130181c0180f4155404502c0141140203100620011108210b4403518060030a00c0101c80746030310414200e04c80360404428410008000c00403000b5200c094504001c50020001078070303511031080c0f24003240758003c0e440544c02c50130290071081e40260098621403506a4440844040702c251300d4820021000c04000d01045038214001c10b10308800d4100030004503404c0580702501d81c14400c1140d5043c180280c01c100122030000250341720a0780050006840703607034510600300030b01002c840480d194010340700b10110514185a580d40400d41200040210b150300782d400b5401421030200c41075200407044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 530703039 1250 530701789 530701811
    0x21203040318080609062206152c090109080d0207030c021002030705060604061419170610090606050403030305100e1302130b150f04050904030306081603030e06090301 74
    0x10700c2d1a03006007441802420f851504900b0b8a0a04c03002800d1400c090000c850504000180c40d103002d0550390300710400040c0c060b2403000700d001070700c0244c0c8280d02000558543c1d502e40c0046090806000e10021800030301551655980380c201c480300c400050600000340034242c4100110350241803038074413038140000a04110f80005030000916840c13a8010f0780000382d0706080003400c1c071055411880995050101c6800d010803034403040c403905595409080e80c500c40c40040e90210484000078051088240001c104501c045038071100101c42105076195180c03000a080d03d0103116110454449075240c3c0d08242c156601100071341000342c44800480340d0050017154582c081030303031140100c0c6641c0d170840d92a0300c3c620502000649500800c0201882c080030004540c13680d016420180c3e5131140c111766142a5a244020140200c2c2c01c4036400c41340340707410003041640560000d02603a42c110100c540c040c2d03c40520070649401804000c1c00622604007000303031800d105014080e030300002000410040d8a035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 530704289 1250 530703039 530703077
    0x3020a030f23190c021c020d0f1a01060207140f0f0301050910060f050a0611030c07062c03100209031920030706050702100e1f0e030d0212030403 64
    0x601e114603160302e800210003042402d892103611404601c0d080c544c07032508668000440c6941042054041503490821540855590303211012090f82d12240744411b03140d0908045041e120f0740d1114030000020140046801400050304c1822141c000802c1c104507040c980a00c000b0034055a8065000b0501442004040d40d00780540c52003110010010712a8030101c031010b105403042c1c1e81c400400540541000e2009440d0012003d00351016803c040d04e56907145e900561861081e6146890311b8080d074000402d000380d1140c04005100030f5200c6000c148401c18450b8031040d1400d55606505a11a449080311003c0d1900502480c6000400350350b002c1014000745030211140b01c0e422a814100d0031050203a1031500c544d04003440724190300801d9101d08000001d482c41c4105100644104510040310b440c9078440c0010340c00d0180b010301040094141850030316805900030410002140c800303c1c0389111400c00007803d50241c90940d004205082a825201103a90f20141c0240e0130003042c00d640034808519 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 530705539 1250 530704289 530704337
    0x306020a0e0f010c0305030a0b01140a020c01020d0806280807090e01060905060a031104022a070509090d0804110d050f060c03063613020f090403020a030f 68
    0x25903107030381c07400c8030a4104200b498607000d0101c6052020b1110040701086d8090180e0380c0c003d000c0c240c0000c030340c4440c0005a8074140030700700c0300e0945100003540031581d82c0d001c145010300e00400e070210394003240c0026007519a80c40884401740c0115405220041d2010402126100541c80c4201840d105032680f803580d04200d400d42246241c00c0c1c80e8030368403065440074403c901c021301220804002904284000550314031440c440505049082d100c0141140c1e01d5030304a0b2035607003520000d591080e9000c10881070384903070030640c80a43d002d03c00d03000031141002c0c0d5283c0d110700d9040010306a5104150000c0d00c0b254006031095501e00a0b00d240880c2640710601d1090584d8054001044665640d400c0c5619100004010168003030040c000c2c0155501e45030550400001003140200550024460300d0141100d00c80c241d01c410001001807104950f184440500664001c0e9082c9c0042c0030690305002004c00103607801801030380a9604440446d226800010801a00e8036102c80c0f80100e0f08400d20543c00c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 530706789 1250 530705539 530705557
    0x3180213050403031401090b1f0212071a190b0a0b031305160311030d18140111010606080115030612020105070f08030a02030a1a0310231512061302010315030602 71
    0x15890712035523043d00c1d00c05459643c42c844104142280381a10100940391a00f120305044986000f080c2c0c003081000d8424102c42c040c1607051509124504414142c00c02d815101d142d2807c5490450b080e4003a05007082c40c41c0540301500c0b1030714a036807180300e031045540707240b20000c1d6114015a03802e041c1000f2108964001103001e420b21018070b8072050300b0541065005810801031002440034880e01d201051209021140e494a4044c1300c0116a4016507908030320188a841a510703155010403459009403103203050741c46143c0080f02d6003018460603000c03a4040c0c041c50300180d00410303610f030066100d0320080001c14800c0800000010300b42e0740d540740680050310440c110a8006c410090300202324403079921410714001150340c035109a00c1c0441d0701c68001b6545041c90a03210300340134031541c8440c403100780b100e0300700c7c00d4a0305103181005d81030400050390030b1110720070a600700301402c4a81c0000303041405022664071001140ca0240c1c0190010305940081192000c41c030307030b0700002040b464805410444 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 530708039 1250 530706789 530706791
    0x3103080403051b19050d211805180f1b0307020c010e0d020906090405030f040303020313050405060a0e04030e0603040510110f0f0f04051c030318021305040303140109 73
    0x10303c01080c42040018001d160b0148000d4002035404400071466501110070507142c00600582ca4180300400c0118101d5100b80b800311181403440490340072031003010492040120030442502d0b901006403151070741c00105112031001d0040b99081d03039030b494107540003071032981001080c020a2140d0b400c1c9070001c0301c800003d0b0f00a49522035995030007580c0318540e004203c070b0803000d4000c980d0000316080b40240c042c9010f04981c60000f0b040020070011643d442d6441183d02e0b8a842d9a803500a581c0d130b02c508140405400301d49070024032410a8020303a1b0143c18021b00c60080c05050400008402c0c0300140107600300002c1c1d209503000380d01c139800194011401400542800b402030000801542e504444130038403e0020456500b2003140d0320184d868800840400595812078100c0c000c06d140980d8000325840a5220510540b13401c1da04a8042124801e0b1006d100c1c400c0d00d451590784c01260203001070f41041802c50403800344000c0e544540c2d8028841c0c200002c3da1080f842d400c1e10b940d03100740c100550076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 530709289 1250 530708039 530708053
    0x90e061903031805030c15070501091713170606010c03050f03010611014d033607030f020418050c1305060619050403050102220803310308040305 64
    0x4240c1c0340c0d00f4003020345020f400a044032035054010414614508018004a80d004160041008001c0d00310f4a405a04880c000320300a00c3e034001075805500403900d00e001c0750780010000a60b142003400410349007045401130031a07a0b5035040152080070b03298404401304181000310300d0a1128440c007450107040f5554406601c444440320490860b95544201e5100d805805d0311040320801d256888020400c01c44540412200e072180c5801c143c8804280c41c1071520004402c0012079040300212004000c00303000c00302a040d20303100780060b0000d1640050f064503048484284042210320069241a52000c0c000160751014060880046c0c000040100c1d00ca4222800b02041e0340ba01c18000d10400b00e922008214500f4040001400792160f1128002000c5180100540180c000c00c00c1e24010740d000b800075941e402d15084c3e900007007444024110303800744800c2c00c04030b509030002003544d003080c034400c400c2502c07583d80c60511441c10181e2092103100020712a0007200141c03411000d44000c6108400910328 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 530710539 1250 530709289 530709317
    0x1b30110109270c230c0c0306010b09030105010641070c06020f0316060c020f150106030507080c0315060c0708061b0c030708090f04020a020f1c090e06190303 69
    0x40e0303148000044100a00c2400c041c3c0358500581c0403040700d190884a05a54101c1c01c01402c1c102890540515414020500002b0302e845250006019003101140200034a0b0303240c120686441405504180c0c10800345040f1034160591030f0322000e407641200000c01c1a043c1501d26551031603114030012180c1c611001380c1080160b0701081402c0c02d0324460005103003003480280a001c1c0052480744040c2c84540c952141c03104240c02401510071107401030060343c0c42c0b082e0710b4885000010080c1f180800180c5400c1c0041d084074440e070030707060141d100c0c10145482c607210340e2030742c1000310791602c14660b00002c100000604044108046d0780141103c0024040b60301e4610b0480c00840441020241580d10030404044640c001004a07100349612400d4a500c130b2149070046a00d5180d0030110756006880040c0100c1c000f40c0006080914410001c1184c007500c0c075090790401e8030941300d40b841011036000c030001d010b400b4130098440e0f8044405071030b100c22403110107001402d41d107040c6d00030380c0072524050200c89 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 530711789 1250 530710539 530710541
    0x30305121021061b2a080f07110102010207110f03070803040f080601210f0f06140114010309050712050a0c03030509150906030408070206071b3011010927 68
    0x8034098205040300d540384020003000d00b0074600855400e80e000c1d428110b108600c440c0104c3d800c0b000d40c106c0310140e142c2c0d004480407001c41c3d0200344242d0b50715074081d142c0c81c1c0562050084402199000c00c6c0d400ca40305404060295000428400990500400f80b0124142000b00003170002881040000b807511440c02c54158240441030300500b4000e00a424440fa0f003041c41c1c00300c0c01c00250300c030070010315007881030400c0c0021007941d85005088608026504100c00e043c4c5c03c40b581600c981d05008004020303508015000c466095000034442c1c0c0140e0400c0242d10809003078403d8180c002c0040e902281015514500240c0c0c590300103c0c0800d0703000c2040c50b107500b001036614501140e030082051030b06d941640050300501008200802c00000014000304540f90081034070856607010b2030300f2128030112540340b1a80301990240c80700e40340c1e0355540c941910081040f6424682c5080d080c0c0c440302240e41c1c46030905030100c0004036040c00a482000103070b4082e5027400610706402c8104480a41825803041c030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 530713039 1250 530711789 530711801
    0x7150516020106150809030c01021303030f03090c03060b061e0d05011205100c200c0103050a020f070b06211c21050a060f090501091503030512102106 66
    0x39003160300d042414414000e01c00c0103030180781c01600745402e050766841a00c07442c520850521900d20350000c00c0040842d9060a5200c0c2501c0c0300791140c544240903040203c08a070750b02400980b000c07020404c1000844e0040d44011041140501240d18000759003540784000e146810781c481c40071800040b1044042211310420340540713401504003803105541c0e1a52680d03200048104941d0700c4c1d1721005811070034068840680c65803081140f034800c80142410603074980d2500403249001c00e050000181200516101701c80320301c240d01d0b007014100411a25010810000140660f802640700d01200703104e0b44071031545181790701550000b0041d04901c1c40e010303400001d8840092081c450307101040c0a5a481007150b18401c1094080c1c001081c0c0c0d152000390011740b055030701c0003420311300c1c20401107140301c01500321a058030042d403001d220708840c118820200010901c000340010300b052141d80d04401006c1503454010030340b8030780b0000041c0c071001e58185201003480022007203002e940d00c240405c4036600400d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 530714289 1250 530713039 530713081
    0x40803070b0a0e0309010c060203130f030f030506010305060a140301060b07050604030f08061c02010e060d060f053705100807020d030e060c070507080f0304170106141302071505 78
    0x91420084400006000c03040c47c01002030845030044005101d004d0140c1c001c1a4242d0482d9120b041c03604141000b0b060018080c004500190031f15000030500d500a001e154010200504110310b0b0901d000d801c0402c54039030318100355047d501c9000c0000e9103c60a4041e025007400f95024050368209071801400b02d0032005084001c1c416080e04100e02e41d0303100d88400c000c4411f0502c180841003110301c012205444400c0420ba407022002c50419a00c17100707a4080402d8070107281084d445540c442e02000010701c0840c1c481d0440000d01d640080c2900490305590784030392110403129442c607071078100150030480294140400070f0114003c0006030b50b0f04000c3c8088244550400300b004500c580036168440c0b40080142080c070034005242010003804101e030380b00501c8010144c841140102c90519125031052080c15042e400c0240e510700c2e00c06041c4181c508840800081c07881b494044024000101806507130f54201030f0307080c0044ea0120b9003910504900c020141e01c009000c3c50084098140b6049000030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 530715539 1250 530714289 530714293
    0x1113020c150f0c07051903020f01060819140a17070209010617070f1701090903080906010f0909060b030d090e090a110d020307031212060902030f160302040803070b0a0e 74
    0x2400103030b03042c001103181c00c41e6001d00c480d0340c0c8004908007546005080c050141e19810300c1c4c5044000d0503400714400b211000100024003440d980c2d030312256030b903401c1c1591548460300540302010016620705460120300c1c0c2e000084c0d48168034182c480480790000d10714000d4002900055400451170304601c010b01400c0c00c0d041c41048424004511800120004e01450030300500d42802c2c80281d01030340c04c0c46051038110b07200990310b68403240800b001e0060154100c000c00e9100010075903015000c11014143c1364b0381c0903800d01c01d074a0109554090603070008292881a51042d88600c40d440c140301600c040041a200c070000e13140303000300c203d551710002440b803203054004004080024461014200464904442250300034119000090408840d51300c01002030400009513021907070804000086a4036040c810004c40b540e41c404101030340300440d0000030120f5003d00003401040c00d684100448a0140781c0142465100c0180502d90341c8040015a42d16a81e0004c00c017104c000342c00f40c40d90b541c240c400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 530716789 1250 530715539 530715541
    0x3131703091509030a2a05030405030705030102070201020d230a0e091501170c190206041b050d03050d1e24050609310221040b0a02071113020c15 64
    0x3c1584038000c100103101040482000f008100b8120206900b0010f5400001070300e0744620b18042d0b80d2035000388100c2e030003401070f0300d000501c1d85410310959403540d4040e006010002ea400504407100802101d6811030003092020070800e00403100c0280074103529603160700350180c130a00b082200d100001011074114070103050305004a41d0303000078000c0e07401541d452101101d4443c41c0800c0c151380100d219070401400d01a103c0d40b01d031940095110300650041207280c4c4103040070b00c0040090080760003180d4103d5905241c1c032002a2080d0018044840104400a042c240030350103501c2c210061011400059218104c00700522180d402c0019141010b611503107160b450030000c21001c0c044d000c44948038440e4400143c0300d520141070401c074080c00c4880d20341c0f003569a2845820003908143c030ba01250115207040d0007038031100741d00810300540e0804000c4100d0340c1c9460380000030b503000950448445100b1072200c7c5164440c0f500259600f1040384000d80c5a40c460b0152a01d4020402c00004030424280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 530718039 1250 530716789 530716801
    0xd0f0f050f01050a0603020c030424080c0f04170f0106030303050915160c051f0f1a0108040206090102010f18031701061b0c12030905090709031106031317030915 71
    0x1004d950f04481d03a03400c01580f12684225064114010b0740d01030000344501d025a03444400100c0241140c00d1407548600c0c9258850644001e118042d80c64a50f0303124204200a000c48946040d084601504a00440d00d00d011410245030a491156000721301007911001071081c415005d201c0d00e0a0221103010744880c6180c540d10341c662505515483c441403010640c15075045c4202408002580c0300c0340707040c00d202094901ea54000404180201c0081035141c8500c0b9810400d80189004880c101690f4504031521680c00300b0406611903000181503640e207860b035041c8003207140500103440703683c1d40c0c0c0c001c0800b07040e080c081c1064407840c840d40040d2140000500845800042480f1061000703807080180024a05e050f2107100043e400480404000398003840030117901005032001e4076000c2e220300c3d505885410040d1580c110a0000408804040e2014005814510040c6520408040c0c40c00000c2c05940c44107842003600056504442c00004104000f100007001465a520002c0c000880c10789000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 530719289 1250 530718039 530718049
    0x90105030103170c03040602250302061c06170c040f02040320180c0703110d201005090a03020d09060818100c0e040506030102090f090c0d0f0f050f0105 67
    0x140401002250485100707448440340350300344e410b040c020404403641c4545403280a0741e03a080015030384218982807402d005203003011b180888112580684000c1c20908642d166012901500e89502c000c26a00d00b0001004a441000d5035409000034010700403480c2c0342c0c4103000640340c02c1c1e036820481e039004100c1040001c0b4080d542113143e40081c100e04c4010240780000030b802000b100300011340005040284082c2c40800c05c01000340a22940b140f0341800c1c0c600818a4450110115641c00705511504001017050410400508103d8031800e0380ea0001c2c04c205220111201a220914a580f18400034001c050b010444410111407608102c802180b070304400900700c0c400100a074a08001001007801c82140c100000b00b05108007510078007003e004617000602240000c0c1405110b5814200424401d080c184212454400082c2c421011070900b10700303000070300390064012803c2c4e000c2040b030350b01d005006100b01700810b4070143e0082140600708411000b134540140145411070380c0900100030581e90 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 530720539 1250 530719289 530719291
    0x201020105131101200a03110f0a081c090c0b03100f050604060f0c060e0c03100b130c0c05010f0b1509102a0506010e010b07080906031003021f0206090309010503 71
    0x3442e00c00482291155529180400c2081d80c5d0500d101d40603c0c0d40030560081b0300340300a41c0c00001103a10700d0302d00380001c0c1d40e15082d032034004d04511001c0000c1d0f04007a07603045c1890400c0e80d090794007042c1c500c059620200503101540c0301341001c0ca404428800b071000401101d20090840e0140880054100800100d0030f02c07840c8140d2060101c401c24450229000b170100918060304000204207401541e03000c1d40d1140a801841c612a004480d900e01d40d580880c0326121000340080c041c2a8030340c088600000051080410728400d00200340034200002e0703024021346602c40c0c0d4000000c00c0f50f0002c00300b481150751514501302da070fa0b0818001e01d02c0c261918131850443c2c4c0368030315005c650303103060700880c034440241690102e0025005007015030500100040ea1030407120018429000750380c0c0c0c0c00c280802801070200040820104015804444c50003901440e0040c500c030322012030580d0b40358005015007421030746c80c90041305030030002c4144c55010311640d58405900e101542c500420200004c0c440d00c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 530721789 1250 530720539 530720573
    0x50714130513180c1404020a020618011b0c031403040503161403220e0405030d110d0c030f06050121020318030304150605030d050d02090f0319020102010513 69
    0x1030050101e5076402c01c0c1d900520b180480016000c040d00c00181000803002500c0d0045401d8150402c0d989003150900f40b00703c64034445168041c0145441d2406400c00c020711045110400350b403913103031040703080c0d6409a0f03c0400c07101326203a006104c8101e25000d8046031521480c607440710300600802004c00e80108c06c845002d900c0c001c0c14410b0b9015407a00701082c0500690804491002080105115500c80324404460307242c00d105849140c0ea40f0f501e540303e12421280180160814000f00c01c2a031003a030000e200741c0c84400100c0e41480c0e103072590002101c081d51000c400280c1c035150004940c80355441540068007080c070700030805003102400d80405540298200b4609640040010801e0350003441590b502d00315801902d42e64281402c000e100c034560f443c100b02403103181c2100059140b400165080101401c0e07101d09040460f03c408440094002041446e004000d80400e401a6036041c030447d640710f101e1038103243d041b0741d160000a0071602c00070500002039800e181d6a1010a64004410711810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 530723039 1250 530721789 530721799
    0xa0503040f0c0909030e0303031e0a02210109151406070609080f0c1009110d050c0a0801060f0504090f0809031e01061502010c0e010807050c0a060507141305 69
    0x1440381e240400101000c544054640c1d50418804500c0c1210760300a8040749020396101401500140c0030540c5030302c403c3c1ea1811a4680c2840300118948012484903841b84085a005050014800c02c2008426424440c100b50b0100c038401840342903c244501c003213001c42d8417902c004241c10324000d4000841d4407001580324403408503240040288640000000b164482c10007903c5890000b0a07102d15006000072007458040e40b241d158a05015110f120441031300f0020303441c607000300034080c8901c40d030b82e55109403690f0051201402854680c0010300000300708140c0002841c51414140c0103901d031040d04018400c0c1d042c81d641c040802d40b03000c40d000c121900400e40958078008034002a1500000f498201c1500c02d104a507a50003201c103600c460120f416580701c2603407050202e07000301e08035024019402e000c1840c1d2901050f0551003001c410781e006d06c003420540e19024034040d045151101807030048a0a0351580c1c00c024210781d016406000c60031400e09a5424041040954421521700380074040c026 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 530724289 1250 530723039 530723041
    0x160e06030a15080606031c05091c050609060609180304090509010b100309060c0302091f020f030c0106080d08040b07140d020c010e0d0e031005060f0603071e0c03050a0503 75
    0x46280c2e8803000c0100012080703420700950740d000141d103604084410390b00c0390190340070741d412070a84d202414a9203505617456500e030060080030090800e080d5010f100750b8a0a413065000003400420541d8014162000100302d00c1c640309003080102c5200400d68010b012088c0400204039900006a4050f15145c644c04101c03682c402107010b005005805a40782d01c000e82c0649086803e0305644040e0326a80158800d000490309030605405a01c6818001758108051041040c01c0341188441440300102a2040c1c8109038003131040640756422a0031821480e95541c001000107000801040908801c0da0a02030003900e043e840e281458000209040e083c048080081c580c580354038002c84004072200e41c801c5454950f0450707118000e01f03d0940244607849418200310350180206a00c41000c88000d00410368031950f0401203000d01800391895030441036081d4824181c2d6a01c1010b580705a4080e41c81c00071044040003620010b0000c45980c00c02e000301c0c0c004003408254800d046070301c88121810000d42e2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 530725539 1250 530724289 530724301
    0xa02011b0218040501050c090609010e030a120e0906100206040b1b0d0515011107062a0602070209130305043005010218121b12060a020d05160e0603 65
    0xc444412000075070009205203034080c200c41c0c02c42c01c10b0145020700000c000a59640b4040b010500c00c5468280c3d201409004400c0550b10695806a000700080c00360303402c01da01e80c1d440313004041d05204910003117101c841c1e150402c5d003401e00c550f5a101801720390181c40040e40c0c10000c0c0d2075070000f17000500130240b01c0380060120304110820041c420405054242e9400b1840001e00080c5000d0300c1d6007945540d4002500d210b50b200b01140c0d8200c26158010b0002245440019520354006000f803081130130750011a80044809440d00c0c0302803c0c0211030240c0e6550403031041160294006021000388110504d010010950100950f000c0d51151000f10042c40c007130300c800c0d00076075541031410201014090740b044200031064015158486c1c54070407500166514108101130f6403840140c40d0980e60001044210603c83d60342c1c0d01030410000b4110000d032088034089242041000c50703520618940005034031a00000c54800c3c3c0f54003d00c00310401c1d0010340c1206005103c2444941c6e1107100e0340c00032003c500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 530726789 1250 530725539 530725577
    0x80d05130b160c32090c18040513170304031d01030209040207030201240501270506180f011704020409030e0a030507030b0c0c060106050a0309080a180f080a0201 71
    0x4501d40000d900f40c9000e5848040e00944081000c44002e110960244040340022100e40380b808010014410503843c0c0c1c41303401c0c0302a950080309a01341c041c2449180c0403c0d1741c07100d1091900170624803c140722a5807080c180f45c00005000006180e24040400410021031f03840403c00041e46c0b000814000c1e00075202e03004030068000c0d5001d9a500500c0004c0e902c00701501540085d602d41d050148100074401e501d041900243d03424800d26021803003100903404484a0724140b622205407000b00c80a83e01d032030724040760140c2c2201e0ba40d1140c0010502601b022803411a004002c1c1000c2403070441c0c00d101c001082410000c038040d00c000d014544800c10740c4c00701401a4240c1ea42d07024040c02e10440f0542da420000d540d288544000e4400400d028085108280240d08540d03c00d01c41800402c1c2503441c059003102d25a0041d5aa40105950b400180d00050a001c0041070307041020b50360304400c04109845030150080c00e51000034200184003080140c582c001c00d13410b050540900382400800c0720409102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 530728039 1250 530726789 530726827
    0x1030c0b03100623030a05040b010506040506160606080a1505010b0307050d18060f020703080c0f0901110a080a120c030e07060f030e01050c22081e0a12020304080d05130b 75
    0x54901c13000c8100410011580e001c1441640960401b890503642d44092060a100b20301405030003020400c903540b84202800b080c203800500c150f03400070f5216507406070170b800d041c40c035041211540380081801a000702c1034024030780542401c00e505861801e10001c05441442400007140e038203911214800c82020712070b8116180c107500003205011007840b04000000940c07003c00201c002c01d65050200d212981c840c01070b116020000c1940f1071803c8440300c01510f909007410a40a590701c6040000800a0a0a0040e160390200d41c1c403403441c0b20055800500c1540e11601c0001e040500c2d040c0e9025034900c1c0050400d080b5401c0e41040c140c860203400302180a007466211190301582004c06021036411104020022400d01c0354050503000d59a1001e40c5001410303100392034966100c120301100852504400c2d40980701104111603d0310019641c0126615800001c0f001582020404101c4008188541c6001101a18050307181144d9048440c105500c40e000707108003040c1c04150b0b031010b160391604070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 530729289 1250 530728039 530728097
    0x807030c020f01050118110702060403020f0303040924121203020c070b041e050108090a060b060c0607031d01020c0304121106072603150f210601030c0b031006 70
    0x340030541e11822200c11b10402c43c545e07902060b10f01a6002440041207042d5031409a000700344902c0e2900d1a02088106104094515458042000000307941302c039520071080580508004103482d040c50315000700c1080441d900003141440a1012100000c8103001030004241c920300b00180c5a101600600d0300c1d1400c81e40102d201940000b07408199041604d2034400e01c10141c111101450352508011500038406590750f110b6603102d50313801c0300002c140350880c1d140c80401034036017810035841000b01c6141903001d5803410042641c6e1920850300250030341c00a4446035280c40298980040d20105d03517038901c1181310301a1130a00c48500c174020080c0f001190b40400d00010b0445840c0c52250806803015003e01920141180782d09204002e1503030014103480c840ea40c0000325440d65068101400b00145080102c10340c08090310800c8111402c6014011a0b0007641000801c101d40c114a0461402216a004185842800e10410520064510725101982d035285898514130380100c44000c241c070030103244 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 530730539 1250 530729289 530729291
    0x2030a11160e0a0f0606050f1e12060a3c0b070b0a180803220b09010606110f06180106030b0c090112110a030b0f03010911090f070807030c020f01 64
    0x8009094000d02841034090b2400f0f800c100310400140c41d2000440303c0c0d40c420507002c10014440305141d6100d16002e0111400c3c0036404482046002601e030100d503204001c0002045e1004044c80304a08002d50540b001e015400c48030031081c002c10b00c00400d01000004600303400c151a5a8840c160a8400080c01c01000420070a03600c0c2d44841c17030a00050441100d00d8041c89117882c140d008820403140c8c01d0ba101940003001c06107191502c14800b0740214090380400b417003c5105c201c0c00c0005a103550014400c0036140700000e02642049002007a0300800038015045030b00038041002100070200c1c0a070781190100030754001c0c2c1d050080780317140540161380c006452820700004000010302103000070a03200100340e0310100385031401d0340481d046a100440801c04003805000c0000041e0081c2e00003000d80e0310040c051030341c0507030f0000042d003903541d080001c481201042c84001c08034204000c207150052921000b210f101d01e0305000007865444002c000030201078507026070245003402489031890801c45100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 530731789 1250 530730539 530730583
    0xe0d03031803170f01050a060503071b030f0207050f15070f050f1b010309050c120c120114090a110103150e16020d090f03060c03060f09090c0603050702030a11 70
    0x2405030003c540441440b450b514410006071000040440340ca041c1c840c010183c0120b20f003050000ca50301d0b04001c1689042c8501003540c0543c40c40801d0b500034000d071203980c0b144840c0900000080c20100181d2109018001114260782c81d0f41c3c811425086030340141400503100e48042c2042c606048101c00060a1401441c1c4040c5139240045948940c00000782131448815080d800110115030000a0281240d0070000541410340380000e0b0130101c29601c0c0085a030078011907000541e620305100700c074400381e80d950080c586d8881503207009035030b1081d0320364040d00c11495503031242c0080d000c6441d141810180d0781ca01c1c3c48030004043c0485005808044480c0c00345140c605103c090300280401c40754094803410a03150ad441d403040f400c1000360342c2100030361b040281c43c640c0c0d54000740c820301c600401403544440000c100c07004550b91100c000d02080c1c201082c05440d034200000128003581000d0101824901000345003030300041107400d06511450403407000c9585550303550520700e030016900b25610b4592 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 530733039 1250 530731789 530731793
    0x120b031204090b0418031e0203090414010e0a090203030d0b060d0e01050402030f07081e010204080d1e021504151d0d1101150e09031216030506030a030e0d030318 71
    0x1a03c040c0e02c07a4400c0d01c04208032003403908200d10384204004002c0020b07010500486501600341d4010043e0242c40c01224204040100003c040c0c0c0d0011909200d5584942d0040108000c201e038081d070000e0355140100201c07881a00400e489210358541d0482c82d54030f812a00e8400d44400b41168140f0301c12540412101d05910a5039018100503142a8824424400344130b0107408003094100032101088000c281c010003e10098820504420300754405540c20301000030b42c82022701107910171982c5a81d03032004820101344408840c1010025000855210980190008205008541c0c110f600700c0d0b0003031100811500c0045c0038065100c02c4004114068841030340d0420000380404c030801c1c10780c035405108041d1420300c500302c8001e20001c004000c4011010490b52165200345a00100490103507890710140620190059106403074031030701c12144481d0482c4a550604c541c58103c6030840250031040b410380c4004120352440300c1307502d12511020140c0b801b014003d6021581e111404081c56180700c100e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 530734289 1250 530733039 530733041
    0x27071202030d030e210f030a05061008041a090102070f0c230d08090a0306110703031d06190b0306192d0207140303090607140703120b03120409 63
    0x88a08034040d200c0c01d144891060301a00803c81e8080d6000000c100003603503022030441d141d220201032001c100d010401828440c00709001188103000401d40400c4604000003445540f10344d4440031020060500300380310010700c00d90074000569800000110381a100d402d001402845000001080c503038000a841701000096007400c400c8904218003d407404040318034000a80112045107503000a000040313400150150380500380084000d09445405a00c80da070301d10482d00c4010f401d00c19002c022401c402010303410701a15005040e070b4524081c0144030142229501d10000d0a2403410502c0440300041c030290650003500400801000c840c0c03541444041907500e002c032a2030501c1071500340990f400f0414540c0780390f420065080d403003100a5004442240009402c122411250090300c4003426600800800265018052907005409103081c1648064040440c0c080e40d0403050030b0074851040400d42105a0b000e1400540c480400c402c920716000905000030141968009100414042544541 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 530735539 1250 530734289 530734319
    0x4031709040903030605090a0603020d150608030307090305010506010c0f03230f031008060415020d02040b0d02030f06090126070e090307060c0309020f0d0f06050a020c070f06082707 80
    0x29aa840c7d040d884a2903185c060341c4050001a4001e803c0d00d00200010382410000304541450303903800940d003500e4205050540d4420380311540040d060070003d1060203000c1c4250b1360008030909150510740380c966218458101c0c41400030f82070180308040d64a00307428541c0c0300d00d00d030740820b2200c60f030700e030000d4982d1101a0070980b81c141c0c44042c40c0d507010030000400651130340030741c0e0131803420840307079103c1d0344001d010b544140e1540704420703003d12000900c2c01e0003001030028044c1d0000b000d41c03203103001d911a5101d03100041140384620b068070700410400c00316072030407800c21841445e40030702d68941c011940d241026903403041050403100010803104a03000300150512502c2405d091002d40201c080480a4a50a1401075032003205000c0c07160b050310b040240d056200f0310582c1030310503054554131014202d804c12140a02d070b00d50000b03008401402e082c0180400b070700050f01c190380301605285005000250060960258041800b010030440c10320b01e00315100f00001800f121803080c1c80341c01d080841c6c94 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 530736789 1250 530735539 530735549
    0x201240303171e09030d05100504050901090c06030e0c030601060f09090c0503070c031b060b0a060302030f0a0e0a08040f030308180d0810050d060902090f0705040317090409030306 79
    0x11107011818410300055418082c50045034500c84042001d84903e9041e03101401e00f504134407040050852a441c1406424401d4400350141103106283c00180170a42d04008c005181ca64542541c29001aa0b03500e031080a03100e06280c00030f000d018040c1e4007486c105d28880035a03410301c2403000004290342d0110140c00d82102544d00c02001a641d003800c8026945016807074400318000380001440d02c0c0c403410301310321040e00901c0d0990400141164001807011441da00351801c0741c65103000041c3d401d107800356030018440c42ca004c526602c1c24842c40c61000c0d0010f08036141e0075481c1c00d0b100b0002072041001c4a00140c0001409550719500d0084010241c2203101c124003156400001502880d83c06101030b80c80540c64025012441d60711904403a401c0d0000c0100e0844500b41201048503100c030f40480048622494000920004900420032001720081c145820556018100410554001d0035242100d6100f42100c080000211501d800c03801811031301a081032420b401d0405140e03041d040501252 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 530738039 1250 530736789 530736797
    0x250902070c0303140412021026090c0a0513110c03030f0915090c1011030d0209030111040506120402030712050a12022103060a03080403120909021c0203070201240303 73
    0x766002a201d1018007a6100d441480d0003001e81e8000075040c01180341d80e280708945804a40410340c0d127650f010820211070014500e04007a4100000b013502046200040b802c1104e501030310724501000525000c01d070b0b05030044810f4503040550038401c820710540e618106510152030312481c080c0489484180c1c12506a42503129000c82205c0c84001c00703244034041c285143c080c0c40380500e0b020a011041046112400c10890101440030141c3e60910140400030b203a010056600c4440e8130400d030940b182811120300403401000100890703601c20b070132140309071245a00542182e0340c81c00028188502c2c1e81c42510015100d034001c0003081004606c485c402c0d4403a405984d12140943d50480c8e0b200002a03050712030b408011004505845034002555128070007c204d5080a900c80e65003044981040d44115030354502d00414a031340744c0e040103560002c0d064200c021420b10105203a0010034040500480000950001c0840c6c501032013904480d003480100a6000e80581c04519030a203000810300c4180e00103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 530739289 1250 530738039 530738057
    0xc060f0c0e04181b0528030212030c0a0b16090305060a02070f020303040f0611010912050715060b040501171614040e04230a0203250902070c0303 64
    0x1020a224100d40c48505540344080395100009110051502003030810031550325107840c00025205004000c042c0b401c449034065220702d0f000a211905265404d00000340000e01a1101c0c01c81c4035050b03800449804450081140c4074091540d41184203a00a0721064046d00d03030301209002d58401024000d0322800030088540448510440c0c5a030340c0c41c000200745400c9400407034181903158002d0309405024140c0c010181c14550b00092441e4000e50003000441c4004d40108012508010a290f080500b400244561034a0750703240404000e2020311401403120200b840b41c14800a014a2013040d108c51908109103500e801841840350454801c940c00600e201000c42d040c0001c180d40b09004034480b080c0381e03100580003a804c2d18043c01e4000c0c43c0d04d041e1010b100006001901101c09400345005a840b00c03e5100c1068000103658503e9614540d25407040d108040162800901244041a100c204010341c0c03c0e031201c03e40b80c4401d00c0d803001c1721490000c520301081c080322903d0031342140e100b91118441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 530740539 1250 530739289 530739311
    0x22170310031e0312020c0f03040806040b01080a0f020112020c01021617040b0d0c210213060e033a0324030b040305031b0309010b1513090209040b100c06 67
    0x740350b602d00100068080168460038809a4000c2c00c21408984103a41d9592140c1d0501c504d982c01903070203e0087c0d4450f0701440180001a540c82d23015004003030241c00c541c00e07185c4968003101440c001c020b040014900700c0600c2420b465050303d40c2c5904041c0203540e1101943e400801010700d01a094540040000419941080c10f00481d821280c403901c05070f04017507243c1e0044009145030792140c1c041c0600f0702c2c09021080483e0803458450b410030000182c0701c0c0040008003000d4401c0b50481b4040c05080d290b2a2455a00080c3c02065540d6000e0fa2254402041d0b80003043d00d1955094220b40403142c103c3c0b018810340580000c902031071150300c803442c0000c840842c03c4001c0854400507161500c06404600441c0c443d074000e40c3d0015901000e03125a03c2042e90226165102700c0310364105075902c440c00078040c6444180840c417400c035800c0403814000e4002d00090640031038071800251540c00181d210068441d600403c0804134001c0940007410020940a841032015a42c22981a4980600201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 530741789 1250 530740539 530740583
    0x40905102a03110702040c0c110f0f120708030a0903151104051314040b010905060108060f0f03120d0c08130314070f0203070303030e0d03052217031003 67
    0x5244880c031001c461081d910508160000c2618405024100c0e0b800c015000150712a4010310710403400c135036a85100da9105003002803100b014683e180c0d02c00c0b440c1c040500b4440d40c9405440c11102000c4807029508040200c55500d415100c1e44a600980400b146005080e60401c070700070100c0e4000c4007410780000d114030300b0104031740030003a40c0103005205010620030760030411794115010701742d000700141d440000c0d81e031840022012502100c1c02215000107210704005400798036007086003824070300e03113506148001601424000311042c0c0104500d2101c42c1b441d030b504100c00c41d00342600f480196070707418440607404090100e580c50310780070a0500700410018540c900084811580581d00d00340b0b001c10402d10110654400d00040c0d0303980710201047c40142e0780c1840500c000b140700380c80002e418000100741c075041c64442c1101c0b1003414500001c0040b005000c214102c10782c043e09420761030b840028680003040e072010808114030721501004011450403817840c20019680100c0303841500c4000881010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 530743039 1250 530741789 530741831
    0x801060b030c0a05131202040c021506100903061b021c1d01050415020c190e04150905070303090302090a0207030e0f04020409090b150301290f04090510 67
    0x44008541000010611410315010349150620f40c40c000e4680461070994050948140d04070001d0400b9452001c1d0440c605072058441280450000d003070700740b5100c0004000c5290080c0264002d1580203000c01d04588103029540c09991300032010448409039008180f82c00b05031540c440094402c1050030392003680801c40003d4460a2039549898803146507101c3c401c205200000700741404030174000461a860000f00540c501c101c1d95008090000006040001043d0761f50403110845207a4802031046141e03100304142d1080d00f145c1e51806c06902410f50705c00801402901902034024010080205680314010408036802200c440f01580c40e40610b410481c42a0507000340400c402c18900d0065050020501c4902c1000a200505280ea52a04101640c4030050101d8030807145a00300410704400080c2e05982c900194020444080306074424200d02c000d890314803100e40507040801d00c01c0d03900c4069941c0c00d03410142c001e2001030300754545281d0b254003603203030f904400c0d003070000c40c0c030180701000346e40b07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 530744289 1250 530743039 530743049
    0x10020118060b0f030c0603150411030406050403170c160f08041d010b09060a0c03020a140d180b0915040801061203081302010f1101020403171c05040506070e131a0109080106 76
    0x2071032868448e22443c0c41900145e104040c0c0180d01c85803000500180c101c05107100d503010b04408501c0303141c0b524004220140301c400003082d03008c2c0c45003071110a11102040e200380c0c3c0301401e070740e002845403030420b89101004070308010803819000401080300c000132014002c092000410011a50342c941e00508010301030072108a401c07003000d002d040c0f01240300c0c400c4920018041d0040e02d01201207604d4005948640e1a034601c40350b80043d1480c1003ca41c1305419002c0740d1003501c1985282810038082c00380c0d500c90036040303a100312082c8001002040701c113001c6800500070b6a0080104564850150a01168000702540410040000100c5400c07419400b800b009905030341e285140c117080709050701c600082c03000d0300c0741d5590b00b4017010000951280c420390320391803c82e03200c0c0d850b4161114130500d0a4080134601e5441401c1c0018080003c90024403281c114005080c001c800d01c50540210b001d0503801340071244003900341101046103040001c0081e49240c001e07030f1a680c0c0d56460300310082c2601c0842c803034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 530745539 1250 530744289 530744299
    0x30d03020307050909060d02040e0d02120f0a0e030313060207090b041505120f0f070e0907060e010503040204020702030a0b100b070b040602070c170c03060a0c0e10020118060b0f030c 80
    0x9403003130610780300780156405140288100132650981c2c0100c2c04669100e07613040f0440c3e0080030b4103014150108030241c14000510321039440e1800351326880c0040c0c05460f0b0350a0034031490b5060900b8a68040c802c3d9042c030380725081c105c06841d0342c500c0001d41e54016449046203140c07406581d002c080c200741c02103444d0300030709120000506c2d00d40414800c550300c43e0400c690250040b1410340d18688d500703000c0000c06180030310080041078202051141c0c40000585280c40aa01011081080c0e80e04045140c1401800342406a22541d039400828041e01c101c400081d414040c0580d030b00c08014041c0043c038001c808480031641d0fa40c1e00c81c07000c1903043c03082c4e43d405056141c0e91800180040c0c030300c0c0c008004c2c980c85207000312031090396480c00380c00c10011400d136600a90001190100c00e0300741040030356801800641c080c0301c09200c686002c4c2c12181008600340c000c02941da030380360b01b8a000750800b0004254000826015094504200000b4580c2000307a0703203c2d5248a022038002d00d00041e95180c1e03664010301e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 530746789 1250 530745539 530745547
    0x9020c0a0b0703021b031206030c1c1a0f090105010b13030b0411030115080c01180302010503060406150f17071704060b0310270b06041a0d030905030d0302030705 71
    0x310290044001000c10b81015001c00c1000d0800d40c82c0700051a80c1d0141500540e150780e80c2d001031140030800185042e00907440518481419561b000301c620452640b5a0030b03204225031400c0842400203003140c170600358841030050065130b48a620401d131044c001c01008021a0340c880300750321450300c2000d8000f00900600c1d0340c00c0c4049443d1614598119102c1c00d0800c1c003001100010900350340d40e5415041ca064a00d2408100f004020f014261030a4030928040d10040005181101941080e01010741008808000a0740c65241d50b84100b02509100601100e003c200180040134040d600c00590006280320081100701b010200e11a0b0003040316444001078000240f03400101440c0c02001a145251240d0381414070351003d0040c446200340351a40424400000240300240003150404040c41d04042c10081d00420284c2558540020046034041400c03480e0718211420056550f0049030310120f8980580308250b000200345084032030640c01e0b01c0c1010942101a002c9001c00c80300385d008507500300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 530748039 1250 530746789 530746793
    0x70215010b131205031c090510020f0d0501080d12020717070c0902030708040c05060a0c060e0102070c0f0f08060f07140c061003210c060c020a05240109020c0a 70
    0x15249003a01c18072142c10043d07851815a140d44410181924030b600009810450b0500c183c01071200840c0414003840001d869a442d40d6031070f4100a03421003030b10307030115940030242640011502600104501031000356114035000b61074100c07140041d00803a691861901100c0824020398101d25000b0000100f00e2034410360007202588450000c840d1280c0085020070130041520245003c0c00c0956034104075458680341c011403280c8660007082c4206028484899219030201c00c2c511002d500c6003000c16a0702004000902902410303000520400b03613a5004a4080c250003040412a421401c0041c50582e03030b0409551240c10a88022800d000d008000481e03a03401001c171011180c000c0d410607890310b8403008082d400e0140071b4500c04c0b442141e03c0401c00c14464401000d940754412442000d28000700b006015045004200d0001c042940b22030600007400d00038868603802c0354000c002c3d00c0800102800030900881098940c11492507030400104105025100340c80300d40c1c1300c000003071403c11090707 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 530749289 1250 530748039 530748059
    0xc0603060510080103140715090602010612050a062a170a020c07060e030307080d0921020d210603140f010504020a05010c0c050a14040501090902060306130b030102070311010507021501 81
    0x51280d80751b152043d1240040c8800c00d40994980021142d628101201d00784500282540e40b240d20400001e0881580d0340040349020586080b010303408040018425441005c40100394402200a007120981011804047d9005a00450303540c0c8810f400d071186070f4822019804a019090b403903507440d0310403c002e10180740560f0040c01030580c01000c481c1000c0103940c403038215038000d2149186150b03e9900100820040b40c01007004000a4849502c1081240700003c5d900e45402f100c86c001c00c10390140c1030302d032340c400e01000c00240415a40c0610605485e41040302d0852092007425510384200707a891340352140107114544c0210350080c0413180b078601d4207004561001e100c580a64010200900002e070640e100d044c180000c160429401260400c0d030000c000486405911040705e803400c1221280050b65200102c80d072020044034881c44680250898800030011001c03926015803001440c40b0274185c02a180007603602301003000b07100c00d95851a04984034a029030b140310100d044503006000070801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 530750539 1250 530749289 530749313
    0x80a0c080702060a030e0d0c0503090118090e150a02040803040e060105120f090d0e03030301030201051c0501060816020a030c030e0301110415020d02160509070e0d0c0603060510080103 81
    0xe04909070408265400064807a4020710561000c60703501c01e80600d0010f01031200d90150383c51410444a01051a100c29450b40b1566111604010311042100c040211481492000c0c210b800c004000c61401c0550b015a034082000d2071f12903c4507001d000a01000460007242d0586081001440c03c0c00d180070340e29107880d1400703041681404800c0c8010414078110142c0c45119003550f5940071640d042c00912541000d081003c1d440030006550a008001d880010071a4116a0f0a11b401030399070b03005c0020b4407015031591188101d80341c01e01000044480d03001390024042c400c040f00128440d80c0c01801a60b64070f040c1507005000c0760504d0b0140700480c2c050003244983d40c00250020582c0380030204030b100503a01c1500000d91400b03250b80340c80650781d8100a60000d906680c0020007000c610040802181c8055100b810b10a00301000000e001a100d0140c400c4002400341680340e42c81c50b80e141c40035030051780d4010900042e241400006407441c1201c402d100b44500d54841d110b099085840305680c40b03107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 530751789 1250 530750539 530750543
    0x20304030c020405040510050901060e0c0a17090109031b0f020f0f030703030216140102070e0c090418031103041815050613060e060306090c0a0c0813090f09080a0c 72
    0x941d0411080140c0c85034001c00e40304078407a001912142d00301038084c2040f628007038010206030385400f2091004201d0a8011600805006080c5881d5490400210f44070020f0120458030f0741c082c4000e200d00d01505400059803284a52521070000701c90f40c11182d644420a100609110a4101d5240142c03e000403000c04207000a020000c00c07685001c08641b503d50117600490040c0d03c54440c10b03015100306050500038251046840c3c1d24483d040000030740e075074498012071082d4200c3c0030110b54a01104821615010405807061140303036441c02c0325070030581c101300056001ca8840604503400030004000c8806849244c0101541007184005410003401209401d80428050b82d602280746d944040140800440f000d485207001400d15074020700350400b04c682c8501589040c81880703810380e1307100d01071540005d5000b540f40e216000b41104840f0442d164201821a8a0018010910403601c20f422005d4900b400814401c2c0111440c01508031854003402810081040c0300d0368942d90711038028407007114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 530753039 1250 530751789 530751797
    0xd052a1015050405010e16080a02070f081909180c18090e0f070e040609051c051e090f28151d0f010e011107080c0f190902030403 57
    0x10348500a09000c40d40420740c480c45406200c80100858542030151501606d10210702110302e0500e050945c0594040310502005e2101c6140003030580c1e84d141e41035130036894002d040d0490b0036038542441d1160b40d21212001c08100d011241c50811130340a03d1503641201c07c0d65240c14908481062941c0042c648403080204011901504a191092003203000019003400040000d08240c1c180c40b261070408440c00c20110703a00648000c002c482c0703440200d554001e412242c081581501032800074200f1609400c1541031111641070003490a0740036000d40129400b0642c0d02101d104654143c40c040d000c3d41c42c000d54040700282c011941703410240400000003503030b070100c02c0b41c010708059400780100c8035401c4015854030f10004003415560140c48d240b039135040b07203118404048084d804110b0078800c5480c0c207418000c8101c0c070080d40343d11034817280d106801d98000b65259180c542204981302e508601d801c1d88122008414041d03d4506180313018001c0d074804807481c940e82d1500a28002070b400040058040c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 530754289 1250 530753039 530753053
    0xa0c030216081c02033103090e06060d1b020c04090b19060f031a0708060d0611040816051e0a030311100f050a0f05010f0506091207030c080d052a 64
    0x1111044c0042c40c05544016907840064900c02154103c0c0025442d0b00103c0185508102000c01d4200503102c040e15540031f401412580c030305002c12018410507007040310552a01c40c03405c14404581c1801400320004ea030a5550500090042100392142010040c0480301e251000c6806c1a241d4030305100c00d09210352011036240c1e92000c180c0c00004c1186d00a840d000c80030211100440d54074100d01e40d0007096030030240080c9c1000d10108000345005000200143e40c0d602c0d1201000480d0019200109114012520524031035100c0c6211295507101e40ea000e020031604c6940e03040505046580204005007014281c07a00d903480c11200001038a1f0302181c140510b000f51400701c042d0303001c0c00c0c0030510070084c00b2620342480481102110710344080e83c07014900d440c0050040448140098086900448400d922682800006440503050032090601441544000000c104901a06600b10b500321401c0e1040e1034003920302070307844c1c1c81400d2440b013a1144103c1d003a40100103c000c00b02810b002e40f8111408 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 530755395 1106 530754289 530754337
    0x41505040e043509040f060302031504031701030807150501061b030e06031611120d18061e0c030603051009031403010e0a0c03021608 59
    0x401d1400440e04403800d084034007444031124015400f4041000d180781c0c2400ea134400d80b0581c0c080c5041403450058410148542021a5001350140c04c0300c640415101020301402002141440301241c80f41c0a0215180c10044c040c5100301d00c00c5590703800b81c0c10804415080d206611884a0070400103000503580007148a000508400b0241001d0056181c255400d210f10252a0b03041440401084082205004908040b0140381c40385043d81d003001d52480c0d11003540700031451010380100300c1403601042030307444030700d510084054440101d030066603010150341032418418865002c51460955032602e034420490ba074202e03810100503140c0380d907075480d884102d80c81c86000080d950f10800005c0c940140f0092241121b00800c2c1c542d65a11000c0f50b00c1c1c000c8042d00d0b1903400324030f01005096040c0c0680b00320b62580e140d000034000c3d840d00d00ea07030740d504591018228802012864240e191 = true := by decide +kernel

theorem cover : BRFrame.Cov 530575539 530755395 := by
  have h0 := BRFrame.cov_init 530575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 530575539 ≤ n) (h2 : n < 530755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
