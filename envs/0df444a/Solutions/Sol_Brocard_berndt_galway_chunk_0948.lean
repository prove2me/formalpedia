-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0948
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:22:15.52034+00:00
-- url     : https://prove2.me/submissions/b70ea382-59a4-4920-9ae3-7ddcfde73794

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 170323741 ≤ n < 170503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 170324991 1250 170323741 170323781
    0x812180a1212090b060109080f030a2003070609020a15050409020f07140f0d030506030a110f031002030f07020c030a0605040c030c0b0a09060806012307210305011a0706 74
    0x4102c01c80f0a0204241e4070090a1418480d4a40c0c2c403015081c000d100c800d0090100b640242051500c0c0c5c4a00e141c3c1d607081c013030f05e4242e0320b100b5011540d525a202c030301003042e2a114845030410f00060f00440500b24824501c50380041101681e18480d107100700c2c0c280e40c0365414a07003001c110340001d610501c14048030241c00c0c000d8100141ca20f9000024481e00f100107885a0000c0c0c1031007910300756410b80d818090508002c1002000c1d20001091600c058000c0303544030603a072080c40815107150064160a825000320709171000640c0300c50300107500a046400034034140703507200581240c440300c04444195142d00041039640c0850340703076001942c02501030507218a202e992946c8a9403030484550055880b0702020504401d150f400c08842030080410381000c1030f0524060300024102c8110000d10540d001003000c20036481ca0703d100541c6c003021341c0442e01e95100b001691031010758800460220b40001c0c1480b00104205660500c80d030380103842c4409507810500c0584d9110007601e05d2052100c010382d005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 170326241 1250 170324991 170325017
    0xa150507150908070312050609060d02090a0e010f0c09050a081e011512060506030105010620030f04080304290403060c2c010314010f0603050c160812180a12 69
    0x340c00600b4640c2c0b1940710340c2006c0c00c491210405031400100030900c5850300404121450315a182c041000c2030741220005100d698490003680104441c200000046d0710f44049000d07013070b0096111503554899902d031911020fa03036100f000701b805000c1c041c41800fa0043c80b01c9550903154118225000807043c1c0000c9050180c840c20641c011107254403045034500305203440c5051220b1840b86d41e4025005030002c0c4455810701202400d410070580c401c4035286110309582030294402e2068500c0c070841061100d40d503036079803080035507242c2060003803110060440441d208440c1840d80502c054100b20039040f410980707541c032814000e00311000300e2000e216000070200754400c00b9401020040343d90400041c648030500000401300c810108036490000007580061103034010380c0c13241c641140c02c0f5180c08203c960301c11403480e075180147c000071001040d0300c140d02820800004042c2c105000948170360120b9a0b10401f40d40c0d4815500c644410441e006120b071340c0049503a0b034012002c030f6681814511400c8400d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 170327491 1250 170326241 170326253
    0x40510091415010e13030f052109061006020f120d14130c080c0105030f0601030b06030406060806070302030402060d0e19080405030f0c060315010c0b0a05060a1505071509 75
    0xb8402151031080e0b001c0103020140342200780641011001000000d4581d0682c1d0240031150340140090611501240f04100313240f41010000486010751882c0d2818102050500c0e52504141c030010081c4000a01c08118180f000942054280f00da0001340700c00c1080c8221401c144e4000d04070342e4a5a91281070122440b86039066050255011007961414440c0c1e505001e030b81c0801c0354001c440b09820910540420784c0e803040c10b41c3e420a9000e01405000d49821005a000b001c5600c14550024004800c00c82403204c01e0780810100c4601c1c0d410f0301c03031540ea00e00c2c046089102c1180e00a41c0705409010700c2c2c4ca0310185034003110070120f5210443d17201041210104c9071008810108981000001400384510b00b01070103601481c48116008108039400e81c80040d401c2d004c01048072041e400800e90440450303214120b01c1c426203800040a07442401d1060011000d8070080b648280200180000001d00d240041c40b800d8039540c803984c5a50608941d5070303404001c4208070700d110041689640c51880411030b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 170328741 1250 170327491 170327503
    0x16080309030304060b040204120201050c0109050d08100509061c03120e010e07050a030b0f0903040e0f06041a010504150908030a0c05120c03030604020703051b0d1202030405100914 79
    0x440c0d4002075440749083d2070000140c480840d40280180d00601c0200001011007a02c404034950900b4901d440780d1905555038010600024041e00a110354600441c000750041801c5002d0b01715220f1003d8420b490341c06110031003030203844240c0c20448203486500c24110f031400e0041c903140b00b817a1084035501210b00003800d55282214101a60b5920848041c44440803c02d43c0028030707098500b140094a10f4854032200c9400900c01d02c44c0c60403900025a1003401401110080c040c410541101c1c1e04009125156194080701e259001d03034608a502d1050b0340700b807140b02c1020310b8143d4802d880c00c0e0903c1079145000d141d140300c0005000b607446001c107551805102419041c50140d8441003074010f1414520314019001000280409040001c41d8010b5400320403650310003026200983d8401043c0340407552841641890b45010140d108151a09500416409010788041e40d071135407802c03e69041c01041380f00584d00140705600c0300007000e0384d0000e0758100f101800c0c024100d230b19004803001d1007903080a03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 170329991 1250 170328741 170328751
    0x6030e01090516150305061e13020a0c0b07030e120c0f060f04050d110c0f0607080d0b010e0402180f0a05030a03020708070b04030b060904020a0518041203020a02070308160803 77
    0xf2011583c203000d41054100d51912841d0780b864140b140b42450004105060b05010300d20303958011452116166890300054040b000503284801c541ea08140940141200d030b00843c2101d14070607030703070108113444d12071b002e041c01094110001d09190740e142e002014507544110036030b4039a4060640044028581805580d00c01c00c94052000d1180c6414508282840c003120040020300c0304000381e480e20340000107011307400110203030b64540140c0f03400740c0050068007503050020085900051180c0044045030440c50715100e0a03203490001d00c501c4030410050b4001d800c1e1091071102c0d0340d90003036081c0c5000d9540c400c145c0310162400f210541c0300d002081c14401140420b4001d6400a001000340c0201080091300500740142d4003030609040d0303600d0005414020b080c081c411741c4264049400d554909582e5002050300400156950031360520500010034100d078180c80c604000020340340361a00034000c03100b4052b20340d800340c095203040d5a1544a690400840e00c6000c0444071202000201500d005502503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 170331241 1250 170329991 170330023
    0x604110f07050c10080a050405072d060201060b0922090b0103030e01050a0507081b010f06060306170703030f0c0203060403171803040626010f0f0801140106030e010905 74
    0x40e40d5241840c9140841d506101405451002107034130081d035000385403a822940015020138281c1351070404902c1e06849420940034111000810a0520481200403454a5051030005001c84e0b44072000c5c3d00300c0c0c4241c03141c4145610104603680780f501d80004a60745440c2c000310359a00b4960717198040c504a0724180b00c00c40f00c000d6a0001441411340041080915401c01d2034200d2030885075420060083c06003880c002c1103042c01240c51000c21920070307030800345001540003c0009940c8098100090b00c95482040c02003480c0000100c0c040d0054242c416103071011000038603580d440c1d640c0c01c13a506440019050308000030340c0d59410050350140720140c002c03170281c0d40340824100302101e540c03c250000b038100d01041e10b00c00c4400c0c0c682080401940c0c2101c4c1107041c5103860a161080c030303481040e00d95800440392400000040b421500506280342510f0001c2c060540300d40e240e01416080b10440c00d8850a4025180010050319100350008080d140880d000422400390740d075600c929000d0001f90340064 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 170332491 1250 170331241 170331247
    0x1401060e21060f09100507120911120319020c0a0519030605040c060e03060405070614070206040e010e010510050301120201090b030f0a0e0a170a26040c12020303120604110f 76
    0x361104c00c100350b00400160060402c210306100402410314110215440c0310103841c0d00300c4405000a00c81121030440c005001d01c51303284421884144c6940c805404038007a0545480b0560f940c910008814200340409012952000c1c00e000400c031140700341c10031150040b0140100800060410702600b40510b00c1a06462480340c1091005450a950b4100460182e40010100004075a0000324103044a80383d05101c40f041c11040b4003508035200b641c202a4003c040000e000801d904107003001c070b04a4030000030145950742c0301c60412040205c080006e20000b041800180b0480c984100300d2001b041c4141005100581d60320b45c0718580c1d41003190202c07103401406042008110349809014125a203400181c0540d0065581c4d0480800b584130003080b600030049080f039010760260001d400c00c0d5a0101d0b030940c40c502d0140090030f035540102c408545546030f840e0000340b5444000120201140c2c002c0185040041d100f00126440030000d142e103a11540300d030910034084c080b100040401e0822140710f40d603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 170333741 1250 170332491 170332501
    0xc01151701060e0c27190e060306041208060109050414091501180905010b030625020303010e0106030e0a020603011401170c040b1803011103010302041401060e21060f 73
    0x20071502c941d446401c0c1c0003040002c12000c3c0d01440d0485195200d441484112903d0780341400c00b00e0b0200c26071a681009200e201c1c0010300d1540030400044500c14858050a1380e29181031584803901038800a090720040641a540c10340200c40860340020b06140500020340d0764400182541c02c40400c02a10b01140414449500d1080c040b080348101d0011162800d94945039424500c200c00d0302a20002d295a503101c80c0c00c01800b0b40000c030200100034111b40103820500904804140803002401480d0000c08400d480e140c00402544d040307031900e0240485a80c4bc02c0f40560140200400703904150003442032210050f611940558068580201f586458207028000501028840604a18907140c01410031809614440458090711180444151110024400300e080440303400c2010f03070715501341900b5503800400e0f840554100c0b4001c90b01440b8880e0303690940240000c0c00c0c042d000003d418a0f05d070310344c14201008088000014041d0b00d101258114070154144501039070f030300103002d10380c0382400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 170334991 1250 170333741 170333743
    0x90a020d0e0c0f060a030b04020d0b010219050d0c050c040c051e040b0a0c0f050f0a0b130c210b0c0403170f0301030201081005060c060601020601080718020c011517 72
    0x1000c0c01c80880020b0400d0008500010070500d0107204851045100050340041a4440e4100b0403101c103010b881951151901c0701503a010340103070014640184100111104400c1100d0320004207103030801d0203404010240300086480c0841d1220a0300c051040e8220040346450768400c4129440040e40e070f55407036010542014131101d006050605049500340400c0c850b48160340e0440b864080c1904000040207000d19100022103100c0501401a006000c0206200301000c0782c565041ca02c21910700c00c040d6101d400c040850110180f0203050500035480a00841d140c000156071441c3c59192100c18800303070f5649003a080b0900716400d40a00790046010000c1042900c1444e01d15601d00d1911400d008044a40d241e003400140304c06810449820041640d1030561810440900406400d40d035a82140a444681c0d410b8150340c441e00504c00e050002890120106d4400305690454840e00401c00e10022264083c0d0050100d680e1203559400920134091401b0114000800780d40720242840c1c03060518a07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 170336241 1250 170334991 170335001
    0xc05090115081f0816030227070e061306031d010c052b0908070c091509230405070e0c0a120207030c0803010b04090f0b0f010c060b090a020d 62
    0x10034500c980200a4030003182c00c000c1e142c1d4001c100c1c02104400a00b21200310080d08a0390303010311100e0140c0401c14005054080e4802c094034000d985600f01a0360701418404a15044023242c04403a01d087c0100d840f99105441c41c152200c1c004200904083e002d1100403800703c07241d80846c000c03944e00c50400c103818555a01000004003154000c0003840310346c441c013610074410310300001a5411440c201c0e110000c80e20200c01040c10003401c04010501c034520b042c9a0b01c0d8022081074400c1080650006056245c1e809181d40c110191502076014605d040142c1c00600202e65020301503c0e000604508424505d5802314440c071b01801c0200700032443c06115070103d40c0c0140c00c00d58080000c0110484050304072418841c180c50480e801030b5144030508044030315081e0040014142c1c070700000005544118403000d1f03c01d84880b19801c10207543d40461072011541003c6085800800d00c40d0509015030264200200260040b80c000c40d100d03d11034000340c3c10210464402e4101c80c0d0100d21581c0e080020310031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 170337491 1250 170336241 170336249
    0x314010905060f06031c020f1c020606220906021207030c080705090a0b0c100f02030601020106061d0d151103040b071b0803190204030807051203070e100c050a0c050901 74
    0x218045040210110b86c0f250108003115000780002107807000d80e03510800180ca6218085000c2d1070b641071220380143e48904c405103103600144100404145140b0b4004c130307a89100f2410900e00a6090460001103010309411340b03042e583c2c2c0391300f8080555001d00010f040c5202d00c04503a80010b0b47da0010310082c0001c00301914110401100780220703000c0d40c8a0040c1c920641e020342403490740b611041c8080e00c1c40c145802000125044c144180c8040070442d5802840c000c0c41c1c260020700116480703030b4045400400300d2002841c00d8112100080381ea06010803003110300780c00b50034015503801c0c20744541026158800072010060100008000501045540f00c1390481c00502e4031204505980d100d690881d1030840028040000c0040072514800701c14000580340d42ca2610190b44032580c1c0e06280b00e507034004840640d1940904a1561070621030348040760704c1202c03552940e084540300002481014035120007048203014000241001040c820005940003600c140c00c001410390500040c0483c0c0941030348 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 170338741 1250 170337491 170337511
    0x1002090316030c03080318010c020d080a0c0203030f040609020901080706030609110d0507030e2d0c09150103020403020a09090204200f1806031303080606031618031401090506 77
    0x1000d20000f030b15500c0340c1044a41000c40c0c00d41303a8540c00c1c20440c6002052564195540c42d02c00008803860300800d00d40c0344c1154545421100780d0b201018941a02c81403804000145c10400c00a0704500710703250001d17002030040d8000070300c0c60603650104145000a07000000180d000309010440503605004103400343c45514000c0c4160040080c61a13403030300404070f005024079111030005450a2190703003c0b8040708440c3c01111070310540c030220314a82038584402c4815011030303d500444110400100300c59086009400d00006540782c000070300d108820340300f040341055000c00000002da0b4074030240781d0281c4210343c0d00050501c2107104210481c0c2e4905c081c01c4c020007240800701c081c0c64008041d070f48203680400506a44407203010310750340a082c0e514180c6034411030220600c5102410348945484d000d00c01c2c6c07101c000c1c0c2d441c1c041c2001101e0000311580500707900340a2080012a106800502c120f2584c03d45100100740c132659426203440c03c1c152820b10320f0799035902c09024018100595030304854611 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 170339991 1250 170338741 170338783
    0x503010902060403121e030609180302070b07051c110d020604020f01120207060204062111030c1b071401090504060f0b160f0303290d1b050310020903 66
    0x40d0100e14035000f42e110103000102d00e201c11050303460003095400c0c0f041e5003100040d4a80c401911003d002014580a5172034142c2c50614034413801c6040c42c95040c5040c6e0160000c0010380d1414540401690040700200c80b84e02600300307011661200880c11080b046401d0b201d806100309091a0070b843c00303e11841210455101000b40070241c0c03500c3d02000e607800000e2034007078440750340c098402000c0d00c00e0070f6008000510000380020b046602a220071441140e045e000265803800c61858001e5075810008201c1201d000c101246800c3c44900060a03c05090700280da8070040181049003003101c40c0e848000308017005400b10358250781c08a1164041d1004030f504001e03540c02c2140141c1d84903072a0140b543d618100103004a50b1a2080e422014155480020b40500d81050318005015100342d83c403044288100c0e500d10804010441c104040c03141d800307454039044241035143c454894140c20204804030410820124080d01c041c000103004005005001d41e55082a0041c0341ca00909501c0d801c8180910b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 170341241 1250 170339991 170339993
    0x80619050412140c0a05071d01030515070c12020c0a0918060b0114070303060905010509040209041b151715010c110105130815091f050408091504080705030109 70
    0x1d140500082c1d4036140c1094200c81c0981ca080aa218480400340c1a11035180541c080001c0080c021041d41c001000b9403030600740308403055450349420b0000070f105400200034240d0580d0914200c80c1d1100d503915102822541070340b00c01300b0101d41010300c00011b82110325030000c0d6080403036241d40140440320003044060310081c1400d00c0341c81d000030300400207500e40c1111842c9a100da0000c030001040410402e0350b440007482d0290042450744503008030203040078000545c502c0c0540103180b2440d00035200d83c0035036440c0e0340e500000944480c036103d03ca00000c4400714402071a824210491070303164440500c0c00e1200c58007244400c070010441400b10509003040c111381c4c3d078080411103000741c5c0880b41a6060f041c66005031090b00411075012070040100d1000502400b00140124281c40c039055544c1c030700e4031113403400c0c1d40b01c0840c081503a0501c20081070064516200c1e41c48140d2190140058504000c000000202080a6011a42c4d0240700202d01400841c0c0c4c00c1c03005500800d0118002c000c0509a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 170342491 1250 170341241 170341253
    0x5030105030a0b0a02070b0106051b150f040c0b16020a050d080702060304061e020a0f09030b2815030b0c0a020a030e1201141b280215010806190504 65
    0x103414000c10040f00a4040b4503241c5203901680c41d003650151110f8007540c1c45000c02000e582042e800c115071018901c2141703401c001e020815100552801c441040c096441201c0c9443c14400600201c494450490740002c1642070180502006080d40c003408006546a0040018156594101c01e00c20713010407220500040c1000202c490017541a102c40c0d4680c1d50740c1c05c04500400c040305004071041c2100700003002c410429401041094079540300d440803042c070341100703c80c074841030301000f06001e1802010038181c09030350401d60201119490015800900050a2403e883c0d001440750007401c0c86402c24001c00403000348403644000f03154511410b283c1c0c5030074004c0d5201a118405000e2003070300c003030124490726000c008686032000300d0028012561222803020001100700d660718415804541c41c3c0790314072205412113000f5103502d514650003d11040204008000c04c148850540c8291100e0031f08500b00d0004031402440d051002e0031203032601e801c1080441d084400e441a82d14038107010040000c03e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 170343741 1250 170342491 170342503
    0x3120a1505030304080a230607050405040e0118060f020f0f12090a0506070f2a060b040204030302030d0e070e011712090d060b0a080102040306020405030c0f010801090203041112030c0d0503010503 86
    0x14105540c450324120210005015a9a95481c401c43e80218020480084c0d04000203000b0cc0f04192030400500c0301c02c040032400c0710403410320074010018100544001c1030050b0000b404113220b45078014034088988045036165880702101d0f00c0102c8021510320780d419500d01c8103c3e845081c5030090035481115075103042c3c55090080191051003212103064040e28410f0f003c0b24000d901020740d00b038070301400601022003080d0b030311412142a4209510352289042c64000e640840f941500218108801e0208100142880d21a4001c0621038607000041e0340444140d001c3c001c01f000e0650918020090490038180009402240d542c02003c00c10801103403a006020488030343c00050000e5001070744030000f036040c2e61582c400c515640c008140841800b01035070003401142d00403021210030300700090500c40c00c0000f0f640400c0c0070901c2500104a0b0001c543c00540e80310380310390400000e00f0035410020f5840c110860f000501384c0e0011031a240c00010410402d05a40e850b404c03c107082d585001c00103907541c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 170344991 1250 170343741 170343743
    0x10602060a020f0405040618150605070201082e06120924110f0c011b020a1e0818030114040506060d080c03040905040b071e0e0303120a1505030304080a 67
    0x5500180ea60f48010180701030310043c0a00500501c4600e60762402d2a54021400340c6c0805003c6c64049190900c6148440390822155203449090411560f90010340c4ea4810082082c250300c4d509070790100740c1d512100401d03042e420003001d0080da083d04081005148110341110210032a1074420b984002c0342c89450351114011004120180d549010740b0341201a1084100d0307806514004552400e03c4008040504a09a03131a002007102030341200854a41d140c585d0700701c1005d070b000100324801054140c0f554a003136880c2c0403511080c1000e80da6440d40c280d444156094848080114214024034080c010000b91382e2001902944900302794842c117484640c00b070320003482499869584c83c2000620340503180c004a24006030380d02d5076034402510001c0c0070700f11400c5901250300d00006010030b00540040001c000c0c03542071080101105613040d03031b00490658080b54140300a0000041d95801941243e100b00038030400803503220000d038000d040d10a12a080180320313820910044c44540c4000440c01c0c030079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 170346241 1250 170344991 170345011
    0x106050616210306050f010c0f02010f02071706160804030e090604090204060902070308010602060c03130201050d0c02071e14040c090b0a020604030f0302090f0108090313092301060206 81
    0x1045040c985024244010400c1c07110482d80159640d807420780540c40241100c50070350741c61688800e89001180d101a1540c40104040c10450b150809544030780b0000c4028907090040343c02241e10f0744841c28011450910660065014408221035400300703050005445681f8186074104c0d081c580ea000d01a2503407a0b10060280d1341d000d000a000f41e4035608990043c43c0c0203481003041c5c648035010380d0041c2d40070040903404075502c8000082c42d00d20002e041841919110344140c2582c4070f100007150b01a06c481030603410010b0600c1910790420061144150030703000c3d900107001c001c0c0380810713600300e041034405000c15107648000108500013001a00c800342c02d1080f82c000034040d070380460545400409400051554001288a0544a0700062aa406180251a134404155005500714268822201c003250400c80300302202800d94022580c1c1600b0a060005890031322202c000d190480000036400701e4130803600c9500542c4504440c8048500b030445084100c4100d41c1490300296851030090045a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 170347491 1250 170346241 170346277
    0x9040c030506030a0b0703110414150301030b04170f030901090b06030d050d0b0303070f03081e130605250c020f090408120a021312110d0c0512030d060803040e010801060506 76
    0x1000c2c1f013a40403080790f40c01c4e1030185440e60b1311a403242c800c8004203600c0c1d034001e0f000c080130080f444a0a0b004d2341e0403280e00100703c00c2130795612b5036035010001c00010308620020707042c0002208030642c00081c3d84a0410791000044000040c00c0c442010f0a01070052402600300304203100545620008942d034619a039100450700c081820040391079403250000190582d1680c4200c4410503038009803440c003560307111500501d240701c900c03100640c1d40c105480098080c001c000301000003583e25001158005a0060180b500d0b22100c01d0440d04814413043d40b80014900d1055101113240000d08103442e02c1080e111008545459910340d40c06205600c040035140e108100002c954000c7c3d60110350042e40040c010000c00d50382c80d84402c0344444049002c5400f2441e11414804c00d0070441881d0610707540100988a40340c0c6000c0520080d41c07280e10071084640000c0100030510035044c01240010a180385c021582d442c42c2685840d10b807581a0031040459042500801aa030f036102d05445a0301a100c0c40382e21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 170348741 1250 170347491 170347501
    0x40c0806060a090b0c070e0c04080d030c020a060617150c070b09070314060105040b061e181903020102060601090e010e1e070804020a15020a0609021804060209040c030506030a0b 78
    0x10f402450359221640ea5640040c0176465124003052100403140e207051840c44a0322480c50506441c029809010310b258860300401c0e40861103034020071001075442c01070300c00c080c9a0b030700e91000781c2d03e43e07030044a16202c1644030a600300e04100300d00d040a6140e40c0c40b40a1509040a1015140c414038402a004044050104030b41c0401403104c40029035104170b01c501410002941d050f11503400748240c2e80314600d410030704002030804c01c044403840000c001508009401c08100708005800071000c80b812040700c14070701c1300d040d2130b401100f080100781c0b0040001a2407551000a180502c0208101d0402015080c100b29003294500c100c0c2c1075400d07580e5110403503600d031901c3c0c00380040c00140041042c9150024441c83c503400c5018640501c0c02504c110b400303d0388482c4008040d00d505100f1900503070008601002040c5c0e25444094168802000c000d00401c1500c000509004203482c01d640d001d030b00081219a41c0340510807460a40001c0c2414009440d011001030703140c1c02c01440c040d00d2040c1a00c0050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 170349991 1250 170348741 170348747
    0x30703020f1801080f040206120714130504060501091a0309010906050403030e0f1209010e0d060905100b0f01090323011e1a090c07030203070602030403050304060b040c0806060a 78
    0x180700c000c400a040d600c5204a101e180b000480c8090001d01190503440842e40112104200ca4841d50700901020718200308080e03042510703070700249808100030090300c00e00f0078201d4010081c040c40c000e802e40710001c0340c18139082004442c05940586c0c140b00e0800c800b04000804441200f0540c848050099226076503081c41501600d00054014408c40c80c0c40200020590903500524180c0c0d951401c842010359103040d11541c41070000400e2001d402d041c06031844a41c803074403801901c0800a07288048116440c2d5a1405813005500110b40d0394106c800389030190031442c4079800c102042203440043c9200e00c100040c01115480c00003030710604000d41c02d07a4554512500d01440c41364148020018001810748101c40c1e01410100c0640e0789051105802e41741d41d1281001c01103c00040c440c0c0d18540710b000b503100c1181d02c005811001e6010600494000c100326201449c4118043d80b103150742e0785410b242003c1200c0254202e40c2c803a074982210030a0315688400c4165000406942c2d059503038071340f2030040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 170351241 1250 170349991 170349997
    0xa05010c050a0f061415010e0f0102030d0f020a0212070209040f030509031501080c0a0302100c140102130f0e090601060305060f1e120706020a0204090602091e12070b040b03070302 79
    0x14044802c0c444043d0200280b42d8000c545050720703a900f0f241c040d1580b91982000090841ca602d00051010303208056070b15000121001c00c41c0140102c902d02032003096000c0a44001541c92889654042000b03080a0740511504036502e551030540c500d00541c903070000303407050710103040980100003611401c002c25018104031540203100a080b02d03051a8010381551013074009015509150041002071441d90500a2680c010781e03500800e000030441c14254111546114414103036401c01000050b0700e0404405e2008280c4100c82c0d00b0000200341c180320340514140740d268071180c034001503901004800b800100307019041d0340c520310380031030182c484100084002150000d02540520700030881c110420b90000340c039400301002e0394403aa02038002c1440688441036031041c000584c104428040062516501c556011031040c400103083c1046c00000c01d000030690b9403d41101c24551202c500c0034a008041203903e4a2204014401c0ba4280300403428107008a206290104030007001260b800c81c021780603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 170352491 1250 170351241 170351243
    0x801150306080a0b0105030d090305120a050f070b100b19030b040e01060e0a05010905070f03090201020a060c0507020103270f02121f060911220503061303090e060a05010c050a 77
    0xc030b0f00030700040d04020401590a1180034800d1094003050144035004140c6e050880380c1181c0500005408940d50021681c4240d00c04020010308006003149030281a014080c12800f42103182d10310300d0314200c2002000075580040201c21001e1002105003880380340115880140b514010074a0195007002c20040e0509a01030342c015420544007080825005100c3c0d4030a80c0310a806004d42d0341c0c0c642c054001ca0700c2c1a20100c4c0001e6142016080c3e060098003c074401610601c102d0726035040a458901c106c8084a1ba0b4100042000030748005560381801070500500030303003c11003d21561070f648a030501004030002400c4094458143e03055655030302d01c1800c0400101c00342e44080408064004000e4010040880b02034035013140440e088600e8411403164040144d0344515100c0c648089400c02161042c2401282c0c0d56400041141c2d142031155901a15000400f1000c20f0740c0c80c54040c8c0003408903041511003c0c1050b00700045a03851207821000c0b10020700b0103025900e29030a0450034081a010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 170353741 1250 170352491 170352493
    0xf06030705090a0518041b0b04120b0f10060e041d010912030504050628060e180604050d0804050f010203011503110a09140120010b0f01050307080115030608 69
    0x8000308590818014006800304461840309152100c08114100103039884692a82e156100050001403013000106940418103120302d4005950312068942a8020303046124104c0e01c101c0408200003242420b40d400c60705403003403645d95240c80c1640122108152143c4403c000040d5003003500c40e1101c3e805924600015070901030240c0ca01d9407524080c0c00005c0c0201d40312210b806448403203030b11070300c00d03d40101e41c060090081030701d502032151059200182d50910540b200091354070040054861140201040540c401461500040c8060ba408003081c80310b455401503000c00c000110040380c0030040d0441d9080c202951703100c5040140c54500710300100c020390342c40000040740120814150381c500308203580d000e00021120500020b001d000f0002a04040768080382c0603ca00700c40310002885c09141072600c0005180f01880341d40301d514010000388980d035500c1d1603d542604189007031032460140be003081c61450506000042440005114404051807080c4004020b1440b0b0b4000100511841e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 170354991 1250 170353741 170353747
    0xe151f090c080105030607050a0305041713050118050d060f14071106070f020d0c0203190308060a09020301180f06030c08010e060a0e070e190e030408010b04180f020f06 74
    0x2000010468401c2010100340c050000080610300050f0441c0b003034606540f80c0742800881581540600406003040741d10040b52441c1c200c20416410151001684003a8005050380c40c110014185800801500301d102042d0082840640c503290384034585554803180000f01e42e0480d6041200404003030031011a84041d040520500650120803800f0315031808040c0e8503036850303104098510301c2c1c5c1d07001000e0241e0803e000c1c580c92a0702a000d0284c0803400602510b401000100a468000384400c604802048451081c040c07582020500c00001c2c10303414000314515414010103180c0496080b4644005039154110540382841d1a00310000950340310b008540e4054a644103203020b0503910002241920407280000d520380414006c0004201c0c1ea800506282400c1589000541d64010481640d2241c0b000c5840141d000078401c410f107091511000c0c1d0388681c245440306088d0340b202c03010a1301c15410008020b554540c40d1060b01511a445907202c51840e50034030104c0d64800321480f03d694046404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 170356241 1250 170354991 170354999
    0x4030c0f08100501030308071809060f03030201060503010203040b0c070c09020301140906040504020f12030c0708010903020706050f25061103090d1106010e070507080d020403020a090e151f 83
    0x100340e80c030094502840541e845030588003540001c480d403d10015001458100204038698003420208224442c40d40d4180030480c1c80d0000030059900c69800744021ba14101c2003001896420300c0b46101500c4201c00945c0f841c20319403681c42045002074080004424000f61a4041000344841c0700d00500200b60306540300d607034468502d0080265610b18a00480b11030340014443e14051040724460307030380288181100052407041c07000b100302000b4619503c0c0b108220b41b213115001000120014864400003040c40c0038185402418103990f0303030015003807201c1440200000d20f002030031394060340c22043e0940000505c440b070340c01485c5407604014003018600003030000800360360401540300c0c0c0b942c0d2040325000344024400302e840784c221000901c081d80007600140111680c02c90059001050343c5800303414040c07262101c605c0c542c000050002c40b1359001034100704600700f60701c49030020a8144005c20042000d813200580f1018501c070040e01205041c00050804118040120b081f0708990910504071619 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 170357491 1250 170356241 170356259
    0x3060d0611041802160311010f0513030f11060106050a031b08010f051503041203234c09090b0105030111090102031b0a0b092505010e09060604030c 65
    0x10a00808009450700001210850004e008403040688424104040e0b0540741d00e00325031a810f45c0140b540745540f00e02017080508803d000b4a805030503410644105241c4c40e01d0083c1c00294140c0149003030121080080403480c1c00801e12604448080c1485076a031503c4210450003021030400c01c2d6000020030346100036240d480b002c0700781611240b10f090088551500200304080c04d001c0c01d100000001080001c000072807141000d4019641b908001c100c181307804c00700b0b00b0712000225180308910003550401c8039001c01075a548003038000750380d50b0090392800d0342000c500c3d003003c0102290301c0780074004020b21241615007003400203000910b01003000d140945400e50f04074400303200d01442582040c80d03000e6120340c1c00082710a1814140c00541c5803542020900c00d4031400d04c01100d07202d0080041103408a0940200f07a0303c05e4207031002502a011300308110f0400300b60b00160b030044c0a0403218007480103980107041c0d41d030b50203400c888a00c090b6a510000a00360b20a60304020302d49000034000141d5064 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 170358741 1250 170357491 170357497
    0x2090a050f0616060608030301031a070309080304030f0e030d05040513061413020c0d0801050907080405070b1e1629070503060d0c080f0f01020408060c03060d0611 72
    0x1508442516006666004001060101c0404507501150410410424481010000c08500c0c130401e40400c0c4030f41c0c0c50400034210340007644243c0300c010a000403010f6403428000c02540c40f0a650804200c00d451070340340c100d1280002040207080c04840c68403044070500480d121200408000c08640c0200c01d0403070010a5500644100b9014020300c95040c81030050700d02541d011741d155002408401c0744918204904440c07582403c000081d820828110814801d02200b02d966240d9102c910700340d49020103102e00742a00034204d4080014000500000490106001c002c035416003841a40320401d020401685c524280c3c0d486007441030019000c00301d20141d8101600b250f018112400d40162501000d180c0d40b04035106040d0650b0f201000030b81100d000d1400f0350b4103c0406854081c1d1030074140c2d02e480c1020126007041c070080c1e0207195107191a100801614101c943e1000083d0704040c44d000e0107568441001d000210100c4010000a03141e4a0350340b003102d03231a03800031014040d00c0118601c4140c154 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 170359991 1250 170358741 170358757
    0x50c0d060b0f0d02071401090803010f050301140604020a1815020114070e04110906070507090c020c010e040c051309021801051c1a031b0415051f200102 67
    0x1034280030300098840354810a603150780404a5015180490381c031101d6009600012044a501c0b0990f40c1d0108400400d200d0724001900c00c0411955075414102c00c60282c50035980507034820f81c1042480d101c061010307c002ca4200030281c9016841c1d0844402c181d486000c80803c0d450307545520701c80003560705030aa0700302d0229a030540003040343c0ca141c005546112003040711010f012825007442c041d000e0034654044a101c1c0d00da00d80442c20001340600107091644602000c0d14a50b00102003845001c80520640290860500041540350501800a4102d03040d00c00c036a88502d64030003103801d0440c0100201ca800b0780010b405c4030340e041c4e101e105100c001c0d0015640340310704041d8070be140c22103540250110b0300800d001c0c540b070000e821140041400030b040311240e1000707100d140300304070b9000303071420441d4075090b0409800c0400043d81d41e0b800d0004442d010103500c0744d00d04c0e01e00c0c02040300d900c4030a1421460320310032140c1110392220050503a102c42e401c100c00c1c80740f69200c0980141d00003041d40640410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 170361241 1250 170359991 170360017
    0x709020a0806130504052112040602070b060109050d0209060f0402030f0403030c1b11030f01020d0911090408030c0c0a0506130b060a030305030112060603080c0c0a0b03040302060c09010210050c 85
    0x451144000300c210b600495000f0702c1070748047c041c0481d9030000c03a4501150741a03c804945400000e408040c071201013610708988107030300442c4441c10414400b00150340400c0a03e401c011a500c0c003400140d80404108000e0701038145100440c5064581c0003200d403101358040c20556403401d103103035805a0000c00300c2c0c05800282c0b401080782245403040205007510103240d0040416454141c444610389080c46042c141d0511070210800f481d46400e0000c0c0244105003039000a0110503820001480400780d5a0244100311100406c00042c290b00d060f240c200c90030030b20054481e88501da003d45403a0700160003401d00d02c2104200050f110644405111840c4215951405610360300144441c207415400001c01160050006100d00b43c039000017035890354013450300880c203035950f43c0312041c01e98018020789100e500500100c12460400202e1200100303041000c461441c0340540b002501d40030302501003204d007200019007003c41e0303100b0040c107020382008002c00c00a80c00c0c0541c01661540c4204400303404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 170362491 1250 170361241 170361259
    0x20304080912010203043f0201150e10030b070212040305010b040b03031206010f121406040b0a0b070807060615020d110a1e02030a080c01090c0b0301260709020a0806 73
    0x30702001030090b17900840c1d00010707072603001c210151030880104500342c0400881400b01c01d0500507032034a0140140841540d000080d10b0b42140f1960011303408260080c4000c90384030401d100c51504083c1c1d900d0212078214407946215200d010049081c2070486a52103440c2c0d03000300e00401401019440300440b54022541009095010005d26407280181144220400004000540b0b654010700301301b407200c11580341c068225400101007104907500840044190440381c0100070583c10140b1481441500031201951101e107047d010740d02501c640c400c0100360182c0031442d00c00704070303a0f90011005861002c02809500300000f1000f55502c404820540c001514404212595a804180b4080b01030304424900c1010b0300da01082a82407003a403400326010300c6076004030300c0490301e13000150400070928000443c07011030ba410400843c0f59160481c0580d440200010000c1450005181c0d8030702d80c40361074000941003400300c5142803e10b03d45c802190039000241e050b01866104004904c078610494010307030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 170363741 1250 170362491 170362519
    0xa050c0405010e010b090d030905060a02010911090622020d020409090314030c0f031e18060702030a1d0111120a09080a0c060c150615080708160e060c010203040809 72
    0xf074168203216090304003a00b0400031469040c41c0c5280800035006c2e0a04540a03550b500c0490200e41c011940400180d41d034281000401100f84d80c84d0b43c2c03072a03003112214460304090001036926258602207060f200b444088054200e9415010356103004030000307003151110765034400100500304000046001940300e1800103aa2000310702924091040780070340c1410400d100c09600000d6001410110000c131508003041442404409900d10840207034100000c810418038496180080c080c0c041029034009000c41200d20303a02c04401194845c818014543d8150200e0040c0c40300d11154200a4150007055402e410086080005181b165035903030354a003109585040b55500c1e1104d001c1c00a0030100101420800c0074852150002441d000d0a001e0300400507650028045610b030394061048090403035403004c001a0040162075112080b0300340300c0314a103814024064500003091150040c0001b8441089a40e19a50151110119404000c564904081c1407050941d00070940f00b0303101d4614140400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 170364991 1250 170363741 170363759
    0x80105090d050409090c0b160314120402210105040c05011d0607080f040b0c100b03011a13090c0f051f02070302130f020a0c0203010b0a05010203071b080a050c040501 73
    0x401d19241c5552200d00742814403107030740040d110015090390328005c20600800c05041d018001d18102c00910724010034000b0303515001d0b0034032a0803000c403c81c040040c403102d03d4180300c81c0101c0c1c3e4051790484552454000c18450a24031a01c000c440950561900f410041007150041c0b0010903502c0c00d8880841400d0b081241c48800c8080680843c0c10810500c05603002900940281902541501459041036100c12103030300380b900402400441540001441500c912071480b178581103500c20b034028030014841c44041c038402440e42401c0c9005511011400209080941c844091f0541c06614008a2942c4517441983c00100d030160710720803e0070000121010240c00d8804540301b000d9009040001d2864080100100918501d0400740381c0740c440304100918248000d202549698440d01c40907a802d0050600319207221482d58021000640c0501440c2c0e00082650000c40c1d218030b8882049542030a2046801610b038081c1d8458803c0074205000c200340841e1a9883d4081600d04114503030341c1c2c071080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 170366241 1250 170364991 170365003
    0x5010506040503032d0705060a270f03110318030601170d0c02010215011203030516020705090a0605040603080715050c0d0e010b270c0a080708040f0f0303050108010509 74
    0xb56034184d1080003850301d0b280044086038484900f0452400f007070920581c0c0c8802582c0442401c0300c0c0c81c0c010b0402c12005420501c182003030720552201c0c0b05c42e2101d03028082e2906104800d40070b8418520000e44008044c412035543c8010304103d03003902d4580504560310f0320340ca254403030705034403a004900002ca5500e0b415103100c1140b07079002d0b009082100c05094203a40310181040e09038114056164000d900c00c81d00041103008080301183d84c88001c1ca28100201140c0010300780c1c1240b4160030440d40f02069000a00000359081120b1501c0301c1d85841c800d00f4000c0c0f0141d80181d400c02c1c10440000309018404001c0d03e030450054070100c518010500d6403d040318000c0701d201c0c1c00480d0038058030303212003959403001101a506000026001100307038005000b000410341450505c2c60041c14400500c035260900075000308030021200c1c10280301c0c580151040c0c0380144914201f2042100103024000c40b071030103250482d080300c0c0311100c42c4024200140986000d0141c40314644c20300c408680565800209 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 170367491 1250 170366241 170366249
    0x420130e070f1d030109140f0109320106080a021003060806011202060715020c0f0a15050405030403122609060403050d060506030903040f06050a050904110f0313060501050604 77
    0x41840c0b1030744411098403400030380010700542c000900c0c0f680005807000d1150300689800780d40c403150300b10056000b1516010003002c1e0001070303904003140000000c080001c04814a90680008040d0003032108950f88080303074240307144241d903090500c0080c01e00740102e00000003500aa072040450303125500103030151500c511980c41180d00c4a0700402034640c8100000c0c0702e1620040c0710f80c3c40e02c817041d21403140f08002d8070384280c5016030008030035240307000411600c030482d628080600355001c040d4940d898148804075541624680310b0f00050304000c0c0501c101d8014592052407c24110707042caa0080c080301d41d41d5110414481001340381d04000b15058012480b650010f0014021650303155022900b9421904400c503007903844103004204c66480b80061803180306c00d803000b5501d4901d13056801542c2d00241e40100144001006040c0500d9484011550030200640d00800e40314a01c1101c01e880d44a0460070908110001c401e1002d060340d01001044001e00451044c4000e90300d4004001081c4500c2c46 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 170368741 1250 170367491 170367497
    0x3090a091a0a120308040609050a0b10050a0e16030603050f060103060605090c091e1002150c0415110c0402070615051c03030b0307080a0305031906140f0420130e07 72
    0x10380f4000034070071500950712600c06e40c004101555199103043c0380c1490340368119440503200040007804940140c0160041401b21415084140f520108511102c0702601c110034400c41c3d81451081c01d8026009900155401002c64007840214030301541c0700c00080c042140c41070b08205d0001151710344502c2c121b01607001ca0103441e240c0304240c0e0400c2003055030303440c980c544802c0080700c10805942d0403004041803c600e402409601c0c0202203d4401980000e2501c1e0190000707100c140032004241c0c11011004a281c01d03d204841c0260b50b40e40d05d8515a0300d15268054000182103080204941103881c10b9116a881100159140c070304200c11124800c0d0003646280c2550756000c0801d1103500304910300040501a01c01507500c8182103800e26084d840e003074003c100004284404541c102e1036002260303c8540040000d94180f00c8030407410b50346441e00500c0792002c0a480c9a040d901ca9014280740729032000c080c09410b034031910300b02060b040350f0008a004c107640c60b40012030203c2120080d10910750b0355 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 170369991 1250 170368741 170368769
    0x100e0a110609040902040507050d0b0a0303020606010c05100c11010c02070305030307120b03100921140c01240501020c09040b01030b070c1a011703090d08090303090a091a0a 76
    0x501c85150440b441107580b0548510100340962030700d1044034003a800030b0355820b58a0610210841c2a00c0d040c01d18a800341c0d0000c0c0c410030100c0c0d8040b9000750460350902c0e00c003842000908109140100982105140500d0019003e012a401c41c050710b0313901ca602d0000380107603445400240e03250101e51001070000d400c1000045c2101e440380340c082414003210500000c0c500c1010001c0f0340380c03031550b2441d0500c0583d500e2500080c44258900200101c0c100030b841100450401d10040c4000394021115401003400301d503282c41180c0c207402251a481c490161011655200414143ca80b41284a20350150080340724a030000c0c145407030154445e0340c0000c5010010b0340780d5a0340f5018010020560000c10050101600001b41c045542c1c180000c0340141d00d002070350601c80b01d04491502c0255a010b540d1082040c4c012a481e030b41d808403203c54218440e291103a14010200b810b41c444c410420358041d0311090040381c15035184d400101c58040041010700281e45503428009071620502419132030060751 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 170371241 1250 170369991 170370023
    0xe0610021b01030c1107080303010504051303020319030b03150f0c040e0412030b060d0203190203061c0c081009060605030703080409050c0906040806070e150a0c0c0512100e0a 77
    0x2900702c3d04c008040c40c43d02d100110074600b80b80381081c440390003034001074200000410441c5070500030b55801c030364010010301286500703a80180d642d10500c00c0d03110343e000c0102c41030190319019034004c2c070800c0e0024096822070f510403081d07041e08000454030b41e0b804c01c52140c0803800c5410102c0c16202076985c1200b2a021035192900c1c0c060072441413024030006c02d0303107503512080591079031409001c00394440c9102613100d04000941d0b03009140003600d4001d9031441401040190b50b9200c05280301510b0410081c1d240100c14241080310a00300d401c600c5403407050040409607a03c1640c00529603d010314030802010b0780b80d4041540318440c62001a003c1c0005110500c03081800b03900087c2c008a101d030030b0170b00c7d082490300030502a400641c030200c0250420410800e800307400c0b03e00701400c010204c40300b800b030300401c02d4051014041d245140c0104610403407514104503514a07000d003c0c04000740840c3c45809103c4035160f0b500010103407800054104003100c50ba001001072125103a0340d004200b0072501c490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 170372491 1250 170371241 170371247
    0x150f180f0206040915060e060717031807320a1505090d03120c030507120b0a0306050933240d03030609110708090f060d060e0610021b01 60
    0x544000e07070b8480801c100000e0010040c1c425080c0c1c03240d102030a1803811340b5010f005021120b00311482030148400700410b100091441c0b481e007048140c0b45880a440361201c0c03101c103010341048128103915200f0844040385c0865110803040403402d082903c042400381c9600c00144002081d41c11329001454150306008074410f101c10326065618625241e800c1101003400210a074591503c10340100744071414000ba68041c44c021203c455529040900043c20070180041c110100039207950401507442422480941e21014076200954000301d0601041c140a0f17503140e00c401d03032100f07921200c00c00d03201c20000c40c3e04c180894500d0b0300001d000000a035598401c2002c50b9030360041e007848000034030800324030441d9078003121b20002500a550020b01a4200032142c0102d0700c1d0000a40400c0c1c400b4011000041d403120704131005000c0c04d6903800c6010701c03c04086060350180b140c1000f440c60400d10042684240c070294140701e00c03400c54480110b6000210240c0c3c40390040c2c0f010311030b01c01e0480850030035540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 170373741 1250 170372491 170372513
    0x915020903030d0612031e0207060f0c0c091b111506010903081308010b030c0f040207020604030212010e010507050913050403090b070501060503010e0c011205041707150f18 76
    0x3001506691900640c03080d500100e511a0b048880e1004d10107900302d0034540c0c40800d458800701044800d10f800c404401000c2d55804480c4075110030020241024001a8890256002c01c0346e4040c0c4c40f4600962948520b001400801a00300b0403800b001622807400740c1300d0040b00301d1403904980940040803000c110b07517a1200008041c5414005800000400140e42c04c005000320344181002c004850300300380714103003518001c8003402e02c01d074020702c20002e440c1d07a071894014080e0000c9500681c1d40e2440d01c0824010b004584c0083c1d80101800f940801008064015244a0350804003c00032035498403010769842c0150400c0075081400805038640b206100e0b0f0080b03401c18020309100300000e960b051003403215844807100b05c5507a51100020070503410f0174016850584450b1011741071380c1442c40e0000b840100070312201500c40780c84c2c0c0c002c541405518104017400168008403d03039290010b0a2001c040308030450090841464200c0c1340c00384403040e100321001000003002c0403001c0c11007a165034860003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 170374991 1250 170373741 170373757
    0x10030209031504050105060a050306160c050c030d0203072904061a040203100617010501021f0906020d0506100804021c030e090708011e0b030106081f0e060a09091502 73
    0x1101d200d60546a200c0b07000012489113104000202d01c0745030002c02c1c001a10b4042d0701950113540142c06008864000003441c1c4003420880c504040c04200034280b00d4945081d06529030303050b007d440c40b000807196010006144070f40c0101f8600403501e10b204445a07130307100c00700c1130307400c294440401050008819811039100346420050318a07904443c08000750890b4410341c1c8094184101d92030800085400240207541c03001c4c540c080ba14250316010000c0c2d1a1841c0107803080704a242c0000c0c2302c040c02683c0d0300c00c00b0a42d401c48802c5456920651804000740300642e80c0750301c100020f0007211403d82c031804aa601c525070151240308810040300030b00c103e4082c07001e800c50074440032620303c08a40c0c40340c070328030b6208501c241d848501c3e81d490091146024028480d48600508641906009030089807003141d04607549894255003641c0c40c1d003400c566059800c0c00e080f01101c0c04c0d01000803030300c201500d814029602100d6a146288e56044074004075a600080101240040c1120302c1001103583d0281101f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 170376241 1250 170374991 170374993
    0x2040c030e0111040f0b030103051002131a07140303071d0f0402130504060e0f010317091002010e1c0e0f0604050901080303070813032124090b0307051003020903 71
    0x401d8655800350035600101c03100c1c400ea00700030800300103100c0b01e280500020510300c078680e0310b19411501c8403a22400440001d891803500069010070208614008078000d00141005c2422801040c84506080d0712641e0140c0b03149942d642600206000807045034040c0c9041d03142c21590303e44c010340c10072071002c01d140c1c0180e100c140c008000d041c9849500040c0801c84030550151200e07400c14040008075030143c1c0012004540034010017541003601008103041d280c00109850249650180c4080de6203e840300080d000b55100003120704c7e468054000e1550290300364203986420360031000203064407640f11000400280740500e00b0b089814804100003014401925003854144c54601050031041c003a400019140d2000081022a55006e08182e42080102014a10450464900400b02c1039080c2c400182861303c1484030380340d10302640c407c03003050280081100c030100000000c1c110140d454030541035002e081c040c41070910f2501280600541340f000b0000e8101c0c050a542c12002074010110039501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 170377491 1250 170376241 170376251
    0xa0608160203130f030506010806040f1502070f0510110c100e071a0403050606060702090f15191a0f1210050319061515030906180c0f0803090603010302040c03 70
    0x22031003c1a40c204090039040500190840ca1440c00b645040300592060308542c001d4400d000000b0900745030300c0002500305840c542c012102441030002841098030050001c04c14440302c608001010074000700c002210b030700803c0040961040104148200d84200190350040c002e0740700e060b40981c1c80400713003070341080c21204429161710003211441c159081c500c8180f10701103010020030000b00290759101c02d00b40d48040c1082d81540c042851403c0192003990300852080014160f016201100320740804001d04030507000040001c101d01c074051314056040310a000c0c4800800e20071804003101c0035032414200d02441c0105082d000c0703012000c05081210006035880700041c69940c2000780c401c149075841003a0b42003a0b110300c3c280c411118a400050115812004208600b41e0070f8003400702e107002507040200d112102c03032a062005000f00c0c244a4522010500c100c8180a41080c50605840e4290315100030703e51240c1d1302a58901800ca01e40303510043c10001440107040540108140018609002c14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 170378741 1250 170377491 170377507
    0xc010e0609120c100302030f09010207120302032a0901090828050f03030c031005010e0d15150e0601030c020a0f02010c060905010e060601020118020310050411091807050a0608160203 80
    0x1140710070148580000070b40100900c8500c000e1231410f01c0d0051034410003103140c107000d90764500c3c08941c091540024980c1c0800040c42e00d6580d00c1d0b40c002e2454203201400c6080301ea445080c01e030390f000850107600060700c10b03001007200b0800003400244903420500701208041300405c04a43c034003201c5002c40b03d9004800c8040700c00742081001d18040c800710000180c50345041d61003000795101990056042040300052403049407604030741c1c842915080790380700d00110000603c61018102404aa088480e008900041e040b14201d110710b008a02c266000d000104103c9003c03030f51003031a01d9000d8500c41001c810540107600600c42c1d040c0f268440c400c082240005500c8007400c44842c2e0110200e640c12503403c101082d03a080c071034107181d1400c0008040400c221500841e945118981c0700f10005a507400100d02400030045001c280d902c4010200c09031880e00100014041443c1c2041080e28400d2724004074203460100070900666000d607031214965030704c0a0911103030000124440055000401c8049 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 170379991 1250 170378741 170378749
    0x24061e020c0612090c011b1403041503060302030601090e07060518090708090607021b040506061902031c0c050906090f12030c3a11070303110c010e0609120c 69
    0x10745218034100d8442203142145540c1d04181c5c031000e01a04102160030003002e82c06001d000c031001a40c01c00100c02c03125000d406154038501c45d64006da810301802d100e03c1000075074142c10013025240709605542e01d603680d50344203c0965040902c021515002158240701d2280310384090800700444084084c0d87e2094030002c01d030100400c0c7c4840300050716500801401000422000f9003010300c0f8401440a14201000d402c5d80e009000c40841c400d5864101184440c2d44207002d0f10368541425481350400139600002079660750008c400c0600c02450325841600604030b0344604480a00310340c0b0395901d04800c2404101d013a501c50501e03940d00c1308050741c100d0460344038140c3c01400104144015a5a01c0106542ea4a4012041203032062150095442001646501d65000d4060020356900180d03003403030042559103250030442e0021901ca40600041419848000540c0b0510414140c81c03030351036440011107503140f00500c030582104041200300a2810901581c070456280c0005a0b1450540d0130009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 170381241 1250 170379991 170379997
    0x40f0b03072105010501170403050d0c050f12090609030702010e010507031205280501080a0f03090801020c0703060606030b01021f060905090d030b010c1e110d0624061e020c06 77
    0x102c1c00350756480c1c0051040d541c100782072a2606243c524544410300d807580c2c1c01080e07807140643c02d00509803119a42c648050081d03054460081c00c1e250fa154990102d511070410490040301d00300d49500c9001c0c00315901300c002108a9070020b40680d207040001584c600155103a500680040b020003001048500b0b4000c968450304d4000c6620140c1c1c0340c6120320007020300801240c2140100071003403402d00100250500050f0240d081030780601c40508052036800c05640211655001400079400004c4142481c480815681300b5244190010404c00d034441c1412802c6586444000c0d005d41d003c1c00c20304031510099081d0a120f10b1410b040860740b180c4881e000010b8403415a103e40b00d5902840c8a401e203e60580118212a0028130f070540002036182c0f1507031a100303041c035429162804d10811a4060092280440b07485100142186c83e05c00c0711890321500604a003201c0300606035080442241004002d44013008503400d640d200446900042c1c03500d1500c00c0d10006580c1544643c181d212050348031344010b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 170382491 1250 170381241 170381297
    0x60207140d0f1a070905090a090f1a040b1303021015180204050909010504080406110a02090f0402190501050a121503150e0304030f0308060102010e0601080a140102040f0b0307 77
    0x1d0000d40c103c0c10180038052001d0841018040021070a01950b151038403810383c010260400801d03180c52600745a1f4400980080c0503000403907030040c62440300c0000d484d950041c1c0c070442001c0b000c0c3e40c502142c440031004000c2d00900507089020074841185058114407a0140c20405200b08941c3ea42500b0001c1400140080d140e550049020800e80c50640c00c4954403c00c4007000340040c3c41c1076581e10805204500804080c865404100300c00c9071820024120342c9540039052081900784501c04110480040f0380c1280310304424a02498403040c1640c05904840041e10b62900b007100803c0c0c01d07581401002d20b450201640c0301c0342ea03d10200584448001140241049002c5000300181c100581d10020205001e59004010400010b0310800c1c1c01c041958143c500020780d41c40e0000102d0140076a00c80782e0190707128440001c102c164012407112001481100a0700703906110785840c9080c1d008900c10b41f90304544030719041200045032002541d0000c064074140c0b841441704e551042e0f0780c0030b56030700d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 170383741 1250 170382491 170382503
    0x1060906020c060c120a0908031611041a010c02011404150f0306060509010c020f03060a0203090c180c0304080d0501120b1302130209030f0a060b01090b0301060207140d0f 75
    0x41000a40500016003a01c80c01d03100545071200d1070413100c0c0c3c0c512100c0c104070b101a80001d40c0c80340d400c0c480d1000c44058090780041c0c4c0c1da210b441d902c6079005401080380a40b10000c0a400540382c61400f4450042103007080c1e07525030104460340b4010f44100d810b03c24140c0c140040c8011250010b11108020030251182c120708814100500c035004011000c001d00220900d45000340c18000940c01c502660803001091a100485000500c00b2403e0380c1108814260075200c0d440c144084e0b905c2c1c50f00914824003c000440744400301000800444058140881c0071034030881d00402c4825559074019944240140f900a00e04040061041c0445400f40d21040d20ba40c030400d26002000130000c606034000072000d40b41c800c41c00d415000100b0205002065005550b03000a034211642ca09010100c1d0030700307980301070b03038440066401e002e0701800303000e22110b002407047c0b0701c040f44c111283e805481c16a00b80d6801011030504041581958001d8492500d40c80980300c812400001c43c1402e0403010349210f46 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 170384991 1250 170383741 170383757
    0x70603320601020f06012d031104052806030314090a050d050a05151b0c03180a0915030b0705070b0a020901030b06190305010906060e01181e06141207081803030106 72
    0xd51812544509442e2041840c514401f01300041110010b034a0004c1c4070841d0001050340300d1240f0300c880340c1c00d510560441d0f1250b002e1884c2c1003030785c06d5018504072402620340515610120100901c2031180e82035850340002c80420034440ca003085401491180d2040c0d080381c140003040e4503001e01c2c0c95041c01102d910f018510007000100c3c18084103403020542e003a6400c50030180c0c00314205889004440356400d02040c02070100c41295209046100201401e80c0100020803490050000100a80c00309490b200c1000000c0340b180c2e40b1520840c1e80c840c2e00080e4401c49511900498400b942c4500003903810103442c1d281e036202c1a5902001002031108010301f82d15501000100a03056410507030100d45114a414001c00002d03400c00300312036101c00e09103801d0200329a50b810b903180201440c3c00c0030401d000c510405100001c05010b8400c1030340c1aa07100e00c03421461060082c200c51040092021044102c040440e14040c0a80b0038140c0001c880c40300300d131496201c42011455600709a110900103900e507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 170386241 1250 170384991 170385029
    0xf0f0c080d030b030109120807020723040b031207021203040b21060d0312020a090923010e04030504030209060301020d0903120b01080c071101140408070603320601020f0601 76
    0x10310400164240590007842100c0f211f4940b00804c0d144205201d09000b010340000d00c04520a112503070107041041d02c4840800c00440300b5000c2c4080b612081c0340100d250600706491880c00103a07084000751107003c1d2070f182135100e60a000fa0014403805086203480140700c04102600d1440280c101072285080140d882050000009000e0f0300150032113014000311120440070036804404420002c804410140c0d43c1d100181048800080d140e2082c0c105d00d24055040d040500340c603050300e07205118200d0f401c0301c517600d0340d4103a40c00b40019100100451410842000181402c4031182e03800400280010b0410350680200415140b0b1148101d00003104068450824850361003031076451a020b11741004e982c035285a04d000d561080040103481c241c0c40201d59016030b0b10481140300502c44401500e92515914114165100e8690082002180c1003c0c440242008584a4802840d0f25040b41445036621300c441c8440c9010003510f014114000c0103440e541044c002c1120a0007814840700d000c0d504105 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 170387491 1250 170386241 170386247
    0x105060108010e04020a06051303020405041103060906190b060403050a061d03070503030c070c080a06021305060f0901140f040e06030c060703092102090103030e010305060307120f0f0c080d 83
    0x507000783e0a020002428030000d0707100c180d40401900c615051090740e0b0790165010030b4500703459030300c0203500902300010002000311140030185601e02c1034048035060344581e2071080c1c95520807a000184175121500ba101c40c1200c5800000d80304034068006440c00d5200e0310740a007000b1501c0c10030f0321416210991803041e9400011803c0405034040d01440c10501c46591b10f0351644006060326404440c0420031005100b00c21070010014086103040ba4a50b46840c0b4054010b500003094070010001c82800024a5040030030480f40c0e04d269101c2c40d070346000310802c01940c0018901210440640c4280020518038506100a10207004040301d807003010b10b00b4208141c5403100c885081400b5000600103880000e820400c03110650342c000260004000031544140300c03052081401030350081010000005040c0c00c030030300c0060100280ea051256550341c900303250342c483c054410201c1c011034050340d00d0b000c0348540481c030b0325252090300c200b03e60f80002e0b10f80188071a00d9030003480d8103401150613000380d03d030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 170388741 1250 170387491 170387507
    0xc01110c010927021902060601030b331605070510050f0705030702031204050f01020a05061602010905012a09080a0305070201020c0907020f0705030703261b01050601 73
    0x820400030940c5520324030009020441500c02c000d440020300030100214240c1d4005a000041c4280b4110340301c3d0400340498045128510f0410090b0044401192481d44240624807000102500456103c40c1060b001450380d0700c01c031101103200c060104582e0303526500000800d0041c0d000c503109042d211780d60405604081041d03200130710030480414803070f50082c1c01006a1f40e402610909543c0c442c00c0c00d0818500b10f00c541e2000070740c18060410b6014142c00307888050803e690041d80d40d9038410441900680e40c4110000b8042d019501c03000000e181c1d08554400351811244030310012907004541c2c0da81509551803405048050b5440d90105c0300b81011040364031720b00400f10726040784902d00d02a4007580760180c3c045c0140030030138001100350959008000c02e4911040140c81040b00e49041c41c40203443d0000b41920310702034018540d0000311890f002070f00c8400c1d25086440408010311480d441607000c0c40003544043c41035414071030100c140041e10210311301140d0000c004503044c07074200001840702c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 170389991 1250 170388741 170388767
    0x140c15060102010623010f0903080d02070b01080619020a091701060306050601140a0507110603040b090c060a120e07030506240a150c0804090204080109170406020604080325020c01 79
    0x34004001c0c1d1140031103c117050310180b82170a2403107484415041c02c8904500c4ca80024055000000300603074450240da00400307465000d000d50075082c0c1d032034041c000c0e2941e500b5112031a030b20466080d48080f00d40c40d036000300b171032128600f804104160381c1c0842804450320040710403826559401d080003030019500540c0d9016809103400403884503241d4050809000c0c16264034108031001c070b42d00c1c081103400d070341e030142c28ad8004109986130714152600024505088990b40042d0042c0300688045003490303401c1d20007616454644800d00d48508403807000901401d10b617412144100f80380080811810300190f4003421078036103603009c00b0b018503214804000120341c1c11030240000c2103041001d059040e4060400320b400c1d241c010740c00d00b502d00b08400c02e8011900420076003440002c0025a801055019000240c844d020030080035510100c000075600543c4519809130300510b0000e07000509103002182d11500c0721000c103100b10396446500c0c0f2441d02d020300b9680560311003010b155903581c1000800b0220 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 170391241 1250 170389991 170390009
    0x1f0b040612260a0c0305090d0f030908010b0604050607060b120d030c0503010b04140d020333040507060c1707060603020909060c0a030b040209061801080c130501140c150601020106 79
    0x10b500d01544001a214180402040050941c2150100761240086030007082004004036800a1136080482c05c1d280c804ca02100400d01458001849000c107009031002d40100800d0581064500000e020240e400030f201240e0241c1e48500ca41680e40c1c6400400c41c510120304010020500b4800d00a41140d03162380031101400014030040111a4101084400384d80e0903400c01c107040040c000100741e019076024ae009601d0b02603110307034005c03074459004040c00c1081110741041d902d84030030380c160012400941d0050a60b4012010500016005505884866200351010004209000e682184681041c1021201e840c0c481e541002503283c010840394005503400301520550900c0100c110341c5214a00c0014180354498140d0310207961180c0c1512031500c03003d010a661451161042032602c020094494045002c1d100850340b030090440a5401b2031716024101d4031000d09040043d2038100f22040c5e00c201c078290801c0100103c0ca4107104040d21201c030380c0c0403298036040c10000642510100d400403204 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 170392491 1250 170391241 170391293
    0x3041703060d230706210b06070f0c03060911040606031505090c04030f0b072709090f020415062606061b030309030423031f0b040612 59
    0xd60b50740c2d0381c8200246035201900701c6003441800c03030100c02c8460706003e00c0d0303280c0030740400051066000b5208400048003298001215001d40502000312010340c0394a0340c00110a1014000107583d0190404040e800b802140d45c1c029075aa03207107003e9034001c181c11208000340014800c0f0b1400d2502032600541a81e040c184000d01c400d0302e004000d0312040c8141881001c1010110b1024401c4100b01c9014540081d00103940550300e0130a02071014044e10751000140c2100e401103801140d1100b802c107a07000e1042440245442c003404100940806075003900c48a038250f4403040141e83d903204141041240d0104029250309d0324102905400c02101d8040c19550151045510020f218155070b03400007089500350303140c29002080012107141c240603a4800e120000501c03024003800400f800440d48404440c100c58500741002e01020030010342d07503036016444072000d640012040c1c0c601c074059601041c00054085054000142904c02c15030000764a1851003001c041480034440c0f865006038a41415800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 170393741 1250 170392491 170392501
    0x7060206161e050d1103100f0605030c13051216090e0a03050c030706052406120114030a1203021e040302090c0f0d0504030915020d0e060a032003041703 67
    0x1031004000d4201020b40484000080d1850094064070315480c281003041185610741c1542166991003541e0503120450300c804006481017900161209442050707a555045403641b4641c002d46421524540e0218030411070041520b8036120b40c03032050301c4e403c2c80c01030800c400303c10b250a030341c01d00da0f810500c1c2031410726040031146a000a01810f4042d0b0501c0c05a507204011822207086004115006001038188403c1c0224450601ea41229070882c002d01c2494400d25201004900e00c1420002c0004808080042008d48402c14805014407005029607422a480c0c0da656054a000d001c1500e0100382e010800864540114075440880d0300345410452400d800d40d00001c1c85200002c15082c118140041d00c00c54207040c46040c3c032103c12041c1028089420b0a14018102c4150342c058080c80340c40c440d010340a5131b40b00040c80f003001201034840e074142d0400c2d801840216032051601d01d0a041d11060714076483d6100003488071190300c0d0280925100d0800d45060048011244101d010000003401402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 170394991 1250 170393741 170393747
    0xc060708030109151a0f04090e0616020a0b010e09030c010e010501081b090f061201050c0405040c0f17090307050615040608030c060703091a07080f01170a0b0702010b090106020706020616 82
    0x140e96192a0320a1b5102c40f9020200c0c050f41c404d98018160217070910301040f29500300000c15038020011031214a4160124607012a81d45e0380410003e001e8012140041200e4080304429a07000704a03441a01c0c0703001c18000b492401c0d28409800c1d48a103a40d9040100b00c80002404080103a0305100850318090280000140780c2023406030180c865104508085030070fa03900e480c000c454060400e070091209240620b580131140d00b0900c03c1601850820001010051240b0211001400b00e0340f246060700a1241103005200c0000f00b40c001b1501c401c0021a010038001c100300c0344110021203e5800401d0b040c000e10061702c0340b90380400c0c40d5074014000740c0c580c07000c041940780d8003d440b03180000e400340d01c90a280525a030540d407142200030038941800304c4141d02074502c0384180078016110b00181d80e6032480c0c9070034260a104005081d00404078400000310b030080a244c100c01c45100128406030309000141c1590f00a030310640240e4040380c0300f00101c0b40c0500c41181c2c45415042603220843c0103140103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 170396241 1250 170394991 170395019
    0xd02070905070c02101809021c050402150d050108070b0703020304170c130c11030a0c020f0a08070611070602010b01091509030c0b0903071a0703110c06070803010915 73
    0x890040d078940e40050103452142103191078031500144034101c3c0030741805028120000020500c0200c1d00c2e141d1010070800d0242c022a0301010b540c450105c00201c00040000003803002910490740881e81896001a281c03441b00500815100c4402c001100e5261004440c51700c010355010800c1d0110900040001c42d40100544007110854400b0391000c0c6480401c45041403000d10305903a0141d0b1138a81101030010540c400d140702c0e641a140c445051380406502a40c900441c44141e000481480e202c0c401401d20070080380c0c0c400030140a0844050711901400d00386003040d00103a001a408090000050f002040700301c2c002d09090000b000b0507900c1e0f000080c030000c00c1d030050100c030440000ca002142c81c030645c00d035001150400840107465454085148481d400003241c00d01c6441103800100b07141c1c0c00c04501203002c10741741002904d0310710180e40c2941e6195030003a50410742d000712400510a5102d035402084403511a064140e901d40c14a181d48044408401d00100c8800c00c1e14010303c010b200c10150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 170397491 1250 170396241 170396249
    0x1080607020c0111030d0f020405040506030c03070605090f030a030e01170411010c03270609060912030c050a0b160f080603060109020c070504021c0605060f040b0a030e030307080402010906020d0207 87
    0x118a4004c5510442440c500c2840c2c0032407003da141144055040c040790740508280c600881d0b00388000c0d20b07590b040550310881d41c4c00699141e0009503041000c20f020304010503c1c088080d10f002d400b081e40340c001900b0210072800617004100012514030166a02840c0c40d0101d1200b0b41a420341424107072501d41c18050202d000506003c05000740a007854040c00b000d89001c50420341c1011110001480c115640d0007920030782e80400c88c000004900c0c18010050041500c500c0561400307042501e450840d200c0d40554800d4a02c1d0203560003420200e03600c0c4031030900c500c43c881052805207040610040800040c03c4101c170410001205003c001e943c04201c10703045491449015850f804010602c50412010354070541d030262001912580c0400c0340c443c4084081c03c0c00c0c1d410003009a544050105034451004150b0301c0c62810001031000d44000c5000e000a0700d0249400030350349103403007900c9255900503203c1e800404d0040041204640c2d22000d0300c0040c0c443d902c05440c2c00300003407402a41c0c2d0591802 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 170398741 1250 170397491 170397497
    0x50610140f040b121606050c101d03030a0207170702030a110402370e06030c0a09030b010303030f05070219060504050c03150a06050103050c0f0c1203190501080607020c01 75
    0x100c2807010303901c5030400300d85040010002c1c03800782603910030380765a02c0007007102c1c0ca0b050080100c0024828050f9084d1246901070074003500d40c0c80f04c054000c0004085e5100c0400043d0140318040800c0300301000950b1003042d0b00030f00166503109034180407170700000400202d2201d042c00c200700e40c0141c80108602c86000c3d401703002d0303121058050740010080c0c082c960000c00d0503912402c1c0700c0c4615074035105640b6603800309c0303440410005103a4411201c0c548501d50003600440b00308080f49102901c030b0000c0900c2e0249107000c1f03c0c025121341d40ca510000d0281d0045c0c00091b120b40d01502c030003209105070794024055000401c03010065000d4071030f417007003c5100a86142e43ea00005418413000780402c00b07081400a0076200e100703003110801e22440c070b82030360700708411407429101054550003841000c0c0074404452200c1d08010356025a1075080e40f1020300f000b824054201401e582038a10380146029590800e0304d00c40032038458003109c0072075805900c260304a03404030b81032103d40c58010880c107291650a207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 170399991 1250 170398741 170398759
    0x1104050615030c0702010e0a030521040911180a05031b040204050a030b09060109110f0a1107060f030c0507020604051521010f050d0c0b16140a05061014 67
    0x40004004101c01d02464554500c0001005010340e00e0000408145100b62512910000c05c030092144088a5010003007040c0c1c0542d40422403a01942d542c2c00010300d8850070036103407548030404072080e07512554003000d2501011070309085c440c400700c0000ca400c000a039410322044e46000e0000e039407640144034004840b290342c00b020355603440300e404a0f005840040c1c480708416690f840c14800815086031031b03410701e002c3d003000130815624502881904a03c082e403200d0501c24900401519030744511034a4081c405101108012b02d0828070110b0000c040b1030b140c403109040c1b1010054140c50b0030348030714810400304211610045e03440c5010713907041d10401c0c1c0d60841400d030039400d00740c4070340b080485030507400d4642e441c8503610010100300d8134182c03100800c0c0b040030a81c0d03410600ca0305080d5620024100d00c500d51003805600540c81c094114010701640844c00403580e03449980c03003400d10360065400c5030080c140320405e00104001c41500010041540c001d8180f401120700c040c89203c1c640184611074035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 170401241 1250 170399991 170400001
    0x161d04170901050409090f061404050c01052503020a060516080c070201022409070b160201030903022404110904031209020d0c0b0c010b060a121503081b0712110405 72
    0x41d81641c0c090501040200322803811802c16a6031000740c1f40049505906081e0010a15810540068044d6a102004100b182e4201c801076406e0340180500080c0042c503a40b1001090080007684001c080c0644c000d02401c581d00e06004090392401841c403140c9003c0c40c0384208005500409203580090002102500c0c1c011718030040b402c1001c5420402a00400807146000d2404008995801030880b0401c450384259919041d60b240d008140d041c0140b06100d144400255000350850307001d20f40b19105440150881408520301c0359040400e00c0781109a200c1000f0421040e050528142c140c1112480e03154030301598002d141071441c0c400441c3c803d4544003120215111540000201da5100148100079a1610906406170b0411030202003158200310103a140307400c108080381c10340102c590341c10782c11103105280000905101c00304844a81c901d080c0000c0411030000c003628051070440e0640e0703d5264100c450628010554000c02e071a08040c1c100400001c5084180d407403000c0040c0d801280130781e40d03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 170402491 1250 170401241 170401247
    0x705060f0403081306030e0604030c030c024504020a1503061809030e09010e01140604080115030210080c0307080604150603060513061d1305161d04170901 68
    0x41c1d07403004010b98000310307000d00031103882207111081d0b076281d9a040040e092800d558036030f14142078034040c002c81c8140d0a2078010920506103040c2c10743c005002c01112544003200701480c0c0c0c8a07154216804048201032070103081420480c1c1c2400d06c04655200b0143c202900040d0307001d1034a110f01c51908510f65a80000c0c18040e070091790090042002c2070f01008030010342d04c0060103007400224002840c44141907400c0c501035900c503050711000c1441c00042d07800d220241d8041400515425400b4034184000a14001c0034041c4d40c8107229000844485c0619503c1440381110f20b001a400c00c0c0404034040040165413034007900c0d40088203140045480d2180c0000c500202141101c1103d510502040032a070799070950420411580180c2d107299052265400f000304855490188100d4000c20651400115080d1601d80e0303040455940004240b0a26585071854070860405080109840c1e8100b00303e1a03080080b0010104020401e100300b6180541d94180203c000124440400d40003048844007a48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 170403741 1250 170402491 170402497
    0x6270815131703010906080d020d03110c031809130305070204050403090509070810090e07050d0602161506060521090f0708150a060f0b0307030b0603010320120705060f 74
    0xb07080703a8400d40e04141156414120f50090065842e910705241001420b0480042d003424669015400341800e2000100100e0107030402c0d82580703080304810703c038940086a090008020030403284035841c0700600304505020207400300401298400c002840d001c0003080d0050b04807034045504480c006840d0343d80340760584075011141c001c650031070740398020000003076000f8403068041d01c04460116840c65980760610107890020030400480c0c1c104500422035414181c041c40c0125205050143c00c10f50321038101050400e82142c20754082c06071b201c0c410354104644c4203580c05428a481e06626104d840c9803a00220b50200c4590340d149489200002c080309420f10025000001da9026610601d944e040c54650700d02d4400c0002c02d140d0459408900c072991984a840c044521548042e0401c0b0b152400f1305405820042082d41899250700c034410b180e648180040d0f010b18860491143c41c00b1010034081291400e0000e1180030b0b8011585808080100040d80011254110346183d524028841586840c1c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 170404991 1250 170403741 170403743
    0x30e0406030f030f2003071401020f07080417070f03020613170a0203190302120a020a08040b03072c0607050a150b10030219050912070627081513 64
    0x5010202d01c001016440042c0a440180640c1c074641c0c150128001c00350300442d80450035981340c0c010006600001d01c81d03100640c00021000005041815601d0208041d42c0602e40c115030001d800a400c4c030014104d032460020550184c00146a030038104810030f01310f0780f503501000c1d11885021034888220309214654802900c401070b0041c00e458028984581d83c0c0c1d1000d003049209008100f500c456024040c40440d144582542c02000d006503040d100b0756460744119601d03411405116100d0f03002c070361208020b100504407005c1036541c0f481c050f08004c0c520004145080c00c4144001c0c200203d80005007200d403413000080b10320603560356080c54528542242160002d1a50246071050600100183d0024a0644d0305541050a01c0d0700d001c0300300d080744104d0340601c8440c540c01080300704d42845800588100240a00348102c84908651100d141c07100e036501c91070002e09a040240060f600300707001c0c03070035084000074100505404c100c1c04175290b201e8080c1090340c03613000600155030103640301c02a540c0c1d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 170406241 1250 170404991 170405003
    0x70801030f0f201c020306360a120305060f10090f0b0a030b1804060b0607080c1b032b140309030301051c02030a03080a06080d0c020f010912030e040603 67
    0x101400354070001d010f100e410300443c8284840300c03800c0c08006480c805460426401000303084d05503030b01c103948014000d4440351a2401000504480c200d990a0700344c480105100d0340040412070450718119450034000021841010b04200500c241c07a00c90920b43c00340440d04650541b48007540e01f104840602c643c0e0302444040100f01c00000f090485100100340104181e034051022081d55006e2105c0340d0520030740015041c0780c00000038080341d1194084071035980001d004516008585d00e03440d1264100509640d960381000c5801440810080102d000404007070300640001c014502c1d043e800201105100700100e0507070314201c401c0301d2141401d109240d510001031616030504000d02943e03a080dd00445010300101000342c441c954001d0b10030901503a0040c01400c000f4850b13901200c0c2048041d1807450115100c1c980810100c5080c0081c04d0009410341e1204010002401000351030070020802905100e0a401c051210b00f08007003140a185400d030501c240e40d1081c1c880418020712203503002503c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 170407491 1250 170406241 170406263
    0x20c190e1303020c0415150f05030a050c040506030405010507030509160b0c070906030c0303090504060f0b071b0909021f050306120703051006230a050f0a0f08031c05070801030f0f 79
    0x500d46c4451120290b500380c8202207410010840f050340c0d079005d0386540c00b0105105000080610f0540d4004590000042c00a00e050550f24008181d441d00241c1382111a80d44480400c941280c3c94862a0351200080740100300b00da007802c900880003002c600452000c240001503035900644100a004014a6070364800c0000540d01e05012000c4030a030301040340050040c01c00052603142034042d07603003078030f4200042140e031618080d101c41c4d180c1d112003800c440e005500a040d5500c003440401c0c50b00244031403900030444100500c1085170722101ca0740315148078007041901c01d42c0032354040300f500c0c0d002105482001c0d4142001c1c0c6400e150018640c0010014425174003100d1078054141c02034412181c0141802c0e042813070600b4020303044210300500030381110020504101620307003900418080d2401900d8160102d880d490042c03181e001e960402a040c1c6d100041c840d82c64180450f0346c000340d0003902000c201c0c80c00c0107100100007020611010780b41140d00d86d40801481032184107881c1e480c4d402680219 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 170408741 1250 170407491 170407511
    0x90109020403150c020316030219060b0406061107050d030504090c050409050a090203151b040806070206070207060f0530010609080a0b0c0304081603020c190e1303020c04 75
    0x3a512502040720f0009039004208a00e942c14082c504424407150051410101c0007183c00e451860003030000d030110300c00d4038807001a4400d00c0c1101100c0500400c00424220003950502040d944564000310800000c0300000700102c0c00030540b0b00545030110380744540d61100303040859142c007170f0390440354225160922800c40d65422000500448000010503c05075035108145000c03109500c1002e9015004100030014000e407403c0940d92010a00c03d80358540f140304001d008043d002a00b00b0a0151b018900780801c03181c041240e0b0342e1041541c8010403410742011801000180d480070410103120011511402c105646640c4000c20382841280d4203085081c45d1020f90481d800b8420840458040640461113a1001c0390900c45550000f5110342d090b21100f4400f1600d41c0b008106881c0003900784840700d0303620a1282440150350180e0700400000c0e58050401050424001c4064070402e050712007004005c0d0880415a8040d41820b4a84104415401e081e4102018400055846880d1200f028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 170409991 1250 170408741 170408759
    0x6100c0b15040507050702031b01111b0a05301203040f231b040b1c0b01140f10030b0306010609030b09030f04030f060b030a06020316020a020907030207050a020901 72
    0x401c4a4119000e00554544110030307101c0e80701c0c0000c00707034040d0443c000b0703405025022049030b03031200c40c180361144441403950090350815404002c51222901104590112480d003680702a014010880e0000b1021144000b080410104088084454400c0041443e001d43d8140881780b0a8680c42084982c0c074a45450a03c0c100c0030022821141109142c0c14800d501c0058404200b200b00070000a14190108404100c1c000551906e1141e116803a00100354140d02c6800e900c459154810a80034103900051a04420b91801600300003c1112080d0441500d40d803030040c40c03000c1003815144039405e007030305002c12000307007052641c501c1c3c06104071000001c8180c2e21120340000c40c1e020b03000140490311080c506545a21518548103101e5a0071320080c4040f6100b1500501c0085c800c2c540018551005c00100b81005480c210642e200b80e8084104205074001e0340c0e0a2102c5151840689180e498560018050440140c0140304140d800300e204c108000007001000800c80d00204160215a9100440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 170411241 1250 170409991 170410021
    0x60b04020d0902180c030a180c0905010501110102070201080f2a0306040c09120305130e010e0103020a060201050f0403030515040f0902100c030c06091707050715050a050306100c0b 79
    0x102e02441103088440c000307030413032200180500c1c2c441d280d40c0d103183c642c03800000141c0034100ea80c4000081029810340007a4446581300000d1961582c0441c06d07614200026040b41c0311800281d1007a40100312060050382e102e0f581550100c940035441441d03858403e10400e0b2034030416181c0b484001ca2904141c034a041c1040650f03c5607008039400e108543c3c210200312240c0855104101c0604c0004c100300d0b00083c01440581989440d4860b010007003942c5003d0005036810a0340055004c0c0784002c014801d60800e180e4541c00b800c443d000070301c07040c00c20030f80622009100900240c01c2517034840220380195450a0341030700c01e490090082c00541c070102c0b04a03004112070740d4124800c2400c81c3c5004801405403105004070f85c0c05131141c40c1040540d80b40c060140c00003120403074080b444a4140a001e200385800f40c01c1007070040c002803a510382060240490011700072070103810b020b802d101034070000340e0180c222903010200303075180c40743c0b003000010942d400c020142c4020543d0103201b08010800110401d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 170412491 1250 170411241 170411243
    0x3050105090604020c03120601180f06260a050403270509010522090c03061a0a0b0c07031704051809010b06091003200f0d06080d0f0c060b04020d09 65
    0x1e85a41601c4010420089119080100701d15801c2444102490003407080d01e03d41c4004103040802c54201010100d05c0501d183d600034424840004106121031a07010300100314084102c85040140b01c1c402e0044108484001c0400ea80d11713031074030001810548107049203507401d2400856003100402e1200c0c4400161450301460703005000340000081c5510300140086100001032040d055848195030307908020700344481007500c8021880c403000000841c20722480440b06005208030307403002203800421000304480c0c0e003c00b403c440240244010b6603030128400048980c4242a40480d1380b0849002003c9d003d5030b40400d03800b60000448100040e0803141503032117803403800000c21110218204210250062405c880c0d040091111a03080c010700940c40080a420720791540120396000d0181c0708000d601840c083c0d000b000d004520003000340c4644c000c000240c59400085c20310348280050080141c0410440c1d44100a4031240d2941844182c1e80b00d18100755014005555881e0010301d948040c00079014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 170413741 1250 170412491 170412499
    0x6050405011d0d0b132111010501140d03030e060903090307061103090103110c1e010b040506060304060c0912050a03080705070b06041d1509070501140403031211070303050105 77
    0x480c41d50030010342c0e04900400a00402583c0240c12a86980866140080107142001036100c032010105952500520754215003000c1c059400c104e0b0705000342100303103880c0500e2440c0c1c140703030060051904040342c0452428050f60071a8103007103281011409007005201440c0c1070b01417007080c07140d070301800700090100400580481e1000399403050125049100e00f05aa68507800c203001e03016243d0300c070f5084803000b18100a00d181c20540345d151010306151000e00316141c101c2e08841ea03a2903141c0c0c28020307450008002c641c00c009030300d81034000c0780851100902c000d040a990f4482c40800c2401425420040d09000b84035420503070b02072502d546d50b91001002940031601050001d41400d114004903a041e55000d20607100640700d01c001d01c006045141964146143c101e903119141910811400b10480400350500c0054141141540d04209054002604109140c110050b160f50508212004c0325810b1410706d1400d03008294100051010102c200c905071000511030060640c940c10050603580b0881d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 170414991 1250 170413741 170413757
    0x120309050d030f030c09052701120308011403070e010b030f10051309081e04140d0206030f22030309140f12030a06030b090a060621120e03070605040501 67
    0xc000c01800c14410000200002e01d60088086014400d030049511603481c0c0c1455803500f41c8510006203520560144c0c0c0f0f107084442d011400c0b031403004502042c010107400da083c0c0030008640e100188914014040c13400c16034451540d000e40c0c0c0d24100201d0b002010381d04100700013540c480d900d0341c000380d0040c2c42d1480c40840e040081814240c0d103580400882e100100860301c54160407101740c000d000d50000075103a008090000414a01588203030850804506003040d582d1400d041100c180c6200300c0105601850b0700c0580303080140c442c0b204690300800f8503030201c8040d55552010708164645030301c1140c2900c5414100030708058141c0c2000310003501c02d9031340c1560050780c0e03141240c1d00c400403105032006170301c40601c1d41c1102c00540015604085000c0000c03540e1502d1b078442070a0303500c050310740e1308965002600141c241b044ea841040082c0454444a070710300302a900000041d0a84414054403a001d551010502140a4035000303066880150689082c1a40c501010340181c1103072084030b0220380c03a4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 170416241 1250 170414991 170414999
    0x103030f080f16020703050d121104080a0f050f0a030e03010507080c03071409030d0f020609010207020a0504020c190c08010b090402100e120703050307030306140f01030f0f020301120309 82
    0x34100282c03080c00590902e04a0ba40d40809040382d510400c203018040d03004030080031020800c02e11034900041c0d10340e01c801410410402400c0102c9528078015000080180403d00c1602c1c404680d10980c2030b000346111052080e5428914107007a03a11014042c141300d041100300415400c1108100d01c800210300030030a03965854000d5545040c01c4444a04c8200e08000203100c482c002d42c101c0c2240d036404400b1900b07110211002c80d292104845540020480800c804240c1d145d0410400c3c2e407000107003000358145061640455111500ca006584c8116000300d004544040c0c204400070350801c54100000440e1a1410401c002da03e06028105c02542000c40501c450300340042d01c18012580900140c000300918107040303034020041000345a0204500001d441d041900300701703080145011b41c000d15594940d03480c0203400c071141135000f0013a828140d007804076695280c400026164100f0308010810302c600c2641d401c02003100d40802c4141c54400b00010505807901c0752403141143c429182c012680d038079 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 170417491 1250 170416241 170416247
    0x1a010b03040b0103080a020c031506150f09010e0f060a1d0105090303090d1b030b070e0d02030c0409080f040b09041406060a111207060f0f020901051e0f0a0203030103030f 75
    0x200c80c081d000b003820400420010b0007020080c01106c0191042d51030818103140041e040c02e00403010000e000035006c040c0041441c0c40c8a13190003c03540380c1c01c05880c28511078800f101a00030a840740e0705009440840c01c469840e9811210310041004000503691654801f010342000b141c02040700c804c0c00c80000c005c680354001c0007110385814005008508002d280b0b002c0050944050070f01700c43c1d07000b100c0c01c55813110207101c103d00c0195104034184025072a000704d008014080c1d02407214441e5881400c1c90005d41c401199541c1c4803002503a010030114541c3c00c0c080e40520610030f201000030740004000441d1745180014204258046900b40050700e13001c08151603601c419644075500000c204112800140104040c5102c0e00071542503c7c900c1c01d01c0440c0406941140c507080e6200e6440e0001400b01b440c4510030300840340c6841000318100b00720440000c0003800b8544009600050400300451001c4c2c11509843c10790140003216a40c803240c022009441c1e4100388000c80105d602c041d403880d070343d0f40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 170418741 1250 170417491 170417497
    0x5010e01120207020d0204020301030320010903050307081f0602011d0d0503010e07121109010e1503180a0f05030909010911070b0601050c061005030c04050108030f0c070b071a010b 79
    0x401655401076188280c441c00009520802089a0140c0742c20882c2e00162141d002641c001c40c026114221120500086200b00401c0103426407031691408080d02d000a800c2000c0d246c0100c2c070352601c0d0150f035644600e4285a40417440da441e0070060000000180d45030b054129825407841004014640081c0010b070f40c0e03a640c217113800ca4001c41c1082c40140042c0307003849412603201c280d0b881d001e000030f0054004481250903101c0c400c02081c00006608641c1c2d40c02500400e0390141c1500c5103418400030340344004d0030740401751040000c40f0710340e0040489080100402500103400c54001e060441c000e14201d0390700d82c801c000450198450380700000e0100601d210780030644015801302032610030140d680a1608a00500341411b0103001e00c401c1245c0c41040150500c00d04080310003440050801c0101171034450320310b1881e4400c030708000040c40070480100035a68040380c2080500d40300c070381c4041424107015564002ca100400081079030010b01c51441c0e46092002e81c0400780e01801d07601d40508000c01e01c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 170419991 1250 170418741 170418767
    0xc27050f0403030207020109090c030203040b010b190f0903080d0e0c1e0d02060f0705071a0a0c1b08030c0607080a0b06090108041502040e16030902030d050304021906180501 76
    0x3006030000e40880c2c001d80041011500c140b41070502c140d215008801242c5100134981d0001e60701004210412170030615183c0502007100341c0c6403d090f6160b0400710400c0302c1c401c0690820065803a005041e900074442c0b54044c6901c8aa80764a072501000c54000900e00c03800c0c4075000b8810254000146c3c2401d017091140344c4010014001c518008100340700003401000d5049800c0380e02000150941c480200150901c50310a40184c00118a40000686548441c00d0054004607040040304209070304142c5c002e0000354440d8a40d00c1c8444030350159140c07004180d025500d40d0000041a102480002c24414401e1055855111403922201200021544c03022052900300c1d2040100b251690301624400741c1c0548205102400c420644807680d05a804c19070103480c42440c01c030300344024548030745200310120700645810400c000154000a65a031407210f101800e20a00001207402d54407070703046000100b081e0480e2400c0f004d43d104030050084521003000140043d105030003141544c4941e149018034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 170421241 1250 170419991 170420011
    0x9060302010203070803091c11100501060909182907020c060301061107090f02090307050f0d260307090503100e03041505040306050c0703110a150f090c2705 69
    0x9013081c0e40c0e4204550014018040e60f11800b902e03000c0800903072a806441c0e020540e20a4000c0314084821850700e4500304081e541d0904010050001681c851104003c40e02011804280c1c0a0f4486a90141c801c1c0100c0c0900480274140704c1c42202000342c211840700b001445034003034403969418012601c820051a041e45e000b8020001040002d1041d0821142640c5000984692603943c0e083c2d84100c41004008a1445801164081710b500e410b01c0340c04010b00303050301c0e000040b821400000d1001900c00c44001c00f0005c2d40a2003059103034105802546070b44a031019280d4a0400700c0c00601800210701c2014441d1080d260303440514441e81c09107081190302c01c401542881e00b818820b07001c2d01c1e00c611280d01080410310000000c070340039002c0c0b00c0c040c5107901800d5950b0501800d00800784103141c01d420b80a43d002031010000203002c0484100000072000c80016502c0a022800d000762800d65005410070f02a82c502042c6540011501ca0842e161402c00b124904200c1c0d2541056230401c5500c0301c22 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 170422491 1250 170421241 170421247
    0x17040b030420211603051c090f0e040302030d0f050a0b030a020a09050c130f0603110c07030b0402131508010e01060305150402030313060f020c040603080304110613081609060302010203 81
    0x440b00015096901080d841901c501c1341e0796100340010342d04180d00980700e07a40f02c00c031442d4410881c4000e24410103290702d0002c2c0c0c801d0812040300f0303844005c0d1040c1818103007810b0024040c9803017031033034500003c0c1d039442c1404020f0201d10000c02401e02a0748414080b4508880800b051600080c0c101080d9409021100301e2860302d44244002e01d40248800c41c0b5500c03c102c4060245000445d1700302601c40c00c030012005078203016006040702c9600842c4000c01034100401c4038801c600142540c21079911030000310740c1342d98501c00303d0304c0b01e00c001c0b441e000142c1c2440d001a40c400b40c803400b140300b81c840b96402000151000c2400d6400e0b900d07188000360468100c0c035a50f118080c540a0010303031280c00a41240d18240340150041c42c1404654000400500d03503c3c02000d8451313061240f03050000045505103c428115103c1c0032207880003502c010f00b01c9403440d034a2000c6460f20402d4945401d00d0400e0710350015621080c16446100c828032aa154a031104408190612140305690075030340c06a0055003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 170423741 1250 170422491 170422519
    0xf041a0601050904021c050105060408030712090b19020c012c0d0506160f050f0405060a0c06020f0d050a060f15050909040f02010809012717040b030420 67
    0x4800005403119040010070002c1d00b240e611580028100c00034504c13018580d4504e0814040c0440c1d0068025500c0b4140c00c102c10040c2c0000001981d11860f00302203070a8191201240c00da07102d1b034840d408034843c01c102094a800314404040000400d100c550251602e130a903007001101e02d032407007104400d01001d200f1a038244090148a81c0c1e0000a80600003140004264640a1402c5811510300b0801141404003c0c10584c2c80408607114074140c1c10400d0919007a8522501e09000f2070007980e0250002044010586108000309204140c00c589c0440d0f607251003148100e0184c0c009603c1400780e900f0000400e0b0041e40d14841c0604440403a5410600c450401041d4002481c8061a05080000600c0650010307a01c200c0c015000768402c641c09010002c05100146c80303040005d2207040540d03d000d41d40350344120010350440e10b80d2201d0b4404840c0c1d080320301d0407481b1400d4607940c0d5019141c0c003140c00300314054040c000b0346c081e40c002d100c2403c1101d509076240182407455120950400c3c5040c200d10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 170424991 1250 170423741 170423783
    0x50a030c02010609060f031e030504031101050706050106050301091d0634020c010311130506030702010905010e0309030705031b090c0408010c0305070f02240c040509010f030303050f04 81
    0x264030001920010601558404040301612641d80040d074004140080070410003480228610104640666000d078410154401610724007903031001811905010692801c142c1c410340c00c0712076055000744204460350312080020f110f50424000e91408a1500c1c00040d002100294802c0d6101c0c818002490196580000c04510314003200100c61451941388501441200c1090201402a8143d004041e21090800010159410500d04070b011420400c6200505c115034045001511800c0d5201070352a1100e0b00200e0040c0301c1403001170701a500e416800c11401c0f5001c8010710280c0b00443c22901d51a032a5010135450f400c001c1d04844800e460000002c2103401c2099031650300031101c49016007016039403059542980c06454407e00025a5903003044040d03a04070315a45810328041c4000c10000144000070f1561156001c4984c80303140a503800074100c406c5902c101c1d809440083c04075459544e442c80544480d103914002100442e0901f000294031100c81c003174041c40b940e041507103419040c0e4001c640d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 170426241 1250 170424991 170425001
    0x11070b16020111180a0e010b0702090702120d0b0901050105120114241201090b18040602210103060c020d050702060c071a07060f0203042f0d030804150606050a03 71
    0x440c05654a0b460f103100700c8500c89020301140b0009802480e8032134200300400403c4106904400c83c6801404018002d00ca006820340c0e46556050381c41801c5501c1b8400300341d2a0000980100c40c0c0c0c4400000c10343d038580c2d036941110f20b5403c01500d01244e0303030b41c0301e01c011350700c43c056078541d201000180d00041019081032425000d103000003a10f00d125021031071500342c0c3c1d60300d00551a01c1c0402e100082c04082c02c54448072a900500901904101c1d4801c6280003c1c0e0040c2ca00d01e0304c01c9084030160128090003030399411614440d8103e030310143c2c03013444503598000303001c0c091105580039403411503241042400802c0345418030300c43e540c8491070002c095007044119001010b68101910516501040420520145200722980011520b48039946032800340305039801e05803449405401032003404000b030784285001d1250020b24504001c16100c0f104546080c1207041d15080e0302c11161070b035000c24941c008035610b005074000c10f90741000002c081c0c618010780c0d00c1d40c42060000b13136081207018442c078440ea001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 170427491 1250 170426241 170426281
    0x20421030516170f0a0f0f050f09040f0603060603030f110c0d05010e060901050117010b030607141612031a0f010f171005030d0918020706090506040507030611070b 72
    0x712581507094081d0b00c1c000c98102c4c000845548000282d00321400b038003e5080381000c01d861820900d8003188800050079402601e240c078108000210f0031120981c5c0c3c681215840140f043c200700f003081d0380c030f04000300905481d101c241c0100e121400100141032003510040035089200c80100100742c241d100780b210341e00382400d05442e903569501c0c02c3c04244005000300c1e809090420000b1850f0350501180c408210007100d041c020583c50842c040c00d00d51004980aa4415030a0620260345420498400034a20840a00300034068246400800f04068410615140c02642d9000c104480c0d8031035003041000741d00010300303034401082c01840d801d5602c02c1c09000342503840c625110708810412070203181c07026003c4d52003204001c1c082c80c052085041c01c1100c900704601520300b1400306845e0500f00d500c501070702c5258a04a0342c00098180c01e20409800c080301c0340b68813a0445100e86003c1c04e2660302d501083c0401c841060400c0c51104c1c0031030300308080c1c03140ca582061080d40140c582c0914890311542eaa06 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 170428741 1250 170427491 170427503
    0x306010507060b130903180e0c130b070606031b061710080133050901090f0615030e0d0306050f0f04060302090c1801050f0d180206040801020421030516 67
    0x700e628544610343c954501e0380c00391802080130781d01440e02400d402c15017440a5552442d4a10030040c004108c0d1526400c4903c4141d81a07451703050201112418845410a003500d4000043ca84d042102c998045421240600e5014100030f81180d180481000640f14580006070079010071120510f0a09801c0d030040d0003800d5005200e070390b6010903800d4076045070448500c844070000b800024900050548548001c1d1940b1000160a12002030f444203010f0240d0b070b00aa69400504120340b81035440f4001812603240340d01440350303ca1000402421460b42e00021030f006410003004010b020303002d807034143c1c1c4000780204c54602c010003d00401801740d070410f540c001e4403804000096150b620507140601c0600c90540e03990b006605038044000a0500a20304021040201080c0c00c0ca001007518110000d4060114145a4005520030194085080a5031055000a00162094055000300126031070140030fa03603404101720040783c0701269a00054081007040222401c05400210300c241c059104407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 170429991 1250 170428741 170428751
    0x9030308180709090b18121309020d060501030b040e0c060c030904241203080c030702010e06150f030304030c03020f010903080705060402091305070e07052101030b0609010b030601050706 82
    0x3081c145003101035441601c000e40d8980c6858103100320103010940c400a20b150b075802051071400d42d00d585d103540d080448001d0001103808007a400000300e4500051042038015502c0f00300000080000700144d1242c40e01180c6081602035143c20135020388003e404400c4003401040c0300040610400c5d074003c2d51041c1e05408200081c104c140c1e030b43c2c419829000079440310510480d0140818404d00c0400343c00c5031000c160304440301070001e0303400802d4580c0000ca0380001a125159a54203902404c2107e4800000d800b9100811031001c8400d2021881c000044500c0d03403101ca40e5034181503da00c25400060942c044040f014400360501d04902040e180d4185003804d400c99a0381c9540e4000c2e0001481126141c200742c0511013545002c0912680110500c0700d000714402c980d5807001e03514101071282108002210000031001409002681c0c000420030890a80c103035410603070811100e0090200b1143c40140c10085041c038204108103c0c1641d5040101364655200c3c0c80041d9410b800c40300c000c0300c0c060b03122 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 170431241 1250 170429991 170430031
    0xb0606090609030319030e03030f060d03030e0105041a01062c0607050a1b05010f050702042d020c07120218040203031605101410050f1201050108160906050109030308 73
    0x300020102203020b910000364017020058010180d4983e0890310070541c3c014010f210b4114021040300707030004802c4070158981081450264040e0501a8508060354079207000c00042c40002020041c81e20440c442c180807907030b00c0745003c2d81e440c00b01100004851041c50400007401200502e060a00c040080c83c860a14880e039691604d4840a40d0080740e003408505640508001508220fa015100900b0404484200c070f8000819500076204082e128945039a0320f0062500c4044418a80c044c01c050a40c0591034081a031002070352010a10050307601c074011000884410304e60000c041a40d00030990018511031040c0c164080f44040c1c010786c0c0c1800100700000b00441e03510100c0002600c0340c0c01515241440c6540c040c101c4600d103080d2242e48440d0010002c030095124455419904100e441003081c2c80c100020483d4101c0c0d40544840c1d5610301030020490071000a400e42c3d46c88460900180401d494554140903906244503081c0840d44040c1c061000901070b0800a50009008190081040d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 170432491 1250 170431241 170431243
    0x71e0e07020703120302070b070e0d080a0f0216031112010e030406031b0905010912030201020408060c040f150c031416060b041a03031917040302150601020a0b060609060903 76
    0x546040e00503a00c010310420400c51000581002284c031403d01314201031468403140b014045c0140302c101040082c440c980503076a20120032001280d0841107950311100c0c80d0502501042c100c8084002610841909071041a070302550b80c0c0070340b030f0300101100c03442d4407900a2009000214880c00f00e15500c44090081001c4100b010304000e04840e507012601e24107022000401c91003040d410400c219007030805204d180d801054030400c40c1c400742d50042c419003040c1422802401203401602c103a0069078240002c0b508904007500035207a40a900c2e1281c203a803000c071101081390821058001ca01c4118074200481c2c05001c2c80002a546004103138a403401480a0101c1c1c549089411150966191500310541c1051f218142d100142e40c100c1a40c1a4120000240e49004250041c1d583d010180000ea54070703841825000c00d0208c4506d500e007001d0a2528000e510b891041101403c02d00d00c0350b00040c0a0361000402a071416044a4041820b03152141804926409000400d4100c0d10412852402d074034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 170433741 1250 170432491 170432519
    0x10501050f400e061312090b04030605010306052a1806070308090f0c03100b04060b030a0506030d0f0c030f1803031101050c070201120b0a0312110c040e071e 69
    0x1a1104003580c0740c1c0440031071080300e0002c6840440c642c4090100074014a41a005c1001c860b006441d8111010845c8006c580c02031050300000030302c4501090010070450290482810b1380e200c2d01081c041541c0d403060f05010f4025401d603120310828485a15048110640014580c0c845003403028510003135000040303a9070754404001140061002c0d410420450070600840344141c0d802006455010341000006e59a51111402d0075407032960740c065400702da0b456030b00900041084883c42600d03444e02912038802460216000341c02405000901000d05200307002510349a1407035150352190b80345030380b021198520b04060740340034403040b40c50106d401c24140301000300440c800e5403070441804040b0300301400c2d03038405012051120024401d8000503070300142c903907401c0c41c1c00c15070024005c0141000540f50008580c030140c07604030b0504540e0f520603407041041e0003580c1840c044a10600301e0301d05110480304960901c041d039820882d411b015440b01e0115003240155948040e00000b911103013020300d040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 170434991 1250 170433741 170433829
    0x10c08040c51140d02130504110c0c0a0302060d05070306030501020c030711030307020d2402130303030b0109050a170313060918110d0e1504150e010501050f 69
    0x80b400340d0301040b103001e80c09801025a090b4a80320301d4501c00180035010364000c01c118805000d030041601880c0d51011a02a0300400000f0018080000d20014151440e8411040c10381d45005450115075035051540807441220743c0604114608040d100d4030100a040180130202010340b0356100001058090000e44000e50300000596560301061910104e40039550103500c1c082d40041c852280175a841503001c1d10040d41101104001080c290720361010014003222407000d45101003045a108540b014421060380c0c82034400308006442c0100655280180e80b140540c0545420310520030306807000c02c001d4841482c4401c803400d10307405001024030560035030840e90000f46d58580c2004600d034844506c000300d02d6505010004985d007841d00341a54800d03108142c5159071602c0e0408c0d081c0340c00f005880c822808d03004559040c0c0c1050f00e0040ca588a4108125031014146105240010011320415048402c0140801c05100310b400500c4032045100750b401d100c01003504003200076100c0c00c100c0d840030b103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 170436241 1250 170434991 170435099
    0x100320090a0609031a070918050a0b0306090d0513051305091e0a030806011b0b0601020c030f060a1109030d03061a09242208010c08040c 60
    0x900540e000e00c84414000d611440800c0000d91080000c90600300c2c0310305040340101c8540141c1e50b183d61054072158102e40c0f10000440c1404600c12009074950301c001d00070355034007030184900300380c030004c142c4d8986003543c805071940c228078601c01200d4010b200414500781d4405111485555030000940b9017016001d1600d440c83d1913004010500e5014405001d8900280d08421102c01d030b03034032005a482001c400001c0a02201c1d1010840c507a000e070384003003403009880c058412528001c0ca070100301020181c520501500c40c1000101c0e2a250219800726642c0d64100144200d9540c00600340c0a0035130700d4084501d07140c00b00310b10706440d00c081c040c03103030080d4050704c020030620b00d45080c8690038451403030444c013544020f008070801652961050f000c80c0b4202c44060000c0502103c107056144a0541d4142243c1c020302c0d400c230b403141c810600e078070b084072511030080086100f4a2001d0700c0000d41107038000c00210303100d0000e200d8400c9064a80c00d0a04480b540348540162500c0b10454007882440c00c0108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 170437491 1250 170436241 170436247
    0x40216120503042d12020309040b0307060c0b10050607050604050d0c021302030403030b03190b01290d0b03030d0504060b0f030607050703110a08040501082202100320 73
    0x24080d114180390080c03486441c02074514986a1200007003245008a1440440500494101d521444880710042c00e80c0000c865510400c07a0103000c1e41d2076001c064658019418080820000d18011440b01c0485442d80c54402004400d59113035481c40600810385210401c03203240118407038680b400900006449030780100014241402c01a00d440000000c000170020004282c40c01038940095503683e06100901c00768a0313440d01d1400b5006814105041501441140f03100c5d0504c0452511100d41c0a000c1c42d48000240d80b950400041c02e180d1410110b40110f0110051b0422000140181407000c9500030006c1c2034100c44000908591040803c4403005031601c00703100030300c15a840380700e0210804035600f000b100104d00219480b5030006007a00144000403031040c083c503000d00340301201e08161900365085840170345402c0e40c29030410f01502e400204071400040004841a040b0550302d94848a89040c4044a80c2000240d01d0b94003000b004064075101e0310803070f550480020101600f01203140c251 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 170438741 1250 170437491 170437493
    0x1d120721051c02030402100503040515040818010309020306011e080607051c091a0a0e03031017030406080f0c070b0f0103021302090609040f0e030f03100603060302010e0d11040216 79
    0x607844103001e440e440603c100203000060b500e0444450b9518480c0c02d043e0303203a5445080c01401d21940140f100c51f12004038041004204099004200414003415414101401100110105c0e44141c100030740690116005100c005071b8054041800d005001148840c0c940301e0a00c45d0405000361006004250040b44080484890b03890841100300e14403c1001031083d561200300f01c8a81311703d14072440b403000c1c0d03005c100c16440c60f80180381a962003104982e900d0811800118288040f880f419000540c0744c140b02103100004011142110b10236541c2c18900d4548802c1c4010341c207006040d00d0341e504810003440340011000d81350b41e40b10740c00128401e040707503140d070040c0300c118030600096002d09031040261903540d98529094031411442942d002804c45c0c5140003d000412003d00800101d2001080c00310b03038031880c0c2c40158465100000b100407036950b01c502c25030541d0000c1c017000b40030030002405040682048205034400e079009403080c80948443d01c0110b0104c9e030089000101e40c03001048200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 170439991 1250 170438741 170438767
    0x40b13050708360c0301020403030e090609010e0f0c07150504140d020d1805040e1b0409020a0b0a03060905070509011d010c02010f1202030a0603061d12072105 70
    0xda1020307600122010041c031140c0f40914050040141c84161001a440c10206680c10440c41c80714160160003150f49545a0502404da451484002032084007003030009001403d08254142c100d40301060000d58580b9003601445080600a144041001c0180000340120b184d0995802c901c103501040050b5505150414030541011a19403075450340c403000d80b1748000c5900184462105400c0e113029070050036084259a0420707602e500c8030f540141002c00c03e007039541001caa141c04446818018aa50203070800500090303070342102010b0f52000030b9610801c0494101002132205030243d160026850744c85515200413100103440b041c0018402041140740c41d60401007122000c4404486091541c0034000000c24440e00050300904104400380d00515981c000c2044025201c1d0b8110255200c2c03408444010080c001c6200940d03205080499111001c61000c00c01400c04108002401009001c0c4201c04180d511580b002c4030015004039200c009d01c118180540107100c629078501c4c0e03440304441d03910 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 170441241 1250 170439991 170440007
    0xa09020304061404080405040e0a0204140906070311040504020702010e0a06051909121101050f030108010504110609010804031b06140f07080108190314070309050102011a0d0b06040b130507 83
    0x30703e0341c801d0120900011480c01001e481c100c030001c84020503c9044140600c0c14200d46220007900641004d800000c1148803410303c52250004804a403410303030780c0210032000d0b9600c41201c00d002c2d0307070100000c1c40a400c0c19001490000c1c0181041d9903450507160103c0d403021600d40c400300000b607003c11403c070b00c3c06400f2085d1071212441e1606200302070814102d07444417101310354024282c2000044c4200035034080d40039a031102110003060364403907a5810b2418064101118111100d01c011060030500d40b8040301503d25005c1c069403044141d985942d07060320381c112401254965107480c4c03041080003e24a02401d545021210840c550f5801c25110b0000030b440c0152880301401035600c01403101c0c1c940000d1645a80b800c0701a070103140c900e40d0905480110014580c5601140700040100c24583c100324410101e401c2a0700030130071140541c0d150080c940366189129030092070325502030041045590300c5a04000700500000f990412440003952544104105000703490303c0714100107030540c10600c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 170442491 1250 170441241 170441261
    0x30c1b0f100905030d0207050109020907021501090e0606010e04111812070627030b09030c0d0201020333100908010e011107120e06041e05060a0e15090a0902030406 72
    0x4244141c070788943d5103545034018207100710342c803075800306503075050207000d400050b0256009803840781d203401e1404000b920703400c2c00f1644003005070000b400000c0c01051845a040c019060001401d56a1038510045405d903010103210b99000784c5440c940707440344a049c1c004151300110b80208400c0c1800303d0b0148140d005000c012100c0c3e07078100c084104121500400e076072018880c09a44e0b2090003075082c0c51040d035910710750005803014088504001907258000000c251180c1410110b40f51010030300f104074207070310044070009c1000308081d0000503000501144848240104005804140010b40114228042c4200c410000444043c010044141e0038801d060100003004000d124031301c0030000c450841c0c451440000c0c10440c1d00b01c003000010748104245542c11900428181d070341d40e5142c01c2d070790139080588005601c843c1c01600015151411800b00c1e410b03503a580d2101c0c4404510101001829007120418171075000d020440300c1803c0e5544110003002d0401d5400041e01d905213820403400f11459060f0f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 170443741 1250 170442491 170442523
    0x30105010b070b010308032a03010e0a0c0e13020f0d06060f0305040804050d0f02100e01201e100906060311220c050c1e0610120602030c1b0f 62
    0x50003c500344142c0c1e40d0540340c024049654948075080f20b04822600640504280ca81840310000f1204414000714101c3d501c0e0714200c005600c54100c0d10089840d00070018010914107203160046040c0042d040410104452005003880310103605600315922228405440907954603082c0b220320f803c0395040b4600b0640e49410407441c0b400d90344030f0300350f0b02c0751b4080e00d4401d0710030b00013a40800335880d40e025040c0303038003a00308000d58000440103880c0354000e0b046140840e8001081c0d1003094148801c4080c600681c100414a80d5100d45815011100190301c040b13550041448240754410103000380c01144c0c0c030560f00003620900d5402d2120b10078061150f070798401d030380b80f41e6044048041d000f2110341240d000840080c2d0210301c4101615240f00c3c042c1d1b010f01600074a401500c9c0d0040020040500000050a0340ca203903440d44c00d05d071150b8803036028142070400c80100d800041000341d40035551028080380d801b8035006990050304c850740d040e082c0e8074030203030300640c1c40c9102c9050510241e104050800b0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 170444991 1250 170443741 170443747
    0x20405040b0117150604020708190207061b020d060f0e0a0309060327030f1e0908011505010f030b0a1d040c05010305190e010b0411040e090303070e0f012705030105010b 74
    0x5581035120313180a072501c0c0c400c0750085041c109102281c000c644000181102e45d104500b0841e10194446000384541c0d0041208c9108034131f072540100410000c8194000d00c09061400199500307801800000c501c10006551144040b0484108201410000b80281c80e6010080d251650003004d0320401c04804082d100315a00020f03001843c0c03a40c4412607980340c1080608494401c0007102c191142c1d541c507114803441d08101340d0000b07411450b8002602c02210080c051440d11902100c0c400a640c070030940011140d07603001c00514429072040b010ba840003412016902e607205000420502002543c10b40075018006020412008001060042c102824140301074600240803035284902e20840b83c0049485104070790b40da0030290703c41c00d9001c00041c030808c000001d000d140516500300c0c1c00381006040440f0081616842e000069911822841d52407180019800b010302407444404010a418001410241c20045207110390307103100440781c0369000b10168a0403007050b00b56481039001400a0700c0130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 170446241 1250 170444991 170445013
    0x40b04180f0903021506042703020a17210403050406050c0c0a0b0d0507020a050c060a031d0a0c060e09151c050c01030b06040e0f090f030703020c04060504021611040207020405040b0117 81
    0xe0348c4021480821850b41c2103140c11742400d900b090b00b8580000c09860742c19500310b0a400340035000e0121461641c072135141c1d50b400c20382c0b0019015426200580841c006000400c030f010311a0b401041aa14403806a032448410030000c145010155000b00091200124422400c01c0e064030566902042920040036440419100c9a40320010380d44024014180050a10702c254001d400144030b80c1c0d85005090060b844c448611512040420350403101c2280b4001e0024500d80328800c6103100c17050060039411a5144c2102d810082c81a40713070f0080d0030840d0702d0b55100b500c200f80d0380e41c030950f180180080c04a021905000408036000840c0c40e031710601c004e200500c8402a0141010361002461002d0b41c4940c8940703070050320f0074124241501140c4800555982090b80c049481c0352280c0042c1d4040c005241c940080005900400e0760440e9604514055640403401c007803040000480042c0006207092403540104040e150201c0b0709490550030350004104002c61090800076500c5100050001803201c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 170447491 1250 170446241 170446271
    0x30f03011202040e0a020d02150417070305060711120d0e0618120703051603021207140607091d071b20010e0108070806130c030c0206010803040b04180f090302150604 73
    0x1a41d00068009c0c0c0320955401c4640403000e084070090106100c0100861721503499403561a545030004582d280660000b107016039000d02041f4203400443c0018080c11400002900c900c0c1c0c2140340450851503c80010012011040c0406401046034001d00c41640305840603040ca0414092034450b10b10b80100701c07000c0820b60180954041950121190a0380d1029003000c07072408259000f4003041a6001503200c0130860403240f5118005410713802e4480c54ad075001d000b581c10441600ca606e2036400c2c031a0461400350361840c8072962040711130501c00003205600c41d2807161003400490071140300c9005410404018413984074460b4804092902500010714040000c005010190000d01480044000720720159104001c0342144d105601041010b040e03902001006441002d191a000d4000c0c01c0001c5000c00004c802c66060310b04410b22103207014a443c10764900454007106a40742641c2c0d403003c0e0042142d5a005151040340664000d101c29034000c01c1c0b07030b000c4070005007101340b240d854001c2040c02044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 170448741 1250 170447491 170447509
    0x3070606051e040203040206070501020c161401051c060e09030406090e011d040602070501110d0b0927070902070305091801050306011503140a150b071505040203030f03011202040e0a02 81
    0x9007990f02588a07112031012070707414012080001c0035540046403507450410f0005161000c1e0111001d400b500756038506100103441d00c0c01c008035000850070400e41e50030448071103600a01001000e00043e0345036898007000317040f100640e06020503401c00a001c004007680400090040c04070780201c1d449652410080f04c80000781903035002c0c070041c203000015091102c3d0307070f0651300c501d07410034024001c0401218000344d06a115480c4440103924156002a16003000015688181051004445030b50602c0c960b200800c0400e0300c450615218034007000c03c4c2c40000c1c0c00940b11851080c1c0790705848110910810030402c4060505800744403034080100400d5500080032030459107502d000116a540c041c80440c0642002054008004040000d11060380402c0c0e0105040d209008100465540c8a800d120300d544030342980070b030441040030360f800149250390344226001407008084038030304510415014540d40090f8440c1b00081c0100101c0e1041d81018041c9000c10000c800241c40d078611250f0003d11654 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 170449991 1250 170448741 170448799
    0x705040f0f050d26040b040314010506031b0307051206040507060c030203090103091e1406070c03021c02070510050c070f03031e0504080a0f021c031b03030207080c0307060605 77
    0x105038013600c1d01c503195020341001d182c0103052040d0307561500d81c071030521243e01030710085407054011100700e04024170620030a80181002005002e001600c8071081a0b681c9000005c540d040c000c540000170755a45000039091600c000e000941002c0c034060500c5030800089a102d8001e02c49000c15050000c0c1d8080f0403162882e41c02d00300011003007500d01b4035200d03510400076000203184144551005107c060446026601d0109003120901da80386a0125044d001c8044010050383c0550b280350201842e00d440da48000500341304480400d95541e0014510340e400030b481c03c0105000042e87d0040070814885c900280413000820f9000324610341c1c0040847e503940c502c49607401952403130310401512038400c54006106840490b400744040341402920041e503203e08a00c541c4000c00c580c5480c040c42d9860104140d00350f141c603440100c050518200c0982c4200044040660030880e00d000121124050490200348500540e102ea0701f41c0390580c22201d51b034111600caa960380c80c00c00f91020940c60224a51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 170451241 1250 170449991 170450003
    0x50103090b2d0106031d010b010c08030405030c0a0c0906120312020a030b040e150a0504020d0201120f14040212011b0c0f02030a08120a060b030a05060f090705040f0f050d 75
    0x11040148841902142c60311404995074220000000d110381e05400000d410b085600e4040c050010070440306d0300302c035540c1c42403601180c0d00c0d0300c41001288064000e190302500442c1541d2410310303803600460504048000c00c40301c101078035000b0701c44181c0c50b1003410701a01402200700240d01042c1c9019000d03007505001c0c0c002c82d640000d00001c00d0b41c401c0d00003401080018205000035081d011040341c82e40c01c1801c64802480c0c03008001800c80b0b0740303806124000c5402506164080c1e106d6001120b01c40003210711220300c01e0f1280b01c0903415140c0da120344211603442c0d581ca050b0a04052040058030700e404582504d0a038140814901d504540d41c50419010301c140c14081c20121031807904078485261030030080d50500520700b0715414800e289000b8502008008920802642c1e1100c3c84e40c104c1c3c25501a8203041c0c00d083c000501e641c25150301907174111900410003014110340800069403640300300c4e10240000c00119040060154484511002e0b140344014440040c0c04c1c80c000c0303211100d20640c06005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 170452491 1250 170451241 170451271
    0x702060c0a0c0b042901120f081e0304020f01031514010210020d021201210201031808030a060302040b0105090312031f06020309011202030f070c0204110d090507050103090b 76
    0x3031034028a460148181d000640b0482c80c41d00b42000383c82c0c42c803040e14040030301c260b00030328102c0c1710070015000e8107030b80038948440d24401540c1c0768900711160f00310089540320020450100c51a82084204821022621042d81d40e454279105000d8010b1032800c005040c075003010800090707002c412529070b0580c0ca098000e00c50a40160300100e2801501c0d01a00402030f00c0040d0310302852609400800720400d0001c01c0ca8641d03640e50305000703106840c1d440c1955140e1038a0480000561094108032454580445001440d0341035841d6010194030950f69104a10764419007041141424040e5110645d000d080ca20300345803101c0d010a44412138052204400d541c0000091043c042410701444244506e01d2000d030715645604019580f0303844002c40e14081035402c00b007016002d0036402142d01c04c1000b43d0310740d6490380320396405a8000c030201c0001c80c0c0c400d0301c0c0e1100142d480403607006020a000100d030007203801001c80c1040303800c0500c1504800e0405040c502c09c0001304034520318540d0046c60100005031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 170453741 1250 170452491 170452507
    0xf0a0b03010609020c07080105221103030f0406020a020a1a040e1306050103051b041a061305060c0d081006020604020d03030e061801050f10090b01090e04060912080702060c 76
    0x30061001e0340246090f94408502c03189018800144001603941d240002c010036103a44020800903452013402d0b0703400c1206104103200080d40f0080f0701d6016031018048034109840c0d5160035480c0d400a8002e4001680f0503039a01081d890030142c4d60000305410700c5c1c2042d55015440f2003180611941c003803801c0c0081d030100816008a28014662000d0750040010401540c491412302e0719254903224258040c91400180450b80c034192184480d05003e2030960714003041450107010747c030b4001c2d40c000100300361000c80000b003a440f40d0300141342038841c680180c10020954000580002d002400b070040c01d258284052003116000281c50781c1050301103a50225029207860214041e140740c004024807809107400f84101c50300c20301d520000c0c103580700d4001c0c02580e403118031400035541d00321111710b180c1c520362004014044080c0e0007000c40b110180340c115000c6803907104c0601c00c2e00c0192021a40d01b5920364143c000e000c05818031812117055440c01881504020a0096540001901c01c150942000030690 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 170454991 1250 170453741 170453743
    0x7030c02090a0506030d0f0e120c0307150f0212090103020f130b07030f0f020601060e0d0605130c0b030c04030b0a020702032e0903080c0309150c0405040b01080f0a0b03 74
    0x1444564020840c1145242150008003d010103440ca02d000b0b204000700021010f004440c8400103403100d5a400348600c800c00c04114803510140c0c4400074900500c2d07900d05c0c1e2034605004a60140c031003204801d68074003002c03000810900c442c00c2444219004240c5602e2081140d00403100c2002003403901507207900c440c80079500c2074442c20841c800040d04420000802088840c0601605406030700c965a011145800613920204400c80031401030b0080c1d070041c0000350003049415040e60000c0e050000d445250340d0b40d0821100280d940103198030b04943e10f40200880d1391a004043c00c140050541141440d0070b5560480c021804010081c2000700700007400c00343c0c60383c161030391f6980007011145036602031001604114850343e60311001d48800d407190b44000095000301171565078181d551403a59502c00c0c2802455401c040d000355460f01414640040c1d0800c1107680600581203220f220f81c0d01c2d4a081d04010480d1000b28180341801700300010420410950021103901211034000410340ca01040002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 170456241 1250 170454991 170455007
    0x20a090b011107080601030201020709050103021f050f0c0f06070201020a02060a09030311031609050a06050703180305070b0d06140a1202010225080601170a031b080f07120918020703 80
    0x40c40b0103105010b00001c950000040040c1240c2c000c0c0c0a40b4072050b01c55101d08141c41d0309010103504050007401d09000d900c18a203a4414845e683d140c9a03042c80f03810840a54140c0c8400c00b080d001e680505a020001a0240601030700417003180000c51808004d100d01030b494501c0249070030350b61a238951405060601a401c1041e0581040e160159a4904031000000c0a600300e01c0322400262409804185801e165403944151b440343d40328036003032514a58080794107507070507210184250b04881c00040016000c21200d4080c02c031101d082501d602002c800c1104998003540300060741d0310684200c0300b5035180c0600310b20949540314030594000040b030005034a040d0f40329685254180c508039011400d0002c403500381d416071340040c00707850003179981c2c00c140320840910b00c6015074140c104d85002e50001c1d004208681c180105801c040100c15a107403696199034100c0d100310050f400c80080e80b00104043e58095803421410b909181c850b01d03040a0328000c1346510480000340d6180c2c000b61500905004081c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 170457491 1250 170456241 170456267
    0x405070e22060303051b0f03040b070606090e15090d0e010807180f14041a0f0d0812100510080604050a020c030c0304050103060824190e010b1507020a090b01 69
    0x6002d6a903803403400801ca980300074100b18a80d8406c4060300203002005c184c07090060003a200445c1054102040590390342e0019400301c441c55556074000511040b28010002c0000101003e800e04001401140500300360007840104650440809030144070f8200390311000d07150f8286840c0c04035035900d40b0b099903002410b40024000304238603900052000205864038040c3d403219611004003440c850148025900e41c04a05a0074a40311441201da0b81828008411a480014110b104034a11515498903e82c0080d04000c1c08400c42001c0001c00e01c0e100d89240c2c000e00044d1103103d0140e40a000c002e000000c0500014840e075290390204210304a80e40680d901c0e2090341d02030300ea43d41c04445440e581c0f58083d101e80c3e4082414840c00083c0301c0310200701840d0f4070b080300c8901a0302060301d069910942d00010f150700d032100e43c54505540780130980d10a24200043c010000074559886038101702e4142011095902811420006100180c44111040c011640708400103d1120080c0740103035007074942c80700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 170458741 1250 170457491 170457559
    0x60c140a12020f0d05030a0e01021201060f08010b0c06070806121f05070e0a03171309050a0b27090a02030d0f08060607020d020d050a0c09090201030b0405070e 70
    0x10903038080c085451076101455030260201e80c190104034548680751041c440040c40401c80c140001415005260040711134a5641400149001d90060300c56111010031381020001541d120000742c525074101e404240500040c46030304d07061090a40f015031380d451004144a0403c2034410120b0802e4030740204032580c0c01e0510007541c1021f40c0d40540300f0780340c405030b09222403c030381042d0110380030a0007204198100d52000c0d00290754582151115540c40d41f0038014184491810003040d80301845801003000580310404003c140d0b130500700c3c01141920848103280307125460700c03195090303880d0b800200e91010211443d80e00030f19658500760315007090307003000c1d000e90035000d01c1c41500c030000e030320105910003002d0325252000c2035200c15080c41094003604500035008180e9586402c09841d0080c03c10070740034800c0040782c1914002d545e5010500d4502d0f1302c0083c0142e1142c541504568150081c1041c020b01640c08001074644008003e00d10340b02038035918002e2000900d2000c3c09645100300382c03040a0910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 170459991 1250 170458741 170458753
    0x110301020a032309071217040e04050c01080c16080403080301060807110c03030306041d010f0b040608010b0d0f02130c05250b07030b03010b0409050304030209060613060c14 76
    0x804050b002e070108002c1500c6140b00314540800c000c03000c9001a000c0c50983c001808054106100354014207080f2801766114005000c806213010030807401800500142403448209007040d01c1e2803440c003505141040d0520400e4000c0040c0340c2d1030396080d6080844a000e10940e018494103102c0c01c82d100b10740000c1d0403510000000300c0c1690300407603100e000c0c00080c0e40700c070194000030200b1030f11443d001c00f5960741034004001180706481c0c160064030786416002544000d900984801500711011400301c809170903158240c0d501e46180610441740249860030007402030084420000e84030400016004007149040b110070700564840c40745800d03e4011094082105045510700545281c10014071f00040300c43c0811071118085855030900c1240e84d100c2c80c40b29491300c1d0480280d01401191000079055940c1e80c1411040759164028550b4490207000655600c0342940184003020702d0041c40d0b50f019132400c104210404400d40c4822088030180d18011881074803500c0d107008a00308000700400244181 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 170461241 1250 170459991 170460007
    0x140a051308031e1603050306010e0415032003030d181b03061d0a03030b22051806010f0902030a0605040e030309060a0e030d0e0f0304030b070210060b031311030102 72
    0x4014038025074640c609503d46240041100c0140c861111403900c5280d008114000013030040c00a9900b02c201410007142195800c2e022074101d842009100903a141e50107402c0003403000000c10a0803151114400e0300f2038014100100f80e81f4494507541c045420b070740b025500c480b081c400f4803a2925951101c4c0d1050f9111803001800c21200c020b010540e9510300e03011082001c00d00034088040b107407181c0c40281c90300c1a9540ca00703a00500e5008a0703203802c40f4568440040001040031242204200c0450000702742c2441010303540c00304540c20810300311343d1201c80188418102010b0410454020300005a6030744d45958201e03001d00a0746e841145c1203800c10070800340304d03140800514811948101140e040d940c0d24030b02e06c2d081d902c0c0180201c0c101d80081180304001d4096801c500341f0710b458501210703c030714100306080e407175a406070740261000c070748410500038170a605110140d441c4840b00300510189052500100403403002800300c1040c0c40c1000b40c42c1040100c103800403050308000070f008540b41c86003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 170462491 1250 170461241 170461243
    0x180209060303040b12071107030c03020f2214010e07051209190f0b0702060c040b0f040506030c03041218090203250207090c0c050c061606091112030a140a051308 71
    0x2042e46c444001c500e449111311480e8000088040440303410140c5101001d2450b001d0221001c1d0549000d038004110030b003034140e8825050f1620083e000c11440000b46a54014940202c1f04010780081c840c04c0040e006103c0c908d5403050695000d0442d81482a90356103401454500d0f118403207407a955400c01003203c2106002c1c2140011405a02030314405085556044040741c507030404503042d403000c1341d052005004903080741d40544803030014800320501e029107800005a040d042105c2d10140c218000081108211030301002c0440d91646081982030401d0000d88a21258010f00610b00410750100005030500e0003596904500703440391108400c1e43c2c2903080c0003905c0760094010b0b980d040e030070200d880c4001c3e0b10030542904040d40181c09019104462f008102d441c0d400550144107500b0240c0c8104086800d40c80f0300200c0a01c50f40000042c42001414041c0145401c0400c150582003441800701041d00700600c0e001462045440554611000300706441d00d004103050020380b0000920003041c0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 170463741 1250 170462491 170462527
    0x311120115090801020a021c020c150d1b0e04020d180f11010e032a09090303040204060608060d020f130e0102030f150a090b0619021c0201180209060303040b 69
    0x4403aa03600b412150311142414242e100d001150030050703001074205000340c41e08041c00c4098041c50b00c103071840d0120501c0011141c0c082800101d80e40304001070040b401948500c03860900500c400028009003034901342c0501244265000540130781c0e0006181045010300f83c0c0f10040612107220316040d12140d40c10800d8010000c00340864016141c006148150760251002d0141483e000f402000c8545030051030041c100c00319500300f2088031209440d51100e68074181024851510b89000b0350f20381c075080c0104070646206600c40c0d4203010641082c030000b519049004002d040e0180d9003101c07242140d0b07000c541c003101000403a100091404200c049000b030190011401150300140492854490388074030b40780c0c00c4104079410741c050001d0b80c00b0443d820310740e0071082080d503006240390305240809a50301080c0d401c015135807005030000d0410400b4956004230a001c1c040d4940700811900105131000488851002c101034841e180c0d1600080c00c1d6a010400c03507002d026084502d540b01c0486a40020380d04d6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 170464991 1250 170463741 170463779
    0x2010518010612140304053a0305030c070c0905090a050f03040501080f09010f0911030613020a060509030102070f0326090316031b0b01050a051c020103111201 70
    0x1640320640d0000c5010140201010740300d107151000c1c030310500d0340c2e94001664668684401d16000901000a440e561500c48024040c1030320422032503e02d403030350784c00c041c03c52074060407840e403200010a00c0400d43c0241a650b00205001a45644800504007514104403941c003940d0302038188410400a40400314402440303a02c54011500b240c000840944e443c1d000341d0040c1400a505c00000400c40e44159044941080222000050b041c01d1803081e002500d0140e001960b28440141000c805401c0030400154080d005c00d440d020701c0c42941d400105055694480c40701000300109803041d40c0d540a40c11100020b612421250728208586009403072441d07880156001c02603038100c2c4031954003a1042c11440344020f0005140b8040010702902e044000e800d0040d01003000c685100b17010580ca0226620420b409807030040082d42c07509003000119012030b00002c1c040c0b400015035540452007401d4010800340d0908004c1152000c2c0043c01e0720901508541d0701c846840d00c0c000245041c00c0140b988001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 170466241 1250 170464991 170465011
    0xe0409170d0f020301030503030403030902010c0b130c0e1e091204120209010b12011a040302060d050105090703112d0a03050a14070e0d02270916030507091a09010303020105 76
    0xa80b0100780700e10120f000034030001d460340c1c004100082c0006c1c401d41c0002103c0341b0505160b20040c22540b1051840700301103804d4074501c1e01c00e0603681c06020b290a26a4000c000c0003030081c40c2d0f8036142c0140011000b9050025042400d080c01050880809121210404601d0140151540e81d207102d02c3c2600ba0301c00f50160b0141424400102e21070b0210002c45400300c1821400380480c0e4a060503801000f06c898410600c82e103001c0c08088016138500c401090460030350400814154140310801107910006007030710081c946803541c080211501c0b141510540c0c2111080c0c2c00b0860103084405c0d28015001c0c002d07407114100040c08141301030f0075a020b05c0c05002d20040401844031480c0350903285c89000e83c0e80001243c4102d0b0714503050b1070068550191584050035081d24254040e00b9000841c0102c08100700c214030210400005048c20040240c01a4101d402c4c0f0f58418610349030f090f1076515502840b5511030700c8100103800c145c034203103082440758030140460905695030305009000740b8080d1050407070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 170467491 1250 170466241 170466251
    0x409050f01060503010b0a050d11030a06060f020a230106150305010905040b2d011514071a070c0c030308070e0d030e010f1b0506340e0409170d 63
    0x20000e5400c0200d4140c640c01c0c0ca40d245140d082011296940c1c01c500e03a07440400400700080c2d040d02d0740502603038907102c08141116441e03007007400c241002d0360001d42000741003048501c2403d0190b6400548545116003208034200c0400c04886112021403003401003601c03a40c20001e00007130002400001d210311a4240e54100280d0b602d0305442e6050fa207050720080e0030710b0340d58004500303401d0703950200e444101c0910942415481564400100341d04090303019910540410280c0900285c000a6903044c0014110150b407421040b9900c141d030040042c0c210341500100d8900084200f030080b002203050720380007030800450340c2e600e140042c811541160b030381000460000c4a46032a003820500d010541c5d901d0345807c900400d1481c0116210500341105e5010800000c90419008400c01010381d0458018405401036250003d11012004044114804c08208885101c11020282d903d0a1101081490034044098010000030050034030640c0140024040710031011041401d007004015240d000c07034041c40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 170468741 1250 170467491 170467501
    0xf14010e0708090d140f0d0603060606020705030102192a0605100501051204021912050c09180a11040615030501170703030e061b030706050702060f0103020622090f02040905 76
    0x744a007070f2161136070041a044e82d4510800c2c0d1089014200c06043c6508450424600d40e00034000d80d482940f09036151a41c50340103004030350781806130001038402030f40250303c0d0800f4080800002c52012485c44100503240c848140a400c01d405101448941d170403045030504280c0c20b01c1401003000340e845108600312460001390550251003580c40c3e00c07402425804003641c5039028010f0075945000141400c0301c40a002142c0c410500a664440701d0240006200d000e1004060000000e4043e02c1e001c18821980300b0141e1a130070010f10190304503404902540c1c4011040003040207400c481d000f00745030b008840b90030508103626601840c122401000b1500e0503001c1d0620b440d0721182280005000200b9200c0b034078409007000b05c02070402d02003c0e01100c0860080c0102e260031900701907802c0f02c00d00d440d04240300c01d5950400c50341d074001000c10f410443e80d515660000d003051046078a040465540201c88506075881c0400c80b00c000c14480005002c00000800b00d60000d60250080c20300703051812010074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 170469991 1250 170468741 170468743
    0x809131401140d032010060806070c0506071d040c08190e102a0c0b0109052403072303010f0b0105041707050604090e0c0409030f030f14010e070809 65
    0x194101e2001d009850f00300b100351411aa1620044c035041031104d607802c40011100400c00c24101c024a508800107040b80c1440709140c188500136064230200b204c80200c02c404140c2c04200c180e040b003030609042614000c24640300d09001c56054900e40d01500d86131401c09000e401c040180d01c660035000d41340c016850202d25080c22600303540c01b0b21074107502001c0c941090121940c400c5003444500040303085400c100140741c003d2a102102d8010004501d222180e0801c806913076858058604540248010700c0c207030200d10000c0c1314000403140d441c040a0000e910648061128201034618032020032444500100d03c1d500034420901d41501a610b0708040b42d400c445c0390312508200400580d20700d45040d1501c015841451210400401180503855000440d55a07000040c001802c880d48040b4440580380d0090b8142341d9104151400345041065400000350310046a540780050b90400240250424841d00002d101000c80c19008108000c00818120f41800d901c0f0320a0300f0964503900380b40c0d9407005a0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 170471241 1250 170469991 170470019
    0xe0f060d0c1217070602090a0603020403020d060902010c02090109020c190c0e0603100501060804020a1d041e0c0b1b0d090506031e1005010f09030b04020d0809131401 73
    0x1411081980d1028044401140007040a0070f000f40341e65844880319011044440d0301c4003104407051580041c00000a080503040c0304010240f0381801c50a00d45160080b0f40d03d00321000f001041c885e40c17054480700f1a80262030310600fa0f034010f4101001e540c0c40f1588940298026210b08025100d0a00c04810f500e03c0c00002d118282d03800024607410740e00d0b1103011842c500014040d0f56240c0181d40c80300d04410b04500c90b442c000c04c003941d10441c1d2410a40140f20b0380c510150400485900601d904a011403007038580c1c1500264001c440c402c2c81d94480305580e4070720402720401099100f0040c00041d030042c012000e0201071291009240d0401141100a42d0724074000c01d180f400300c0c8001e0b404012514000014541c01105001e0f840340c04d090503110801c2d160740c101c0d05480c400d98110760601903940c2c041c030b000c0c0340b840a50400e0b903607007402c5485003101480020310080c0719040c441220130410200c10162100a080604014000b602c00604100a0402c00226505800c400c100015080c010b000714 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 170472491 1250 170471241 170471243
    0x80a0906030f060b041401171e0105060a08150319051b040507090b0307030603021f081f030f05100c090305010e03040302090403031a09010807090f0c020d1809060e0f060d 75
    0x121320b1401e8504040910388a41101c440f905000c0c1d118440340c1107001c1c0713100e0240304031004030301000c000d4080c11894000d0750041c0c100038002e00080c0b020481503a08440d420f03403c00c0e00810050010700840000900c2c00b03680008108031903144540405c100000001d440f100c03401c42c101031140e240c44110174003007110f404956480002d407094404010f00d0805400454020302d25140c0807400b00d8503500403d00780b05d54401c1c2203141341c1034148114100703940b110145401c04940b224581c8401c00a60714204040201e00018029101c0c012b40705041001c01c110340e908064003084148110768190718040c040300064401a600e550801090809a810100c00c031000d82e07030300805028840c0c0340c64500320000c04800c1ca001c8c0c0915800000d06803e9504c00c49100e00030b145000003030030304a0801c039001c000da6121100b00c980c03040c100fa500941064000c01e032804111800c4c0340941c1400c200071443c40800300071394403c66500307251510200c0c150703152090407403044100d0460002c840e01c405050011460750090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 170473741 1250 170472491 170472509
    0x100207051314160306030804140405060306160e0103091a011a0408060f040807061118010905060d020a170406140702160306020d0b03100606030e0d1403060d080a0906030f06 76
    0x251100c041c094100360b260f200e901d030001e2482d48a81d1080001d5000da080003210035510f55503680e80380b509000b8190321060039000740141c1d0810720041e5452600c08006582071006004070b00009901c81d5000000300c80e0860390b50141082c8480341e07005000030a002d003040f0100032890b01d440e08808001150121500072004040f05d5603941401804404003070022a43e084040100c1008510b1740c0c0a0100711a0507841002da1b40c083c00b140c42e54403003941032462070510041e04003c200e0f83e501d10702600c1406004c034902503034640419030200c1d03480741108200128080c0c02340500040c0003040d4000c03000e51603080104120790700c900c08141d13903070300070001003100328404c039202400000e045401030b0070900d01b12240400c42c190950002070a000503c049015400c5e0340f0b01d010040150315014010282e0440400362206644483d80108002d400051a4102100001c040303442e94079100404985d81d50080344140e1691140000100821402e1080c440060b0a020040c0140c41043c801d0303e0480f000c0d24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 170474991 1250 170473741 170473781
    0x60903070c06180b0c0106050a120b27060c030f0106140306040b04020d020d05160302030c0f090a0f030501020703080907121113111308060727051002070513 69
    0x1150440d102c0041100380c1071031401a000005031380e01104054208512210000715549080c04107000700a03005610540c0e1b041c1151305100080303102030b8201c94000701c2003038070115149010801e00304c0b400b94007005015288592020404026030713603006103008080c000f911112a990303a9404442201c184443c1054200702080850301e185010750003035041d40d03030151004d402c00d024400003401701e8105049541c0e2154440c0200b00f0400c10403210400743d007451f81011825810019545400c078012100c5c50109084005003c24081d6581e1401078014000c07056120060344d01c919219010703420500e401c0303000c1080e1380040743c0b40020100302c85c016600d262220f18040c041e580c9907a101001c2172111250410350341141031050308446d0082003106a590381ca140c2d0ba81d01284500007110710f61354443d54450300035005028419a0002c51011000b0303220110642c1e1010001d41c0c00b004d810755511060713208580210320071a094000c1940c00c202c0c2d5085424820818031600042c094400180d081d043c079000407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 170476241 1250 170474991 170474999
    0xc010c0308010e060312030c04051201061a0706110406120c020a020310110909070320070201050403120e1908010b0603010e071809090503120705090a030213090b0117060903070c 78
    0x203045184d445000101252500f600c1c40d885062590b000340e41c000036480d0001424002c40c00c02c61050450800240001c0011038036003000b1404401940401404102d00012000184005908145440c000c03a03a069035a565035400c0c06049024203980500703023681800341c43c0028034000f00b0341404003078014014060b000c2c010341d0164000c01c200c84541d000d0940510030f00e4400d460b040c05e6144075120316100015504484084001d0030a42c0380c0d107100300301c10204815801070b41e210041d24100d0707034400d00c1d415511000c0c89080d10042c020300301d2182c00c0030042d4041d001d1090651b07001d400300d0300080000c1011070000c00900803644424054481403407004000701d9017251186000950420100240404039504e4404403410f070385030001c007920240c0c0007080d000c00414a22001a03080361640c00e02518050402e00410261123803484064482c0d0340c030005c5068507103460341000c3c1005501c04116001c030340e15140881074080501004407001d115100005450141c00022194816002250441c80910b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 170477491 1250 170476241 170476259
    0x20d0b041406031c090e040f03030e030c030f1b010f0f050106090303020c45060603040302150c040b1b0706050f04120f06020318010b03030901170a09021002060103050c010c030801 79
    0x75900b0000304011710300e038001860301800340c1700e5802644a080e0403841c3e08420f040080a40c6c08144030f061a035002041a0030380d0f444000100c5125154112501c0e03200e40e68113407145400c111241c04220382e9401c080030300808270141e40c404080041c05030010405030341ca8050459010180c0e0200402582c0040302540c2c461a000082c0c030104c111051917104030341888842c03007161a81d174159144202102c07400c10324421032110141d99010300c0c20341d4401d0461505440c000d6607107898400943c0d912283c40007090b034800240302120302034203038162082c0d51004d814170000081940000d03007500d0390003548004100c2511230340844410282000100d420641401500c0d03240c0b02120b0401c90f9410300c0e4000d5180041c4081c005141b0034035400c2d6101e0b4091060700c1d0507609503117460b401c040c82900108668803150f07030404205030450800d200210b0740d50b950304480070700504d94110041c0d80030085030b01903a007295002440c41d05883c441e01c1a5040407604800545205001d81c20060120703000e40018040104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 170478741 1250 170477491 170477533
    0x210a0c060f0e06040c080a0f03030e070b0c03040509010503060105061c020408010c0509040c0e090106030c050c030415180806010b030a09120305090d0804050c090c070501020d0b04140603 82
    0x805154001201d035001e902010482c1e49210070102c15822100800c002e1107900078400004202d4000900b01c00307103507540c409164100d4444010241580c1314107000f07016008106045c01742c10786d018650b40d1400c51800d16540c0360014883c0c58854488500042602e090102c0c3c0d450480e00c001c1c4c59141044a80300c5602003503a1400540d10043d5401d20001415400900a00030048640e07101c465440c0820010304c016207960300e180400340300000ca081d03411511443d03103940c11a022850009140c0c20f8085080341d040c4140c0305e20a0071031201050100700314034a0758112598940ca42c8030350b041c1075402c02d00c100c0e0710038045c8149a41034000c0070040051061030700c01036a000640c07000025110321242d0b500011504212000c0c40006d0380d403001c01c811464100700395250340409040251051400b80e84582d550141c011001c0e00030088030307020035021000581521010396000000359141d01c812a5854000c1581d005040d114a0070719814404004184001c1c9001d903101402074100c41c041004070391000750b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 170479991 1250 170478741 170478743
    0xe01060e1b070804180e010b15030a2a02070e13030e012001050609062d01051c0203100902070f03030b12030c0309090a020a0206010312050d05090a05210a0c 69
    0x404100c0c81e40010111801000070717004a45103040315030408148a41118010110a503441e0325121740c00380c29540b440072041038094045581c0369244c0d07030791411201608441c0610060078001e045c1e01014540d54203c003443c060010303421030300015502c19402e060000b040e1103007008007612110306404644208200d010001040c10020581940643c0c1d01c2c0d5071410902031900d25965030340c1030101c0d03841c00803203141c2c000c0d008851441c280c0c00c90100d0491040d4200444078410041014401510f900640c20366000c100c8480c4800c42d010810301c0c050700a98001c42d403501c5440c804590105200546100f5500c299070403803d50200c1d031b403880c0d80c1600148806042980d0100080a18482c0384d2800c00040101c0e43d5100095030b15100500b050241c0c00c1c0e4064410001c40d070042c00850325a960004205044a41044a1890781c2d450080305075928403814025100f071a00301001c00c0070700c5500045215690340300f00104e0746980d00c400c20a403c00610140d0441514108000540045105020007110320f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 170481241 1250 170479991 170480041
    0x210c0907140a030b0d20060901210603080a0206011502030708030a0209030106030c2d080a17070203070905070221040512070509040c050a120203070504091e0302100e01060e 76
    0x6100704000751038402840c1c5c044071250903c0c2d10158943c81d15428000303050074242c1c0c1007070800c0700b101c1c0080d2036a81040c540030309004d4084140c28214089820030070007236400800e0f1340d0341c4107011000251521000d020380d01008462004c0c4420691000086980c01900491aa0704580f10845a1006907100200040d419901d40e400800441c3c5001d90850007402040c04d480300021486c4400d05a940610a03682c89002440004100d501c40115081c1e8240e98050500302034030010f1002e042c12030246840107501403145a2010941811903401103004141d01d408490b9000050b10010302c0120303103c1d2314490b580900b03000030092400c284851441121442040d01e410705e4551010860050085400762050152b6440802241c1005a120b2010b002d21010507003480f000c40e00443d80e10441d0780f0034507003e0f603038500404e000d0115030028810240e121507400302d40d84d145030500030740d0340201c83d4041d20110726101d00c107148400c0522840d411246080030a510603503a000c1625111140400d04c8400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 170482491 1250 170481241 170481251
    0x121603020a0b07020706110105010803040501080c0f0d0b12031c0b060c10050f060d0308010509070509060a030e0c0d05190305070c08010501180b0102060f0402040b210c0907140a03 79
    0x40401d0360080c4989140c0d13008100c66840e019004006019110b00c0c440d03240d00d8480140529000441143c2c00d595080c00e290009449030300c0e01d40300074403520000400c502c038085801586c441440d04801d5080f0740440d41e403581c000a4100d42034a0784107102104100500a46030500000803d0f003000040c0c3c8001008907003050602c0d06050f0810241d48100c00c45980d030350042010032500c1900f9580c000c0010b40c2c034101c500c030680d030b8094510f141c180035880c8140c440200040c9141d20400c111410503502807d801e84a920300a00600035007204d048010050040825079481c030b040000e42603105039045001001001e0714000e01003c801c1c001842582084800c106000126051151401c010a00e142c0001180e61500900000c010040d56044881d2400c140101c101680d000a0103a00801e54010612803a1124400907005140d10034002ea040142604450f4688940b11f14640d02000d40c01c0030340b0748001c104010444412000c5504201103801c4500c07030041c182e1480003400130000c01d401c00180d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 170483741 1250 170482491 170482493
    0x1b0609130f0b1c14030c070603021e0703020a05100b0307050103020711091f1a042d090b01090e010f030b0a0e01060f0602100605011d0a1a030f09121603020a 69
    0x90b2410240703c8100c00920180c0c0345810070002d4000c6820307202c488409141012010b140007503c541c018840c100c2007503004a01509091989880544005d2507050031540c0c4021b140341c043d44581c2c546005403a1801110020207140096004210542d40000c0140900904180040d8000d420070041035607918000342c441416900d8907070095020350703d5444240f2146d03004007200740d1340e14482d0300100c480300303066007010300004020800e40e82518034001454000c040c43d4015000080d01590504a682000036800168400e00758025040d005080e610144590f0b00d0750032072003064001f881340c810284501b09041012416004e8100d41007188408c0104900d6210710b5803030300f5288590441107058016000401169804004aa47c100100381041c0a01494940043d1000307094a121203000a000f2648a40b2a07443c8410311014206d44406075860515003608400c1a40003115000c8140140e000407407418100010b00d00d0f0400003194406203002003002803040e1303910a41108505522549464030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 170484991 1250 170483741 170483749
    0x70f1e170103060506090c180d03050c100c030b190e07110f071517060f03070305030f0301030c050109080705190305030307110601050103060303020601030b25021b0609130f0b 77
    0x181c02180181c50200303c504003182041100c40d0098455543c802c1e0400060004840b100368040d01000c0c1291070103004941c82c2001d40d03540c450401002070500450b15004440001e5074402d003040c1c00195001c0051401d11001d0022240742e40c82d04480241104408022a02c0310700030b8164003505501c0c01e0740d002d40c6802c0300360b80390641c3d00304c100c5010b4210318402c2c44540e403010280c0070b08034406d2030031074005500590610482c49025142900a0030312031030010082d203042002e00011a4043c080325562076601d9590001c41d00280003c8036028910480022551304c030301100300c140c524110103000700610345020040c42e44c032007900c610b00601101e1b000001191090016503c6240d013601c0b0018000710880095042410581042e4107040c0703008424000300b6400034100c1c1c1980c0d8010880010317915130f240301492060040c441e0300e01c1c21705010725421942e0b40c082410760810011561103040c03003203000e007000500c2c081e42c4001c0e900158401066440c04010703400c94444500c52002c0001c24031842d401017 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 170486241 1250 170484991 170485037
    0x20c0a0303020409050601080411010309140f0714040e060c0711060a03020a09080f031c020415051902060708150f060409020702030601090203040f0f05010b060703090e070f1e 77
    0xd034086580402c0401c01100e1078001c2d0b80c2e000d0070900e0b04208503d015900c0305490342c02c842000d41019940c510000c00c10141c0003495003150369034030890305110b910600c1a40d544032240500121425030701a41082400c050051030014540354002e04001e50f80c0001c10915a00b0002c81a200040b501c1e00b1003d0030b4480034010310343c221469078056030b0790708107841c007800891450740b100d045680318004126800c40040140c450013503072b801c8000055071300e051422029020796008204904640d0385460201a0081c0041100407151200c9c0c0c505c050400100b030fa2a40c0c0b044400d00040740e4142c002a441c605400d00500380342d8802402071380103000013000b0940c3c0e900203030812140141d00060400540c0b13810441e25004040100c410740c554500b9544d070f05402078122000a048884c2c151b8031504110080d0003d001e1202c014095a4030388000e0700300100081043d2140c80c448660000100c0c51083c4150a9005545030a442d030790703049812101002220070001340520301308004800b40d408800030741a60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 170487491 1250 170486241 170486243
    0x160b1003020d2d021e01050c070605040303080f0f01150c150e0106080a02030d03050402030f01050f0a050601021b13060509040f020f0109060c110103020c03030f040b09070f1404020c0a 81
    0x3128100e01242c403000903e03141030000b55603401c480b1002c0381005a8600300001d2000310415204010081c0307050040c0d440c1d00030340481c2c61150140e82030101d401c0354020041d000f200e0295039403003800d40f590a220360340c01006558892541440a00600102010540001050466203050141c43d0f0b1039803030b81e160220309e00c2c80c1007101c02d40f030b50310b01c0642c40800d019050281c907100004c1c140d21142c6a0019545480d01c0007014107140d100d0340010155981404403141c064056802484589082c0501c0204d4040840b040c0845600d0440400c2e1503503c0016080c50410800481031588440d490402921201e841e0f0705440b41510356101041311b4441c0c681190149100d440320090070100c1e8410810003540b0900380074104201044200445580321603d079400c9500202000c58824450004034082d00c200120394a643c44008240102290840d280903c101d00440c07800b040c0f5100d04102c0c588914032403045911045a449081c45641d0002900090405005200614180345140914140010414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 170488741 1250 170487491 170487503
    0x5031b0d0606140f040e04050f0307030c06150e041b051005030a060e090d142b060f3002150a0e01021c050d090c0f0602010b0303160b1003020d 63
    0x25041002982000b801c0c80c80f4100240f000b4185284c0b0044d2010600443c42181c004440d41d1001c41d0501005200c007402c0c40c1d41e11400d40b5a5030b80d140c20302400e10f561040c000c95401d49840080813450050090364030590b6442405035400e61100d0300c3e8549203044512000c0241c0000701800038aa588540b015034a020007515465101d203000c1ba5800c4c1201c160790b1250034a101c0803810050700340702c080340032159910103003010a660302c1c1100346940306000d0860307280c1c0c40300900103400c52010158603500f58482481d101c2400400d0f290914450010000d1040049030303c0340e401000c20701d0902d5801c8a00c0040039400455080b10345800140031700702c0700c030701a001b015000995621181d07031041c05110380d62001c5c0018440810088600d010700000400d004c003c10402181341e071000fa520b41c024001086e0403040701c3c44180d80b286151002682e06201c0ea9015601e0460400d0881c180031060b1200000301926940c4901000c0d2907171840f064004104401402603407001000695070b22001100041c000c071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 170489991 1250 170488741 170488751
    0x3070e040b0402030622020c0316050f0703050c1e0406090b0907020f1002030901021c061403071214070308030a36060c05160b0a140f040305031b0d 65
    0x40240812182071080d142e019500400401020f40c4800840030381024039482484880d0300d102486034001e00a1240524843c040007030401c09040040c0d8885000d00c2c002c0c000d90710100d02c0c10009568030800d0384001400ca800031207500d0402d28103c24a4014014440101e80c1c001d407030b400000741101d1a5030000d01c2c42075a115508021400e1031070145600c03050a0004044100b090340341a59290f0241e03207100344490b0000700164110b2001c0d0150303046030700da600c2c1180f05040c5c40c421610140032a4020a090104e2061000d20145800103031141240c0e00c2c901500c10955050300d8050b41d1110428041c90349208525001000540040040d40700b0404034900048020b680303400241001451103608141f20b0550040c964001260341c900c0384140e0303004d0000200341c000c00f2801c1d11140580085a54505028a0044180106003000c0d901c1a40600c9040080001404889085074415900310a00d6140c0e040080c00190040c002507030012815004000c02200d0b82c4401141c650101704420107461f240d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 170491241 1250 170489991 170490017
    0xe0f010c0905060705060f07120903080603010509120f0702190306060e060a06021906061701050907080102070f0f050a06020304060c020c03060c0922090507080c010203090a05010e04110307 83
    0x4044007102421044800318540005502d940d40c1e918030103001e0024411114000c05c1030035000740d40007911202181014011504c06040c0500b9800c0304440182c025401d0400080c13104401082464074504281030309801d000b510a0202c2035500f24200803604150141080c60a41d50319500c03003001503102d04000f00d409402c00824011060020701040e000380c240364010b014050300454503410603a05462401c801060a0a00101a0410368000455100382082400d140c92040d040740d40700e14024030880d030f0034650f249011402c0f4400c0460181040310000c42d0000003403021100d074100c4078050300460301c04404686450040341d01c16107003140c100342c4d1041c0c100003198041c080c480700705408902400d498680700070b04418a06c20011803500c00c0003201000749003818030005010280b5110501004400e41c0c0f403030890303550f06403800784d0000b41c443c2c0c1550300c00300d42c40001158154036002c4c020340d00702442c10005641240a0031341482d0b0040d11055825200040c001c09513200359004c0c0e844141240e11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 170492491 1250 170491241 170491247
    0x503040803131d070f0c0501330e010501021e161701050901110d18080d0203090708070312030509030910091401051603050a1419080109021c0f0e0f010c 67
    0x1100c110070071101c203c0c003003084207034010172102100043d50821030300800c0d6034903105005002c41c4e1503140007842140782c094129020b00201c0f148070080c43c0d00311804151540c03001c4001030424841c40b4016031222104070540c0f40380c0e8058151003c1010308540c0c0c60203904040d40100e5030745400645540c6051152174030429000d0081d1a000998107008200198000d03480360901d208140080c0006900c6003403900703510045100c0041115085243d40c0d880e0481d00d03403039001039441a100c8103154407500317102046e440d10110b00c100c00c0b40d902850120861070a080d080d806040700411568030f501040c80034611a13201d040381840b90305407554402c5041400c058259801c14a4048031604001040c00313510034588908a0101070550141007030343d01d41020324001c842d0029047c0007451850008a8102c0c1200032002034910101e0545c2c403554043c0e85c03208100c80c1240580d8440b01440441d400508600416561042d20f60b8868600c020440d0103405155a152107072030313070204106a541d20842e40000364 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 170493741 1250 170492491 170492519
    0x3050303040b1f0911090411040518010e061306031a0703061502030708030606090d0f12110a0b2725050306040b061c0b0403170601090b07050304080313 67
    0x442034156110034111071003900f43e81e80d0107000b1503003ca0350362050b0160700c0d0b4000c0199034814200400034807922312104a5084584c029108942c040c0020124202200044c401d105045e0750881e10110400da880800b00901d21034030703074400500070360f5403000840441d1607400c269030460000d10b5507001c9814900001403c4800300c5c1c1c0302100149814000080d1294080120340205401850381c42e2a81c9419001a04c02c2c45a0000158081500c0d4611810006082c44011401d40240000f4045d08240c24066400c40d03201219007030719170030042401c0c00249130810000c2d000265120303070040c5c6869240e0b10100d4030f21b90710910074940d402008e01078100010f400b02052400d850003000d0202070b2400f00801d54400020788001c00c0e0740c281c1d0000542c0c507261214810280a88010392003101460f41c24801d001000c02d50342035000503800b04049021100c0341e00160700898060792022a50340c81e014004000d600485011a00c2d400100030024403103400700041c0900a001e18480074031720f4030f01104883e000f0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 170494991 1250 170493741 170493751
    0x604031502191812110603010f09050c210a0603050615030724050a11030403110108060924060f0705010b0a06020a0308010e22080406030f02030402030c04022203050303040b 76
    0x3c07890380c012070791a110b41c2107442e00321051205000d0303503102d5514200caa0700d00c00140c1c9540100d80072000090241782c03840303514202c80e041c2c401000b403a00d0b5002c0c40800c030300c21600030711035802039010301e41c2c0d504401030901544040207400006546440b581c0b80c0d414140141c0b18039010b404c008802010350325003848050010008401d2400c10307034243c44030625094030030030408e60034801c0c041000c0311598050711840c0e98000c40b85058960b10b40d12450441c01c030400c3c40340414001840c0000007045800d0420031280a072104d6060841803140109901440842da180041d8001405101403071404041c0c401400317019100728000f05441004005020101150b03500100442d8031030740840740440d40200c80ba50560302c201031104019511494150344c01c005002002103000c140c1c0d01078070144070140003e04162080f0307a42c24005030740c0e212106000c4c0d000a0f5006507040c0c2150790240e1140c5441d0380201140703000121100c10b4600341c1016098010519070066071f21f50400010481003020701101c0703e903c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 170496241 1250 170494991 170494997
    0x60305040f02010e27040c050405250c0c090c081e01210b04060b01030e1203010902030402010c080415031104140d170412020307060f0c06020702060403150219 70
    0x525041d11010309064070000040c0c144404a4070b8403a0685a0009948244903218140030f0b00309001d51441410000c22502a0b0703101c2c0406002142503d4071b40a421700401011003a145440b409410f807420b4401c045c6070f140300b07010281000100003003400c05600000c000808000071030805648015045c004010120320444c140c100320780720722419014070641518000c0500c110000b44c00700365404d42d000c500c4405001c84294800300020890b150300108103c0f1070a0360284501018050020780d202444400618001400d1006015280c8294040c44e40b041c014540074441e000703d92103101055001c0d41210703d40c01c40100480c0b1042c4c3c1c02d8010109045991025613180c1460405d404181034040d00107079202c0c9458801080900c80c4083c2800798613024003980b03030781d04c81d5925403c007001d01c01503804078040c0c00345960000300c003800703820303c050710003016101e020900e0030f03a5841d00c000b540410001ca900500601c00480030841c4503a07204020380b082c070030041e695003a4185850320503e018a6120030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 170497491 1250 170496241 170496251
    0x1060611010b1c0b0a0f020315010f080112110316061d06090a05060901120e0703050c03030f0f0a1b0b15030604051906061d19060501020a08160b0708060a0603 70
    0xb400307503120601c2e0b040d0f64102544014949403540c001c005800460b1540072070600100910035545a204c1e80c5040100c001d0b229600c59418004060341c005c9000d2142e0310b106191a140e41c808266028802949001c00400341c44104603503605040c01c0c510190040d00003e00001612a5200c04000c2c0410301000308642c4107081c4605440000c200440b035004407400b541c4003041e1031403940d0041c014005403c0c1010780074000342058540c00f955034a41d40c402a6064410040f50141500b004401c40d1705510001d00c010f8a406c82c8040940c1003035100c06082403c20281c44044000c000054000c6c03140c8511407400c038585800c00f101c041e4001456890000e100b600441c003488002200028140e0200c07651046181f031440803420b08400a0800794091008014156402c040b00c2e814098290b00c981d0010690120480d0502c26030000c460302802010702582c40703004004041503000c4040c100300034029484081d040050b42d6650050310042e02d00300b01007081e08050120b2480c00f401988060f064074601008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 170498741 1250 170497491 170497519
    0x712060e250e060d09020607020a09050a1119030e0f030c03130506090d15060504020f0405030d0c0c0e13060f0b0a05191806030803240d2102010b0301060611010b 71
    0x9161258510300015950784210003406c64503030f1019180b07240c0e001003138040e00076a2441041c0181038115090403400b883c1c044c00d1020381001c0b81c250791280200c171968014402e5221010340040194408030041072013140c644600090003040104124807404016640b9282410000395038200d1642005208060070300000d002500c4020f41e10310b0464000c0c05142c24102d002d0068402001e0306d8005640043c000107000140000c0440100100c1c4c109a04640d801e19016108403082446000002c001008035a820040e04034000200340d00505900125035008845945100841d0b40e1614407000f65500c03841d0301c201d2072a00240500c01020192040d91200900c00709403210317051180907244101003400e11480e84101507511401c0590780c0324030301030b41d43d04200d1604000e212520b020b03150040304100d609481414001074180030a0b0707201c0958110940a642802160b0010050034803c540d6035012000166500b4040c40c002449030b0349511000b4400454550300b07440c03201060ba4003600900b00203070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 170499991 1250 170498741 170498749
    0x20901120b04111c050304140409150504020f040c08060a0f060512100506040e180a201305010b070201120c0e0d1103030706020c010e010507080712060e250e 69
    0x56846a4800d0a59440300351210000f0b2184081d40120132210450250300e004015000004001303860700003038101c11b9007580004000c2034800303c5070018882c43c801900c6410400464101c070717401030b00c02031aa800301d85446001c5800c0b2030046000300c0004040300140b0241d4100201d0040c040d11031640803000741820154064030601c50f0003800350b0390540717075000523403201440cd4000c4090711009001a030340720b56030142d4131007503a010380f0011f0000600240451410170f00040100c1000d91003072451582c4030340e034007001c0540e03800c407024542c102d84c0b2502d0032402e07a1003a01c1007070302902513a1900d646446440c0001410551448a840b0708145072148480c449601320401d52041e80d0200c96541c011016890003101c41c42c8150301540d01441302050450420000780c001c0c1c4110302103100200a10382682c0361281c00d9660527504240484c4150020a0082d4445c80300355054140c4640c01140e19a5190090303640e904080710b00c1607041400200b07240050010707015000a070401444c200005d10034040002e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 170501241 1250 170499991 170500013
    0x2019050d05120d021306031b0509180403021e0a05070e040302030c010c05030106032315030102070215180102061006032c0109060c26060a1203090302090112 69
    0x458812030303040c6202420410308000b01d00c0c6032440400c11648514100501001942101c00001042000d0000c041086442442440c00813404e0b210100010261584159001d13446a01042d410030000030088103110900c401c00740c0241d1088e801042182140c416510321503d003240b10390501c0d04880084000704e80006450010303a030540309019920f84591809a18521034003c0814080d42041e98181105800c4806141200d145442c144410008000503034200101c5440141040c48100041804034030300f10900c580c42500a0001403401460790006501041b802a0181f90044001080413003402d40e05d00c0300134041000c0c0014140e50425040800203040c060080c3c42c101940c81da820207801d183c0c50b0404201d0860344101315025112404124042e001001058a0690800022250440c403030150020403005c4802c00c1404214545400c0c0c818400291086520410001c00410343c002214101c0512501c2a1215850980b4600c1171005016050b8000110661810a0240492452885 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 170502491 1250 170501241 170501249
    0x615070809150c06150f04050f0712020d0f0207060f060b0714030702091306050714070213140f040b01060207120605040302010905100903030515030a0323072019 71
    0x82c0e4070601c060000000c00c00d018540b94158948200424003d140e540a240200340410950307081c1d00c1a0016400c0c002925000d94940f50640804000103a0261240300c011303402c1200008003520b8068101900c0e015105c00102101b40280d0008002c41080303441c2c030030140c4400c1042c000340f15481c076104100085000d0404c0141c00366650013004841e00f03105108580103554001d150a0590034a5201e16000061480044400c0e0785004c020a60250051701001441e00c104445140780c4040c3c3e900340701d17003100c0300c134042d258150715414141c401e0701500384110f2003a4080341506040b85041d0412241d07088060384540c041d500001f40c00c3c00308402010030307155880e400c80c00c00f00b1503448507d01280140a2048064010f0040c0c84030301150600c503400c1000014040e640c217001c203498451440b000c0ea03152058540e80766100c0741d100e00020b401500841f15001503420b802c24040a0045400b40f03a40c0f00c0764044440380895081d50216482800000c1c04010054407100700403a40d40c03140480d034100c07030b0103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 170503597 1106 170502491 170502499
    0x702060601020a0b150102030c010c0f021504020a0323010507050315090c040905180d020304180b011d0d02041a01080105060c100c03060312080615070809 68
    0x1e18403c0381c50704980062001c0e10b40e13030f0108600803030311690107055000c14800191400303001e100c0d041c0d051003a0b071070f800701540c48840f0080c240141e421003005454101c10078000540c689031058416241d01010411565001d603c910b00b5009400380c0311a040d600b03040410003116406001745000b580c074400d444080f010b4643c00c03c280518201d45070a4100000c0c0f2042100070055041540c110f0000d03030028244c4107210400b581802203080340a4056440003c0800052403034030610b825a070700116040000c000c180d4002808807004507100012042d0312107015080303503203001202c02e507941c0c002c01c03c10103160040402080300038038410603404907101c3e1000240605081c0c088410210b05c40c000f618000d81c0449080700100b601c0ca11860405aa0b0000800050039004800c882e1f544180c69110f440e15102c01041b03a040c4e814840350030310603018130042000402ca181514182c03a000c072 = true := by decide +kernel

theorem cover : BRFrame.Cov 170323741 170503597 := by
  have h0 := BRFrame.cov_init 170323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 170323741 ≤ n) (h2 : n < 170503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
