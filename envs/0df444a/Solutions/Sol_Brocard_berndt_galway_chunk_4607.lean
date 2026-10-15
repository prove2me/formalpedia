-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4607
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:09:43.979787+00:00
-- url     : https://prove2.me/submissions/3a13efec-1c5a-4517-8336-013ed36f5b61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 828417266 ≤ n < 828597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 828418516 1250 828417266 828417269
    0x9060302090c030c03040210121b02061f0b09041b08091203090307063b0705040b03120c0309090f07021515120a05010e0303070f1d012105090106 64
    0xe080e070100007418a00d90365003520301c01c3c014082c0c03840c40c5035641d80c01c1010140d1040c844400b4882404c2820120248500c0351405e403014445d000a0f00000001000e032820300c0041c10205000705881c0a010226190010f050869400510030340c1c840032507500240c087d01103108800d490300140250844000c1c1e019050901400030b54041d1903014010740420344c002e1008492280003540100030724030001c0c10305e80c4440d800522400506980d424202000703501c2041c401024035100314503a2010355001c1090299100801c0300b103408108100c0c0d240c01098560a0099204003070320340210b1021a40780c0d040c41140d42e16040245001c1c40c40c60801e020f0301c080301044d41c416005104040c10803400ca0034040c84039000301c2420a104042a900f842042000c14440041050314052840c0120000703c0074001c5089000342203010707684034075001100030082c0300c524010004110b8210345001d660002d540510450203428602048524134003c4000381d103000e540900460503207000304200e4401c006504c40700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 828419766 1250 828418516 828418519
    0x2030c07031b1a0603011508010b121501060c0c090219020d080f06040c200a0b130b0a0b0d021005190903050c010503090a050102030114091e150307080709060302 71
    0x103005502c410b1880c00c400d5241c000812a44508210465074980d0221950344144014000b0440300142da5503500354000d0b40d84070001071ba4480300e94041e103140001030b008522641e10010181180c40b8192808012010711585040c4008402d0b074074184200c0a4003140030f040f13003000940d656a00c0d01076202c0c1140800410f500140903800910008610880b00580295003110404105403101001c110091580382040410300071051503070b4511840061440d0910300800e800f40502c4107090401c508a4440100b421246441040d4101c00241045140d2031b00b100042a0000e1410415404100302800300f80000e036109006d00421505a9800b02c000e0070b000d600110b40f080070280d265010360b4503407400d0200500700c1e001503102110651180015562100c0f4100841d03400d618107890b05400c83c0e100f0b07081407811492500b4824010300b824006541c11000ea0306071200c03000d610207240c5080507806080e0300c400783c405000c540d055940421881003d07000350400e84402e590744404110042902d440b08a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 828421016 1250 828419766 828419777
    0x10803120705030702060c0c030705070b0304060c17040b06121507020706090315020a020703141b1804031d190806060f180a06030b070c021f09030b091002030c0703 72
    0x281c00584200256800f55007250014041c544801240c1c04032508041d00002d940e2005000e00000720b18100710100060000d20800c0c2d41d04c3c01c080c1401c90030382d002098040280800400705a415692100d403060340941c01c840304c04c1e055121f90f40054002d0802807042615442540401001000a248114090302c195001c84960700d56640040e2007a220503c80501819600807440c8804a0a6002850200f00700d1050360300f400c0d120303503c00100500402c80d40700960f005110340c034128158161084401c44088400d0208051800b00200d024600104018100101c03034602001d9001d041200d8208040028044018440300c41e6400c11825424411401c003485100e02141c45424070112005003030001801407007401d210b42400a007544c0010302002100741c3c0c2d9500c00000302e6115510b540c029410351b55540c441c03104070300420030103030003a6018400100403c14203540d1316410000314001c03a90302c40d01080e034583d14024400e08041442c5003c60311140004104486143c01c0340082c01a203210340c899 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 828422266 1250 828421016 828421021
    0x30e0708190b1b0406021f110904020715380a15020a0c15030b010905060315010e061912020316120e070f050111011103060904050a0b01080312 63
    0x111a690039240c0540400c240c0c80e403400d400881c0302d0842e0540e00450050368484403050b8a8030342d0240c0d0703000c0e50002d001a005950845000003008104e0080380c40740080500002c0010750032082c00d44218071317006100c0c3e80c1c0083c5141c20800034401c4051a0a904081040003884e200c180c00d04140141070704200c22040d1044a10136004203401100f40c840001d4888124281060000072042c00001c0d000001c1d0700c55611040300207016656007801800d441e014121210380f101e40c2c01b0f401d03034030119911414050980d105020702c2d11500e083d03a0740a81d48201e039450081b6480016107181c1e50100c2d40e66000318000507a0060242c3c0c0310380d080b458403084c5c3e0761f44607030781207110b40c403000c80c04150360140040f4003800805011610840130300d80c2d1420f041301c0010710040300c0b400c4d03030749401d806510119941803603200c00c02207586c1040d00050880d031000001c1c06007101c00c902480d044d100003040300703104802400100d014054104007040c0c60b0b0f640101c0b283c100b543c4607418941ea0750049860107a40100c041e00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 828423516 1250 828422266 828422279
    0x90e0c0d030e0f0312090f0a2705070f0c03120906020f0403020a0803030c03011203140a120b010f091a0418090210030605211c03051504020405030d031e0903030e07 72
    0x8044810645d00324020303003400100e408000306c01e4040321070b603a4802a03e510203e016000100034100200104000941c910b0406041e1001d54800501071014005540c0414400350b030000314141009500d8030f880e01c3c4c99802c1c40310010080c0b11040001d4000d034404564a600000b0507001401035900880703003660711690b02d00159682c0d00c4100d07000701d80c01c03005000420030403080c10ba20041d06442414580c60f681c3c61483c0944042d0490b0034182c000880e800f002c00d8001a590ac50307d00000000e00e085e04040c407000801401090f401c0c410413040403103030740c1c00c500b94103000f03015600a400c0d02e00340c059640c42d40001c0500644850741f0203038442d604804031416101d010344118012940f01130000f000d403140c0c02400c408040340000c4065214002e642d070b218804a40641d2100311802c40341c8000829041012205040e40d80c0b070080c003801a4810407080c0950354000802e410060600d00e0701146800513010340c00107032012407801240d0359003001100001c160701a040042c003000128216000c1c1c03a13681c070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 828424766 1250 828423516 828423523
    0x22030b0f01031e020d080d05071806022a060a05041806030c26010f1409012003100503010204231504060c030e0d03081e060a090e0c0d030e0f03 63
    0x20000301194110f40e1104000552a4641654140003d18909400445844009807030b488402e50310402c55491080100b142e40000401003080400a4541c90071401c118020759074402d001815508410f86003410855481c102c0a00c81c860f00e1302510454403112039080103003040d001800f80c04401d0342030b01280f40003102c0c03500c100c004880e04000c038010542c1c40c10f1088460154207a01c1c15860b0450b0060194034a082400f840021203003181000070310340d45885921444403030142001000340d041a0712035004100d078038110080012030f0701700d26541e85c80b1240365a048000540c0095015400400d0008202c0f2405019800b4020401c61980d0900e81900c204222403180d18145000043c0a2206004481c0300f980340760041c2d0310034200b401c0580c6800000898000d045101140010035190810224420003d0740e029681420000c0140d982400d4000a255070441e001c0c02c0740c06540c520a40000300d10400130304058000140481101c412513003070041c03c0c440590410350103203c820104074801c2c03c001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 828426016 1250 828424766 828424769
    0x50603030d0f1b030e0d140d050c121f1e090b010512041b060309171c020d020307020f07080d08040c03060e0f0d02030a0801120204092109050906032122030b0f01 71
    0x503d1f24501d4145000d051000034030000d042d02400c1c9100b84410985c414580d2070035030264041d9502c0340c45440c2d85000d079008040154100520010100c0c5904081c80c98280044043c3c4076140c902142181112004035110301030a016a0040c225800900c000d01002d802081c0031410901f22030a1080d48980081c0e00f51002014010300034800c1c4110f4100110361a005410380502d07654500340222120007403681030760000307040107981c1c5600005000c041e940402503d40c0d644c16203006025418900300940703465451031142602030001712000a03080000040c202d40103142e000710200005a003401e421907075041d506100aa25201c0c550001140318000003d4880e8000c0d507544183c202d80c02c082c400d080c90302d4a040101d811a44800042c40041d00b03d040282181d6035000300345240d0502208000c046c102c440c0e01860040d207404040c018030340c8002c1806d1016004203c90842c03a00000c500044079403240d000780d8000d175801c000501d001c1940e03845100c01224011988084280c60300d06a0300b00d80d035002e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 828427266 1250 828426016 828426047
    0x2105030a0c030e150318070f1d0109110414010e06040e100b041503020d0b04020a080a110a090e07110d2d0f180503060c0904050a050603030d0f1b030e0d 67
    0x1440002e0201900300105030640c902d11b4195004103645854a4108141c903801802c1d0f084040601402030000108504d8010a1890070600803038200d800c80001c948150700544203495900e050700c04107039002e44800b014148000d400c6982d038a40d185480030007000300b0f42d02107200c0344a80c800003944040c5c450a0360103440341450100d020705620030043c1c3c002e40c0001200f4040c551101d401648556492029212903543e17a140ca100030301d85020081e045a1400c26a03c0d0303248800d00070402000e50201c500010b03500030100d01061038171880020340b03510b80542040c200c1352261150284000341d0001c20401c204400095012a41288030390031080580000707400c00005000200410b100c0c1d1017410910620a41c00050044a64440f0701090611301d00302c84a41c000d4400141c0c201440c10303e03204a0340d01c02241e060400040c2040000680c0341d1044400040095484c1c0104004000031644089a412134015503017420803056003002d8050603e03000740041d140100d240c1102041e0049201450320b404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 828428516 1250 828427266 828427309
    0xb01080402090604150306020703091502192a0f051e0d08091305010807060f08040c0501080a0f02190f090305070b0322060f0c0201020901092105030a0c030e 69
    0x21920180001803004505c03807000001e10850010100b03c103440205203042c02a60b03841040c074246203040c032009011100700821940004a10340049035881e00400d1115440042202d441c0c03242d08203421038021a0301c0d645582a881c0c800010100d24403919003080300c40569075809007c44c213030f6044009005d000c10440d00181c045200030006072040b0001d03e180340008003592540c482040c0e410085031026000808181e0000710140705207504400c0e00d140b031008528102825103803543d11502d03654014840c69040c051600301180740c0c03101640146d034030b04a0086085442e200c20410050410b4020440a00403a03900c42e0003611b580d115010010039250070000500c0c505141c0444138801e40d20051148040000c0e100d02000301d0312403590340030046802060080349020071070240b401110155220001960710421103100140d0304440c0e80c01c100d0b50140b1004c040154501150202c541d18400000c00501002039031b09402504842030480c1e4070b0282e030ba03c007030030140e0134180030485450051207401c0c01c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 828429766 1250 828428516 828428521
    0x40905101d070e010521061813020f041e05070302310504060e150a03020d03020a0b0f130204270305041806060503040206030a1e09031101020f0720130506040b0108040209 75
    0x4014840c1c1d0000800f4080c80710480c8031804230300b488041503c0440380420365081c2d603015454070307021000c1036100842d42041042c555858050120455515016030207444800146c40309000782c0c155010180c0546000240780a02003080b028201c0b0b204041c0d0714048005008a03040c00c05100790400d5811440910401e601c0d0380b400007216582000c0c0180d84140c0d01c100100068880e040b640c82240e120b0b0300148900d003280c4c40c104000010051141000207072107010407070704005100401b444542c045c1e900146036001d21001c9003450031480c0007a4140f6420034824000c260303008004000300c0e140010f1804a0101c44079010302034178101c0c454000080d030180042009458410019074206074169030006080c4c0207030716108035407190009519010b5581c0c4d9800d905150700110003507100805100214903160500c40030704014040d01c14054031102c100049014211005907a80c104000020900e29403540f4039800307500a80400c0700d45034040e80c10711003604415400f6014050103140d004020960700e9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 828431016 1250 828429766 828429817
    0x803191a06040b1605100b1c0c0605072f1002010e0d0e030c0a0303020c3a0302031213110402070c0902090109051507021c08040905101d070e0105 64
    0x19081103d031103440003240a525000502e08000113400990840c0c4046203107100070f41041140b065a01c040923204d2142000140002c1074001c2001c103441d041e041550301c40816062002211007040050350303410310701c510050043d80040402d8031450404940c405101e94101000303e09840c0c03400109486a8460015034a04501a425944036024040c04031400c1150104c00a000c0c0081588241c0258004030034100311400c290f4140c6041e1007412000303001014a0021008087c00c0c0100c028443c9445041d0b10401c1610070320450b0000922216020143c0c141040d00c40120500c85404a418441031440d10310141068000c0d81c000079080303094104114a44520180650712901c90941004010700f0041556651521002401054056050f4695409106000000641408101480220700402d400050000003214241c443d10302011410342c8451140d109107816a0300001500da9031a0f51481010400210180c4540355540d100209080a100191114410340f4008083c0c0c002d8245c0380e9103039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 828432266 1250 828431016 828431039
    0x30f04020d02040507030f060503240915042f011d030705060721021515031203010905040c05150409052a070b0615030601030e0a0803191a0604 63
    0x4503001038450561070704075900042c111030701100c1c5140070a9071030b0750042c40b00071071707214039005024240c004207075450021244442c80c00105008811803440b400001d040c03840140b102d100910200203120042d400c161038516005080d1020b070401404884030b40110340f20100f040b8152040068641a8820a482c0c50510740c0120310782d03085805200d54100081c2c0351310f8401c014003105024400c12411101c1001960207414040120fa0301190703c0000310355481c641d08032819800022001000b40d00e8404d4101186c1001c50303850b60090040d030044000180001c1c15044184034a104046a8050607141d5041101c105901224134a0700d410500060100c029179038130198010400202c4c0104034551543c00c042c07545c1402d0300200e8800350100f8002c040003010811b69820074400c61b04800c800613910141c0c4007d01000307084604041e1200010946010140722101001344c014801c5a03481c0782c1040c1031a03d0305011643e1003503040c07400d030040c1c80c11070a2140c40c5200a800404040c5414649140e42c1c14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 828433516 1250 828432266 828432271
    0x70305100608040c0e070306060216050a05122112070f0203300703090b2a070609050a030e030c0108010503030f0a021e0706030609050402100f0216120b0c0a05030f 72
    0x4200c0310341900421040b0042d40c0d040d206c0c0c500c80d980031801c1414100000c1c1440c90403560b015503410700b60000d1090369101203030641581c0c0e09503009911000030710b90280c07030302d40880302a4000c0400c4d040ca101040301c2c000e0050209203e0340c0c540c0c01c800d4448a4007290401d07075100c200390040c0c0040c00600840ea138914071a81c036031440d00c0000c1c00410061031500150341ca00f50394607070109a488450804101032044405c0d070000009015450080100381c02c02e000700e40400300348007001e000040010400040d5445525419009011103612550380d10340500881042400300340300703105200c14020f00d5807151803524140c0710054080c40c24a420306c0e5110380039410103030060f800d601503401c00d1030520030360704491040342035030030003e0084074900007014089507241e0b00b042e066241010100409600e840d11204c0d028806490440105004000200d01f0058805498110a50500c0002070a10011000c8540c6140030380c29403103007510ba90807003110394450340c10400042002480003032a00c0c800345055a6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 828434766 1250 828433516 828433523
    0x1806091208091f02181507050105330d051005180c06090402071e0804030b011406090d0602041706270a0b04020f0a030b070e030705010504120c0807030f060507030510060804 76
    0x2101c2c4e9890301d0004405500c0c03103031071922841b8045010003d1100074003640d03411000d0502c03d49220664841d1070034a1110003241c0e8071a10200500403181c1d622283d244410158100c01620400025410031401800d420341d14040c0300d5402c0301700070060003004034070302d24000780c000d107180c1c03604402c3c0051202940100c1d1003564411100c0d212544140164095192082e1007051015500c03400c4d8a40030301d0080060300200b0f41c2c0004040300300c0294607198100c0f50307514003c0b00c58014114180ca008806413003280c00106e50444c0300c2340440c204090020305c0a01a4036281c0c0100445100a54241060b52102d401040c2e1a4061614900800c00490301c107078110f0f001071300e0000d654007d4004142c000002d80c3c400c0310340c00046000c00000755031088030b0300c03401c0f0002c402178404d1514200009081c2c3c00f49024580ca9074903002180702c00c2104036a0240003c00090381a14000c0355242041c02000080030803ea0b91203007490001155103100b8071680d0300c0340400008a4020504241080ba07100100130000c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 828436016 1250 828434766 828434797
    0x1b1b10020a300603140d02010c0507060911060d06031e0c0e07020c0d0c090b03060c0f0c010b1e10030207020303160312050f10050301020c03030a1806091208091f02 72
    0xb1031692a190044001440c054100b2200884030708160a19141000c480b0004591500300510b40c41d035401000c4410164108030080f91040c0c040c24051010b034000800550321170400950b6404a50b81ea8100b101141d000d040030100808401a41c91144a0316450091a0341c0b002c0d041441031048908440e9005000c03807049400002141010034100030b4070210640d0885c61aa40400016100e400303941044401500a00b0340c5013000a9040183e005819080036140d1700880c0302d5009000c250702c00d401141f03005081c1c860450b6a031b1055054a608004841d00651200c42100c464038028005c40e03d515074040c00852402141c0d601321180407100107403c40130000e0309006660364007950300413980a143c0380c0303000038914102a21400914406a48580c2c000d900620030b007890050084207481d0710200300c000100d5401c2c0205450500b4540a900c000c00302841e10741100240107042c4208114041c0d02e0b1513281c6030b030300c6000c86580d503003100201c04018480b0041c1c0d103000050300340e00a02582101c81000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 828437266 1250 828436016 828436097
    0xb1213050f0a03050d0506030a03020604020f0f1c120507050c09040f02061803071403100e120a0203131a0304020f040618050f0f010e0f1b1b10020a 65
    0xc0c20600b41d4a81030300042c03800700b00c95060031600c0c4162504190101c1c02480203900c240d4010b526480010000ba12130303d804500411a0b80f58141407a440d860000c215501c0080903101b041d10005c1e4810742034902e0000a140c84849500900031248181d40160003000d00e43d5071001000517803075000f00110340c0711518094880058584c000a007145d8258034507800c440c181c0701d200b03261401d825a0b000b00c2c0e0400445007510b40700e40b00880c40d084400200d900c0800e50703800b0040343e280360501030307548504018000100ba4084c2540440a4442411004201d01c552a40d458065410031110000401100f4040001c200145404260340244142c09480407482c680c1e2541d490b2190b4603051688216503880340e04004003580090406a403121500c2d08800c0300d94180320512031369070b1000305502c0d555040c0e0000701e040b0002c401e0540701545800c500c0d1036907a042c003000089422880384982e800b80d2048030300c04048400c890094440c080181d42c0c852a82c0c001d85800e6091980030100f08406880d43c8030380 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 828438516 1250 828437266 828437293
    0x50720150411030c0603010524040b16050705090c1801030603080c0a0326040b0a0923101a010e13050103030c020108010803090108060f040f0c0e03070b121305 70
    0x41072085000c1d0310340b40100d0202d40103042c14112a009041d206003000c10045c015036803090440d804120000c08080f02c10506440744840c1480f950b0407400300280046440c012903c20070881c13100d058030039016600c40d5540c2d0018011201400c1d500c000105005000c1800c2500b07200f142c0d8521420145000b04c0e19550300d8840c40400e0b442070480140300d0300116010b00c1411b4020240204198207480c00000c0303c908183c4140c00030790054001466105490f01250000036190054120250071510340010b030070301e411074080f00068104640c2c0441c01203d0070100941920b01c034009001200c1c54144610161101c011503541017401c00141e4040824820030401c0000c80c411a80a540b20b500c03900607092b207a00016154030301c16400b00c06964070400c00e181c0280d0744100400d4200e8010b90700003918a400400260142c40351000c00302455160008000b041940810a02c0d0122404d4080d100100d031101100344140c0300e04a49414a40611404202c9100f0300c0c45c403208545008009649074502d0104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 828439766 1250 828438516 828438553
    0xf0305070204090c090f0e160303111509010b0f01050a0e04150815071b0c092a02060403030b0604030b16020f070e06010306141c11031915050720 64
    0x1040617054564514024507402e11a116483c83d09030204c0050a40d101080e40c5984101c0a0f80001030810400441c4c488a030b620030418000d41500c810440c0ca41e91030110070030b80c0200000c4001c03903c203080d018600303240c9500540454100c0d1260b41e035003005418040c03084c00050149804c0003500004580d03c0010441d1040c42550141c0b403554880c03410500b840c440007407562901c078166644140c2c0301c020800c001401741ca070f28001c0711100b400c08070b42c2044034034110030580907082d0941a040a02e03541d0b15401640400d0881c07056210352001c1150b05104818040d19004d140802088040803802240008018038200c80101c8190710403210001c8002e00e505080c8200796022445604200e03081c03080070342c0c050203074001070103c070328014030b862400078000350f40700540c500440d400c0740d1000402810300c01c0d2040c00764510307000a002c5984000641550400e40800c0390b02c01d1b45e0000d40742900b5240306411b03003e5039008081d55560510300030980c28588180d25004c158241c09840384e10709800c8040c000b0b1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 828441016 1250 828439766 828439769
    0x220302030904020a081b1306120603021c020120030a05070813061106240d0204090c12060f0e030708030a180c0e090c1509060f161b030f0305070204090c 67
    0x17942d4000c05820701302d641c18000031031130259440e250010300880c4000c0c51111000c3c03045666a00c1d11800000401c1e18074802410160001380d00988180000301c40002101c2440040ca03100303076508443c0e1141d4074854130b14101c0c9240560034030782041100c10050f40c45103014242c0c560084c0c40e030500d0100d00380c03c086c00070b2a1941c801c4002c02e29003030312219100d40510805078440300448082c2103040e06040354190f0001c41c9540148a00c1340e40d5010000e5442c1c0f944020261540007010400c61500d869140ca0444103d01c000c0718000c1c2040b8210754280c42c24020801140b4403e0300a6052040c281e82d519040d80009010707280711651190304c0404240c42d50220701d90316000720313000c0134640c0c10109034080d0703a4401082c16030f0780c4e0f1000400e0801522034001e80b0030200540d5001c55103640020001451612486c65800e0b240100405c1c8c285288407480070000340e06215a4201913410888100c1c0103148410740310107895450001200ca010900a100400f00340d8802480096041e40380d98410f044130016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 828442266 1250 828441016 828441037
    0xb060a030f06050901080609060c25080c01141b090604050907050c06190f0b0901140109180b0414040305032a0313050606030c060714070f03060209011722030203090402 74
    0x1805608c40c0244038585c0c108440c0f040707061401034020400c201240035045c00c00b108100201401c000c0c405001c05980c490304403500240039461110800d42590142030710400d8100710075043d01c0f044090400201d490142020b015103081602c1c182c104000c460000700900c045c44000c011901c04180140001c920807102984100d805100761003080080300c00b0107030000300e00351621404e000c0b82d03655420301c00d04491105c125200c00242d00720041b071320929a80d000400c031654071040c42c1140c064070f800a240c1100141c408011403c1d2105107142d20b500299000340c0407030342c1040415801124100c0c85444501540e01c0341054185400000c81d00768000c40e929030401440c0c0c0c050700b0411005103d1250000000c4008220308518040014070b1845020b000070903000c0e05191101a501c018005600107103051400c0b6203140c0c0d0b0b07909000c80070b980100c070118002105c550380c1e8001450034920090040100c0110781c00d540510036290152940c03040010340540c8030138041c015032582c584c00201800b068 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 828443516 1250 828442266 828442273
    0xf060f07050714030c090a0b03011406100f0503011401020a240609020a1d0406051002030d0c091401030f14011202040f020c0624031c120b060a030f0605090108 70
    0x15042903410400580c1141c0400b0b641d4094898030f42e580010344a1038404200c2e80026140c841c21005002009101125505542820080c0c8a0300400068040c4114810781c1c9034941c0184184048480d000181c081001060052005000d64480d810115050345018012283c141005441c0e42d170070310121902030b4500c464a20065031403299140030300c2c0000c0c4010744013903003010001200500b070401500d2185040a00c040a02d0440b0b541d039400100c018000a08542210134900c90001d403254001c2a08040d0039080c111240d40451041c0c100004607207410803000e1615040900440152440300544240340d6120200c45d803642d800f81d04898000d000081248c1d445160b244188800e8842c8009440e0505105210603003440e04040344260740044c24400541e80c0050b940428a0404051000d2940511840664200345680c490303031414400c800d604e48000d22003401104a05035402400f01c940c20200900c403455486010750000710004050540200342203172140086001e441090380075800503032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 828444766 1250 828443516 828443527
    0x40b0406110c0f01030f02070b090c01110703020d0b040f1505010f170a1e060501080604021c0f0311010f0504150c051204120909020c1615080a0203060f060f 69
    0x541101009000c0909480a442c260181ca80080d0480c44500c2c20039040c0354813402082c913401800d9045440080d48442c4030a01070900b8801250354811408109021a690080500480340000351120403643d000380030740d48400700d40d03480c1035000780f028100b2a11782070701f104000c000502c0300880460b014055a4002402e62415400b246e000729182d0080c000051508042940c40c80049000000d5039086546030307441c50f11603480200c2d10566201c0c044d041918100c0041203a00c0085101d6005a0003116110792030840c00c0e208400507408404024520b20700a415080024003a1044034a0408880000a400d0b600c60508a098510843e4111420304510800c0f411034501840b0382a08102645441410f1001c0d0804000500c0f07409000900203003078040c0b0b210314184c0f003880c0100c0070300214071066488814219040e075444003c3c041c00b0b003450410071030200d03024005016441420b8455039500c9003075220300412030001e503c054201340d00902105d0311550b264458500410f00403207200d1080e692030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 828446016 1250 828444766 828444779
    0xc11060a0c0f090b031303051c091b080606210111030906010803030115111207140705030105070f031a0303030709030302070e1603050a0f051f0e06060a0c08040803040b04 75
    0x4034440d0071110901c41d00403c18000d0245140c203803640002c5011031010710b100d041c03c050301c95000d240040c201d44078180c00201d50b03a40d11600450025071180044200501e0410010090203280380100c4509504c6503001aa461801034a08400840c1d51112102c4000003400c0050035a4914136852019400020621241c0d000801000340140401e4002d1803c6504220381c03220a104103440c000d0801441034101da10b0200203000041e06082c0c96400a5904c1050340752240002600103240d850b2401002c00c0000e0505044c02042d02c00c3c2c00e2035582c0c262500841c8429401017150082c403040c207803e184100900d5440c108001d500880c196164103c11a10f1450001d02d03040f030a8100c010007a14080c00c1c00001c12204a80100d0b100f000e050101e1250790b0304d0141e0004010706c0b40540d041c24200410702c8064030109912616102c0302600d050203040e00c0341d51040020a0503190181c012004010342881c240c03288000004291180402a161995880ea010702e076400a400000102a001408002d030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 828447266 1250 828446016 828446027
    0x3051308100204061b03020a02120f03030114040b01030b011209060605030114190e2d010f020c0c01020a0c27020705030301091d0619060812092b0201030c11060a0c 72
    0xc0403c103581c0c91741220490390000d460748000e400090040b40c10340e080c80c0010030b06008000f03442c0c694508498407981e41c2c404c0d5000d4802800f100c075000742d03e0302c0c441c10f206521134000d442c220141a11100c89441402601c0030003004021819590259260808200b039a03080c000c1b2184a40c4000d51203144e8200404018081c5003041e00400d1024600340c42500d9810700400e15540718162142c1001d000c1502055460b940c660820401086500c4c010122003800042d078090304040b454601200d54040190340160ba548003d0314018040d030032101401c100c560000d120400c0d600a511030001c010107000501a0140e0b000900200c942e50004001030160b04404e1184040d942c040c5454150000800000192500005002d2007002d240002c9201850b94007500003000424110301115130b80c448a00390400181c03c81003000e8400d840c03000c1c4210100d20204050030f19591046c4401000a16650055008015a510709424403401090060b41d60b1800c2c0701051040d8404503000c141c00880d000001d01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 828448516 1250 828447266 828447287
    0x32a09040f0213270b010306050d0b010807080304121101050903060103060f1401060e010305090f032a0106061713020d0f1202120405010809190c080106080c0d0305130810020406 78
    0x15581300020542001101c5424240070504202c00000340504000c401207000c4c2c8002c0d0402500900c04d0040c842c100100456418101d89000080d1b88201c0d40f51942e1a4580c0718034400ca0507070000c041880800314010014080e00307036505050403441c10550002003824a0400d0303000744c0301c5a42c0d074403e900d0240300a0054800e40100c04204405642c1040c4001d0022000050890304242d51600003135000c810800a17400060402e1007181d84915804200c01c1d103801480ac03108645210019071102c550a050203441c042d200345031178101c090000540300000030b1071300070f181181c241c034082d4282c2c0c0941c58090168013018065650162011102d05100e0074000420780c0070800c55100300401840c1080380019501a15000d1901d110241c035500e0b00342e03241050b511210710390700340441e841a00b0011000c0d4450300b1034240170300a0000310764500c152500c440840c0e00395600101500d40d82e10009105000400d42400300c000c2482070141c40e02803031860b141c1c2d0022007608840d4001014041c041e00241d0078403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 828449766 1250 828448516 828448529
    0xa200f150c0708060a062403050402040b1c020109080a0b071d1903050c0907051c020f0f071e1a06010c0512221508041a0a1a0402032a09040f0213 64
    0x100c87c5614110020804171581c1d00d08410950740e031010804559480d041340828100081c5540002c02c190403c2a8101c0c2070140203e0105018200c00a41f6120119040602e01c0d00509494416030744c6070003e0b51520b0703402c0c8595a80f206003007007000f0301c3d50b10500d001c0140b0114002d840c11417421850b1481c9000b402d120058807a070b42241c01c010b0023036404402c0703c00b00510403081c030036100511199040a4040c0001590604101045c40551410600082d1000500035580e06101d064210707030300b450721005158060244070b84c10000c42042e520406042d500014103140004580e440c43e1201c906240040f041766104000c0060606542403d40c0e00702451004201140c0f0029464955890350f406c4180d100d0505002081c8002424410740405803032500002e180d0401a615001c082203005000711046441141104400b641143c00e151090f0b0b8410700c02e2500035120400b81411407050000119800040700074204420041500c5600800c1d0240c0802a405601c609400003841100d03c115007018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 828451016 1250 828449766 828449789
    0x606072001140909010308090a0f0e090606012c010e060a0801090c050c191106030c090103050a020304200f06181302070309032d050a200f150c0708060a06 68
    0xf280aa0b0b504400604483e403081d40c881c0e68041000c040752495840350300c200115180d03040001611248a4161032040482d04140e45c0c4503a2000c00540c2d00d044010a4034080c020b80d451115104101d4141800714100141001821854240c1c0012095130100c101040011040e00c010814204240a0503d404426043c03203801d2039109260f0707564a0507607842140218601d2600c0c1d10078015803080d90707583d00f140030700403a42d245006410303c0080e5208101f42d43c0000d1a000000c0c1c02c2032098400e8901036030380030341e035910070380ba41003110480050003c15443d4841c40002c100300c0c41b507540c00b006000740070348007804a07801c1207203008100c80c1d003001081081005d1b004200728400a40e1041005007540d42c00390000088840103030001512000c4003020f490124402d0407080103200c00001c225807840e21880144110a6403401e481c1e20810040084a030484450803651400e803070603208000c20700003101c5c41a824582e02a0545240180c1980301010300d40003c030901000c0e080c1c0380544c2000d40f5421800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 828452266 1250 828451016 828451027
    0x50109021f12050705070f0c0503030310170c13020a090e071d0d0b0103080f090d03110124150e040609060312031109010e01020a12080a0f061409060607200114 70
    0x240040c41003140007807d0034a16101142000344259489000d0300c8040e007206d07100e242868915220304085d005841c02c1d2401990900c051020000d04a15440f00c00b030311110325800c0540e0b03450065084034140c03100380100b500c00841c2c10f0485508880c480c00d5107075145042c0002408041895130411340e482402032144501d44d10106649000d010304403540300b202c3c99602c640e032350580245405165045603020200c400c440f01416032150f050610044400007c102c1a052601d01916a410b105482c00f081d00d202f00c0e080295502403041050054006d0070400d0004880000140c200c440ca031700450142c507600d41e4148280082c0c42d8444407a402c8034201040503402861a2208074051010501c0c1080340782c603010040341e482880103c0c10980e221701c07146604e81041d503014014481c21246448400d20301211030508a0980c042c502c1245c0620040642d0000d105081c0481d00b00024043c40d00304404100140025964010200c041401101038808a041c00e0740018400d94000d203409410180a010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 828453516 1250 828452266 828452281
    0x1b1003230a0f09111219030801061209050a0303020c070e09030a090602030a020712020d0b1009050c040e040215040513090b060612060f0103061a0415030c08070309050109021f1205 79
    0x10100f000c1c000c5690a0051603203415040c9811809042000d006c0c45200d0744004254210000c41d050315481d40300c0f0f04c500980561180d04031081c1c94005403440c2e00030104400030134000e500074612282003005a8155603220083d40e44a00b0041e00c9054081e0310008050612650107160000544010700c080c51030000f1000c00255952400d00880e26032940c00ca00178800c66484e500120509a8840584441c1d46488855942589058802d19665500f090700140140404034119001d4849080d00324001d074866800b0300440001000741801080360801001c2030654403107601004018015002090071102482d00305902c42c400b8003004d019003418840145000e00a064060340480d0680700c0f0f1002d41d500c0c070300403006040698012050300c0034440039103d440c0c0802008000350342c84c201181e408495a5034007101203e00c100d4030710001404490126464030322031740000b28464080c400118000140e42c0000c0c02c5040c4213051510f04c0e40041040705551a00032402c00c248401018042006107013410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 828454766 1250 828453516 828453533
    0x5070512040b0604020409090807200307061b21090f03080304060c031104080705090f0403080106050d090203010507030b120c03060c0a02010e1510081b1003230a0f09 73
    0x1800202000c2c070010020307003140c9840d41030350024440d0034401c0c1305c41e0318242400700c280d600c1441e06513031801c00c60966405460600035a04e1010601030003c2011910740041104c44107040200c0c60204042000e807103000c42c980c1e0502246200e080b006020501c80c00c0741d00907000700030b50ba2100508103840c0c02d040021450000c20f60340d1058009002003918041c0384022002007028042c155a00d01000c100859413020000381c507000c0e50310944102c4529241c544041100b00e00495005001404410041c01014400c0014110030721586202085d900401d9000030309440c41100d0410010380d80e003102614900d0415515543c04501034040d107101c481c0c10740402e898500080960302001e10004800c44054401d5000c0900b00c202c020030340d2100383d080040d85101ca0340588016081400000000c40c0c001e0010a842209440352250181d18a10300310622582d9250300b0101e20901da60741d8251921409402401d01505070000201d072098038204110740110b0745c0c60b081242402d8034040700400001d0908 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 828456016 1250 828454766 828454771
    0x1503050c04231e01020d03110306012007091b0c0c091d0703050601080d08100e060d0813031b060e0f04150602030a0207332c0405070512 60
    0x440300d0b09001c1510220344a1070310007060501c0e40005004031403100541c08040d070f00903841c41c240d00b0f850340c0c4414104200c056825903c449940002e00f040031038455030140d00b001920505008880541c80380c6d40c07071000d007410b0465002c180c0d200d464003424103d55411026258018016003000700325500c003525200039480e800e004901c0c0c03155444115101c0502c00342d10b29241000c0d140c00b01c4000a450f0302d40f542c0c4850080c86907644600c078213001e0a0217140200c0c040d41c4a0035003011320640341d5160a80340c0e0642c4201a001c40c0d003143d1403420100104048500500c8415107460007072800314030790f00c5c20109501b20b000500910010714601402456400035120140c620304070342140c010305480740000e0003889210201c51003182c15010001d000c075004000b511001503690241c0321490382e90000743c041209581c208688a2849c10181200c0c401d241d0800e146003c410300d4143c1e040c04000c0313104119000c906041e28008207003020024446c2c41c01d0700803a070f07104405140090809142c0c40c4601398a1102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 828457266 1250 828456016 828456029
    0x50301270605030706020703020a120503030a0f09060203071707030e0c01140f130306050c0f031306150b0c1e03070f050a061107050606091b071403030405071503050c04 74
    0x411202400359251078001502801c4024207403140b442e0303113140181d0307118228030049001c2c0e81200e06c0015080c200303043d00c0b58100d4014018600c0e44e5070301c8120800074074550842c460300c295620114404151244003440c404d0156448800402d0150201108015002041d820400d8241000405243c0c0040344c0c44140341d50a09014840010000d0710f09518051110074103100d0304c01241c038140801042401c0c0080b00d0044508101c00e4403103240c801c49502c15a001e0703945031001000803404c40c9a40e8141c402c0140e0103a1000512940395032507462010000354403140c0300147c0801d0040ea1304d60244202120440000451800f907002d0303520fa9030300e038000c420024028914420655040c01000e0026100c5942c0c4a0340070010603070f01346900020707038000c0b62054400d44941000200030b41001120a401200c103070890b142c110340c410b07a84954503880b40408682c643d001c042030800965080010310700462040000d8900b06d82040a61810181c5480031f2030205400d00041c088000e16030310841d4180c989 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 828458516 1250 828457266 828457319
    0xc0306090d1103120720030708181c14012301050f0d05070806070f02010c02060417040803030901020903010506150f0a0908061602070801090201050414010e0d030507030f050301 78
    0xb11078040c02e602a41c00fa01d00300301328500801c00e050383e00503103001001c51a0742e04104c504408000306c554a003e408002000c0345002c010b00640c03000307001400800c2c140002e100903072011030b21808801e19544203c044403082e200c100d601c0141c9400380500e141c20403001e000c10352503101642c1d8000c940b0404bc4180b1b402107043c0e514203215900c1c2e0940c520000754126003282c18065640c1c5207641e80d80c004a41c240c0000da503c400007182c241c4180035124120003141e008100320b84442d140d240e00007138926142e02c00c00200304000204602d00b80065441107903594001030701c0311303507000a00d401d4807001007a4500c11203856000309107110114040c0d80400140c110311742e464034011501940e150a403038000c54510f10400303040016100450105145d9090150b099805165551043c2402c1c5d40000900a011500901061000c49800d000314402039105240c040060750312540803a05800002d01c013030f000150700150200500d80c0040c4902d07a14007007850010329540c500301aaa00c10032002c00130100006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 828459766 1250 828458516 828458537
    0xc09040303090f03090e0f0f1609080d090f05030606030604110f15221505071a0c0d05010b03011a280f08060901031a0702010f140403020c0306090d 65
    0x620070760198100a0780031020107410f0005007400340c401c009078840c4401c030140c42400281100f00c65088103000e80080c040c0c900c45030722590740382c44401a00700002010000e0308000056003090400c0410150045612007019060070b0418020096025401003402a4000720500600741c800140031584160450301c40c580504200d4006a411204100c4050b03210b00248000c205414801004202e41c05004485443c010b0b4038a8081d1078400c010300c6000c03006542e500a081c0c0c40b80c0914004c06d4400c0c465000b4500c3c040118500d000d1100f415075082c18001c20120300021101000c1c410180174110001b80d450540d85000010300ca14070160100300c001c8070300810444298507036912240310780741988400c0c0d90308000d8200014082c0309111360100006020030f0125020341070241c5d00c203040c0c940000d00700c3c0c0c0c0900703815080441110050301c21021036580e070582415101e240e10a600414400011003100d41c1000c0c02e00030302e04a48264260b03c02d4200105010400301c0000c2c440c3d01d024250305003003000c007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 828461016 1250 828459766 828459773
    0x50a0603030c02130f0204090b0108060406050a050607030507140a0215040803030a0f0b18100f031502030712020705070617131401020c251725030206070b040b070c02030c0904 77
    0x141814170444c03418a001140110f0742c41c05035040101024001e036200d640c5640d4150030041610740c0d44c8111034202078849002d01c15030a104004120003806401c04034a003041e640d9a000c101c1c4440d010031ba00c1034200c91402030841c80c1c846644d401300c4100c5040307a1304050a02c4651500e91201800d210801d0b650780369031400084080d00000b1900340000d054107003007a4414410204200110356800001c5c2c845540858214500b520750030a49400c00c4001113280814151240298005030064062041151084d080d080c01da0005100d2a407040c005031078000c0c035009000e010202e00009900313031040e0101c20400488941014005040d402c85a20007259109041440c0244100f080850b44c03030042045004c15541024850300100001d0001401c40f80d60340d03090408100c14040c206001c1c4d40240340055414110307044c403120301855441c000c01c14950b4950014030140c0c000c00b07040b103000005004200a00001003030007540441e4508082818103a2a400203488603050040c10b80b1030407411001c00c0c1070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 828462266 1250 828461016 828461021
    0x5010902270c0a1b050105060a09020f0301230a0602070501022a01030b1c0b10060509060f030603150f070206010f060e040e030904050f0924041e0203010f020d050a0603030c0213 78
    0x703c8040c03000e0f0131415070617042c69400b8080481d24980581420a000103510b02c0901c2143c05502d0044034144c00c60742041c44480c400e0221100400c149002c0c0b06848003590785402d005001800240c0082441a01c2c100c00603041007040c1894000c200803039032188807654000384405040b800e007440c00103500d01102c40041c6c5d071260f812100c2e480700c1804c0303011002042100c00310507004520100c015102142e0b02c650441d0346114000c1e000350820780510078100360b421010050754001d60018140c0704203d43c031021621407500122030140712111040c2c14403000e0794040c0240b03809070210700c032250680b5040003000303000070415401031401103580300b80e6121400030500598115102c001c0040c8201e050240d0802c030b103218281c3c0c14008034010130035800340207903401c0c0c0d8450564400e0910201103542da61541404c005400b800a2040d000350310f613000c0140c1c3c0070300c00c14510240411006884a007005c3c0828200d4000510f40800c051a0600500c08603401213403186645038102c0b0010311001e5100b0300c6001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 828463516 1250 828462266 828462287
    0x904020f031e070f0803090f060d06082b08070203030712060e10080d1704170904290307080a0602091507150b19062a05010902270c0a 59
    0x14544055009515061010030307240f0445200078821015903071244180d41e00c80c816468202e40c030a044000700e10950074000c1c0a021120241c507800038003642d6031444141842c1d110502e1a4910303100c0c2441600f40340c401241e4803044019860400080d161004010b54cc921020305000c0900c11212200c450220320390300805c002e484025607000850500018150600700107000d15003080c040c10041c0c070318082c0300c0c42003115580f481064100c80c035151500c5a8280c440300201d02c00344600c00300000300b51911180100d05440da0001501000b001603e41e11400b00744a003c903603480780c1c00c140000c000300600020213003141ea401c83d000580d03600c030340b10000764445c0c242801c803605007002090070401d104100203040c5d000c4032003000900180c00084d00300542d0a074411880f400c440d540d28414000d041c85044450130500380c44180e02550300c0d050100390040000f40341c007101c2a0b91182c0c012000c50178903101030140d41045a031491401d0720010014240000010108024a5030101c2d46512152140310100e8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 828464766 1250 828463516 828463543
    0x10920071502031f1805090f030406120e0d120e070503030f0a03180c060306060908190303021b03070c17100510030b0f15010f05090d0c051002030a08060f0904020f03 73
    0x40c00d5a0314000e10f584919502540e00702d003440c3c400007647c00400804d440d0807003146440034510f02402c1040958140311404140507405030340e81c0451a80c0030040101040040740d6449044a4940c10b0b4603100589910703c0700c00c03034642c01c90f00081095880c004203940906840c912103a45852650900b00d0081c202c07a4650044118044420404d04c1041c0b0405000e45800f613074284200381e01c40d0025030b590740b120b01c14201c895000103410f21144600800c4d211102d07229180c054075080c0004607034103500551318a54505a040000d02c0030411034440c0312030f0700906200349041d0341b11814910721074940702d8580e0000c0002d5211400144028201caa41c00301442c0e1200d440e5681b0b08280551400c1c0c1c00088505003441203001200e01040d60107141d518030f01d00500d40e515450400c03000d00f40441300c40c500d4012240c500d07031004089500c0c0e40e40e4100c00c030801020341c021078451080c140c00810100000d0b11190080c04090360a556644a0340c915550054055440d0300807442080c000c0b0345030613000440035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 828466016 1250 828464766 828464821
    0x306041103010303080916030c051009051e03010e070e01170c130e06090604080315190801020a02060705040503070512101b090602120d09030c080301092007150203 72
    0x3101301600000503038081c02141c0f08541c200300812803d03d091480d42c3c04081c1400c0e0b1102c004104a162024001d50a25801d00d410102c40d40d9030404607012140a520310b08011818040040180c01c007446400c1c0649030311002001d516107004815881d0b1041030164135032282c42501030015002041040060b41e04000d080101400c448401000042644410555813800b621780410000d880004010340100d4000c809189507845003102d4070320b282d12039483e080d0001d8241ca10200d0641601d9201c0d03000b40b0001c80050380e29801c2d490001c0c10110000c0004040c000203100c188100e40b030005045003a10f20640c0d070310394501500102c079840c254410410104a50800c4d0a01c446051072001c607103c84001c40e00c407051450b48851050740c4030992035011002c100f10600603d0142205504284079913030103414a40b000d10b41e1520703043d00c5070307000760008200c00da160074050304821a40322030247c400e14a821058144034059503001c0e4280b203445060707201c01c0d0700403011889080310340054080c1d0650200c140b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 828467266 1250 828466016 828466019
    0x70305030f07060c030905060a0c020a0f0507150513091a130b0a090c0210090206090a23060c0a030806120142121a0a021801180902030604110301 64
    0x10018554007008040703c8a50404030940b80e514020700500c880d40d940003015060640e5071132007040041504030030800440c852a006000070540242c0300d1000c0c0c030301a50260403c10b04050030710040030341c010403013020010b04211402e07100e401141c20a003985c1095001145441c81d8449400b00300b49145c1529900860f204003100500000f54418585d170803003900c002803a10741d40c2c0d000c0c400b1110101505009a00100059079510500b5401a200750344000e00c824180717110300000c203e02c0c1e403054000248003070040d00c51410020f54406152404407040f901c280c0b070500803045080e101c83d10584001d05208098011032807035940ca410003032002035101c0c002c21940d2241c1c2d841d04181c0d85428160800030072685181180d08500080c660181032030701e5800e0040030700d0040302940458814009882582143d6402400401d02240300c50144500000150b110401c021004905000040030305052000442000300c01c0403d4413000c0317040f22104400140c40341d942c0ba010601502040304140c0702c4c0c1900100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 828468516 1250 828467266 828467287
    0x1706011e031515120c0905061e030712080301060801080303010f06050c0c04020d021c11091c0510091e0b010b07110a06051201080d02030d0509031308070914010b030403030b0307030503 81
    0x51a048580150302ca180c5c01380e074911030001111710503074104e504059200744c4046110340703650111804000283c00c40c2c0006a440e000620304902c14002203607580d0000004005d003e60000d600703405040d00501540c519403400f20b1480c1210910b10981040c000c01207407842d03c01708144400080110043c0041d0b40d074205150780d4400a5100b200d103100100c0d040d05000794603c480e407050000c1d19155184661134003040f041000100100b42c0810050346c80d412210200040041c040c50444414044000c03030fa1000c0c07458481d0744081c0180303141c65a01400700303201000c1841548603e04540c4900c0c940f5a03100c40504055004203c0525040d41000c13010300c0c0000c800758050020030010400a00009060362508829515000c0100000740164020701040380c114055034007951700003c143c000c1340e20341725816052011146440c2e0050602d50032106040000b11154002e642c120b020400c90a08a5818840040040d01001e030015040507520001000e107920f080081001860b0020704070313510b6000510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 828469766 1250 828468516 828468539
    0x1e07020f06101a0c0c0d020310140a061409010608070504030f05030301050306060a0f030821040302012009370b0301090b0d0b07030f151706011e031515 67
    0x8620f0501c0c086064070100001d102006480c11002d102000d418145452001c211440040c940e045e03905003d5000b090f10640454803422003001001c00c0944201c0c58058100b80c211903595001d6201061805a0003820780d0310b0784052815a401418040215281c0c4102119240510340008101c011808900c8081c004000701450403198110100c0b506951640c01340708170250284120543c1d00c88440044c4002510321000e080c1a030141c20007442100c00800414024940c292000d07000341c0d40d90200d5070b4900164290710800326041010340303481d0294000100e440340601010034400040528000b416120a903280ca2042151038401100d003640c88010f42c42243c0e0007803044e9403016250001407a01400e00e03003101124140c016840c807003643d540b4030742900508140d1325008000e580d81c840080307030440300e681104081d041d00e8401c034100b2501c0504480c81e10006800520b28440383d400c5101d180036a000850f010740c9c1d8000d814403042d40c81120884043d00c4c1821100d00401e04c420004241107a140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 828471016 1250 828469766 828469769
    0x50d320402040b0105070302030f160c09050708010504020316080a0b030a1a13080f13030b1e060a0510110106120b0a0c0305150f06040509100e0a051e07020f0610 71
    0x22030b01040720041d00001903640d482200e2004015030402d101e10b01d400382098010b403001d0081550140c00400580d41c2c0d02150316000e400a80d001f0b42d0394020b204503d588015200e02500d02075504510f181400d401480c1c04400142c204010042c84400152005026400110615a0240c02c0312103148030341c502402c900900e622a01808800032000887c40102608940050340d0012103039403601c891a2030559040e0702081c180140f106071100c0010001351024080352181039125001e0750300c1d000070a54001c407000c2c0901a14030072580d6110901681d80e0708040304600c100241041c61241e1038000005016048179408070b00c81140001050040c03005082c102031241508030810441000807020a03401c42e0303c2912103e203488981c405504481c20f00708480644803500070314039410310343d6610000e40c4520381101c4801104103505400c010484c02090059041290b124040c042c1e403a10b0400d800e0389603800c00c1103840c1c014000c8085101070b03009000350144c0510310000c0d1491440c0ca00341d40d0700d61182d40e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 828472266 1250 828471016 828471019
    0x30c07051513031b0209090f010c031a010f09090905010f0e1c050c0f03030c0a020c09040314090607050d0c030f031109062817100501050d320402 64
    0x14071600100e45404000c140b44240302658500400742000d07107040321103120050074156180040780c10b09000da503039420b06a115100f000c000705080e4411000079030940704507a500401307250030440c48400d0001d006000d004d0202c0207107880032410560f00c0c011190038260f0390100c000b1918200010b803d014042d0061074944003034034030601064010800031561100d018000400d00c1042203030f82c4d0740c0540b26600030600d42c58050201d5403441500e0955a003107a10a542400c400c00d00016038461031a014401c10004181c1210000035515007601c000e03207400c0210100c600ca401000421812584d1080140d42c00c00b234001084425a00340c42138094101d002c1203105502141e01041e442005a1181c0510301c442180c1004081c03c0581c11800e1104a42044139403640310420394031038154801c8120402440341000d40d84840c1100064684071a06001c0a00074801d201601d080c1446166040021220041e01c03a24002a00d0000085070b0703400102e15515201401c0741e0300d00c02d07002c60f001841415006900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 828473516 1250 828472266 828472273
    0x2130b03090106050901153e0706090303080136020d0608010501290706180b0a1103041b050a14120601030512070507030b0a0204150309050c0f010c08030c0705 70
    0x200d0f0800c110300417109100f043c040e07a2980040703100a038440c88201c0701004442003d20b2a030440d181c0500b6109440c84020305020b00381e561228020241042481e00512141c10410891070858070024010841402045880d580040c8041d00c100c903c04001d50b002510545401020410749803154040d602480c0003110960078220040740401040c0314550484040c151485e1003105c4409540901c3d48040403040701a0398140900c20201d4440c4c000c1d00f464000c4071007281d00305401440c144990b8640902084203d5113030862080303403540701070200ca400030b410a248440d80117062880501c443c83c183c0246402c1408420700054903604200e2040d0784d071400716040280f13107200c07000d4503a40b000d02b441302800c55882440c0542079070701418014081c0500a4066642030340c0c6a444500c0010800e540520b80c046d800901004490700001d00203004120303603d4180b0407203d480d10b03003682d00c0070b1090f0201d225010a0310f00300c086078002c0f40307803040069200580f20349030315046560352996040144261200d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 828474766 1250 828473516 828473519
    0x90403140a0e040c0e240717030105010f02030a0914030a0614190b03030d0e0304080a0506160e030604061a1f0801060f050f07060b0d150b180a0f02130b03090106 71
    0x14017504290700780c81e501403c420021031140140b0509654540c1380c1511892080110302c0104000e0904440c50080d103421307003a601e51402000611a100c40303a02001150010702c0844241c07580031138000c0450340d85d4010111080c01c42c1001070306211080e6002032503140b800c0d0006a4401c2212282e502c5070440d8110141d00619480c20001543e00d004041607044e04200a007801d04100344e84103005641c2880700712418107072100b0400b8503009070183c040d1001e9115004000c000701103c110068107080a280c40e4030308440500100b642c0310000b60000703190360b80358420100c2c01183c09400402c030000c02044059a0382841c10b0050081c0c0071030101c075000411240010481c20300803202c500c2014580d960b541c0c90200754203c5202d10380c20503442100c8a9403a140b84554a54800c003092900ba03000e4084400380d13066000340c0c1402c8401c2050114000c400035511040c0405a864003140e000e01c00c0c14003c01ca500c2409800c5009214080c00c074418000d074164086424412440654801c500c0280200010f0703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 828476016 1250 828474766 828474791
    0x5340209060103060803040b0f0f12061c020d030c0201110d05130b0a021902060d05010e0a1d120c070b0f030a0506040902220609050112060b04050402030c090403140a0e04 75
    0x150a2809080200d5008000070000200d5160041289d0018942054202000e08045690980c444000b58a8048404041c010b0b0b80c600201c01f2003150440d840c0081d840100c0c1d07404600c0241c09074902500b4050b5964504080d640150016080300a130201680c1d40005120001b0f482500300801c1048080c801820114075040300341c080740c2003107030190020210100c11391140c0040a0080d0812078124100348400e6802103194041c05019295084244001c0d00d480701e000d90417500b181039804164003040401d04012000802c45a40000d1203170455640c40c0e8440000c0c0d07181ca012640030900e41140004c2801160f0b15100155028004030807003480307503450740c0007040281d071030600c00a5031000c42079850f1050b4000c0c3e280c2517141c1d05203644000c00c40b19a611410400c50b075090340200380e22100100742c00200b200d40d02c03074003c80d817500711000c010605298002c696135001079112107000d840c161001c1004e06001e000c00002c0740c6080b1241507903c01101030300801083c0d0b0100703541d0045090458010700c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 828477266 1250 828476016 828476021
    0x6020f150915090f060106051c0c1d1504031101110c03070504020c01150b0c010b0409080702040207020d050f0d0305071b080310050d05010506010f08010f03020105340209060103 78
    0x45a500c80100480d150200c542c601c0594003a244506510444d01c3d66007818005020450007030003940c8881d61910f0000c401140c8019240c03c602004038685940c4c81d910a0300101501c141e0480072052460344201c102c0420f04d0284c0034800950b2120020800008000c035551841005000a90f80c00d40840381c0b0100081d602c00c0c58401581c3c1c10b40041c401408281050b50140c10344c449000c0000c0b170341c0c240c1142e541a28a00542040402090000380092294001d0080d0100c070311042e00c08000005e4240c5500d601400f0340d00c80203220b00c0c2c0000d0f20b4010b56642d030340d41a2120390040181c40e46440350a4010360366401d502c038901c021904150001c1c3c400d80c014420001c1c801b10700851205c082101c1d64600140d0b600c01440710182405c0c2920100c3c103900c42d65850303902d10b40304600024990500c9000900040488420381c4100050600180060900200c0d00c1003101e50a0030615200e20505449010a180c00c2c4034410148648008042601c03402500440161b0b0080e194490203031640c1c0c0c0110103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 828478516 1250 828477266 828477271
    0x2030c09090103121b0b07210c0c020114090607020d03050903071202040b0609031b04060b0c060405190206041e090e010902091815090312010305030c0f01061a130302030706020f15 79
    0x46d03a1030b0b240001c2c41b070707a004402d95080c9034120400402c0b91304031458818120b90b2010801070000310340408443c00c40d41c002d40c0b810425207242110134100030741c7c0000200b4910404074000d003c0c040b194051000c0500850681d4034030480101a18409a10340d2421441ea40384240b00740d00c210705026044101c0d08000c011070340714400113006008031480c000c07680c0384162421a201c5421556403c0c0008024800324090040c96031950044d0000c0c2c02d090401c90302e0002301044411703000c10b000302e51000681d204021201100c0b000080300d80c80c6d590300701c0190180c40b040c0e40100070796810b0010815920070191311240740ca03882110364010036152800504080302540300700564543c002120040c0204103800c5e0303158404225411031b0301d011840d10301524681002c1e0710448048c1e1021840000140080c00503401098024000b0840325103000071440c07588624456900a0101c00103500020280c0900e03490081c49d0040e04071b03248195500002940c0780711400c2c0c1225140100c8940d070b80e100c601002c60b40e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 828479766 1250 828478516 828478523
    0x1107170615180a18080307050d0605191518060f2601050d0204090204020f07020307120203060109020d180309060f0e0d0206160c1401080108030304031202030c09090103121b 76
    0x4555680d0821440105004c40d09056403ca5840511001804c02c00003035114810680d20f203034840e07103038005941c00d03601c039500824461b03244c2504c0a0440c0c0d011204880881d4610101c0880004000d10250f520001e00b106418480000364800b1544603002400d04a840c4441d988246484172685502d00d0040e00d8684503c03031000412004120310b01d0324035550755410b800100002140803265001800301e9020b0807000600380707400b04241c403d51405100c42801028009070000130944681d00090b1248030500482114035030101b9200700c0382c221948000611042d200425400c06450b08003c3c000086038401e00d0000740c0c02d4123114948a21880030b580c0c1c0d481c40540020500600b17a42080080e402582c1c2100080c004002c114012507442c41c0d51030024652181d14a0f00c1204000006140500c140c200030459481001803000295110340011416408100016101c0c2c1311841103843d944110300c929503000c54884004001e0216104206c0050b0200f600c41e44030041e801719101c28030140960014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 828481016 1250 828479766 828479809
    0x70509070302030603060403140c0a0c05120d020a060c03060315060f21110312040f21050a03110c0a03080309010506461418010f05011107170615 64
    0xa0000740030f1f0218449064002404502b00701054034001c3c80c1071480f050a03244d0818a10741003085007001460180307510380d10400342c421010704d8100a903441007554002452290754080703180301c25120b07501030070245030f019000040c0b030710941ba850f0300544514001c5e074104021460000802100c1e08100f20b861401c45541030007006000d485802c0655540c0c903944da0140107400c0d91403402030400006001428146901710070050800c8240c1703136000020f9405c1c0c840c00781ca00450304045040004e0f207222456040c0303413007180040f4004c00745003428102d04559412580204001c02000316040140d4801c8404000070400350340c03084200701910181c2000e90314650500c0c080d80142c0f034185807a000746c0316680c05140c0c00701ba0703441004400910a84d8445c00359410b0b062541e41c00c0b4078001c00d0200a030214484503500650400c150141e03021041e100700c50600c1b00b90320b0020702d0f115042c004640101145503500102e5000018000c0c0c940004036110154044449081452071601c2d5014038000041040c15 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 828482266 1250 828481016 828481021
    0x40609050105152110061d180717070c0201080c090904141f06091d071202210a030206011d0112020d0228050a0506072405010807050907030203060306 66
    0xfa040c9603202c0303001e202460703440741030648500c2c0500f01494021402840154065850040020030320004640d40c1481d90784041c60780301c116030784c04904c440540504003080451761074210003900c40d01070140c503085a110480d000c00290980000440c0e890724001c0c0c0320190b203552015551011481405500d0380e0050081011801180b060712a002da02650345089400717240084c850742da031820506800d584500e8541405110b5003889015144003030404003031004907180002049910b0b880280124201701030400c41c4101990749001070390580312203c004a503803074840c2c801026122127562605034050301c5000d00000d60701045040030310170b400a242105020ba42007002d0030603444541c03d0181d0b4803401e0a074107000540d8842d103031000c1c1d0102444c103600b09940001d481c2e140000007640120310611458400b0003143d120b0380e00729000d0903441040fa203645580e000c1000303143c20b40c403900da05030305103440004200c9e200001002400d8413003c5501c85d00d6031765090403c074140d01c812919207400d508603101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 828483516 1250 828482266 828482299
    0x260a050312040c030f2103050709030803090a0f0602040302090c1305220c090806070e010c02060a03020c03070c08120414150f0a05130f05011704170d020702040609050105 75
    0xd01d41e0003d108107001042950b480d11060700c440d51813035068482814100034107804007588500303102c4025060505000f9460b00207400ba080d80700b5403202400d60840000060380c04a01031250200ea103601404400c2e5448107403c1034070083d00706002c202c0c02100c41c000840d18400b10301d01a5941080124803401c0d0040c101020311403108001e07200c0301d0145055101d0499a07030000c1c05080c1c03060405135101c102082c034000c00940303054400342000007808413072944510540d80c46204004000e4054035030a1380c0b101000700450007031049032813040850101190400c20401c45002e24000c84102b80c1c101c90030181c8099a00340c161140e84120081e08200c900c1c52001410000400d12403003001c502c40c24240004030400242941c403a2646000182001031506408a00007007550301401c045030320000c1641c2094000303403048010f10103100103900c1c00b138000f60402000410070b100003240d5100e865103600900e00f111019411201007244a54240580403c03001d48a221351412144000c080040c3c20302d4006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 828484766 1250 828483516 828483547
    0x20a0c0b1b0304060c0207270b0f060406030e07082509050606031816061106160203091203040f0e0103141b01030c05090907020c090a140105010522260a0503 69
    0x300c1500758080c802d80024002000781d80248025842d242c0b03800095025038a52082740c0010010078450305c413446035000184c4550060320160f074141d040026010200e8914107280c035200780c0c4100054410604401c0c0340700321408a1301010110012100c03059500c0d01c00311401e8400480f1402e80000c0c2c10301c001544840b100c03105000c200e840c001986c800740031103580b8114820b07143e007126012690880f01c6452101e400c200c0700da440701e2841c3c0160a1000140e01c02512841840413a6110380d03290f400000300c158052003210300a28861403c0320034030703942c0c540a58080600340310076108100d5240d41c954800e080807498500e900960a007103032402c0c46602c01540140101080102048002e10000c0e656484c0c2d140b001d80903480342d4009060460400d030070400401d100411100c669030510078100c02402d28600c066055907024204941c813032401030803480502560900c42181008480c0c8002101a0241c1613403000001c181098a650b00c4007035602580d81000d84030080684e0300c02c000e2054001400c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 828486016 1250 828484766 828484781
    0x807020f0a09020903071d01050d03211e0207031215030c0e0a0e1902060724090c060e030703080c0705030f1506090906070c060b04020a0c0b1b030406 66
    0x30580030a10404401041580740940c2003200a0780d400554000c452404000c0280100000c400001003c04100241190254184611400f42008450480403d40114111100300c40b400d1150340700f150350644030001901c2a121100c8011808410101c10072816000320703503006405441b50030030041d00c052041c0042510342c0d024564003100d0900400015403502440380141035244981e903217401d02c01d004004447c1e51086011850384440b03500c046003544903010a40542c2c04071082e0351604554185140c400c40040f003522030710f4260800e035072442402c2c0c1e407107114014001c12001c4081b40e1104000d5880c0c1d020003445036490b60200c0d000b04009101600102280e03034002c5c040d2128190b40d800401d1610407010350b02ca00a4000c100060a640c42d002c1540e076000d1811500c01e03040e414500c3d030b200d40300c0201800c1d110421140c41c0c002000d0020f41e8002440d00480500110350b60103003c1d0b40203142a42c80e0f4411504211540c0100396050703c2c0025140d844070501c841a880d589031a41c40701c0040511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 828487266 1250 828486016 828486019
    0x311041d10051002011b17040f031e1106070801140d08130b120c0a0c02010e0406030507140306090114011e0b0f03041e050c04020a021207061b020d0c080702 69
    0x1081d4020940b5100c1a507050f01150302134001052138141070901740c4403c0c80a081007002c00c03200c06840d000d2002c4001e401b58229030011a8010b00c8401e07418100c40700c1c40700485c0c580350180b10118055903581c2c021100590a40841c040d00c0003900d80b05001c48155400388241600110761701035541303c5242030000c880c203e910031940d00d840d09566071000d80c1e0b0400240e0200001ca180454590445880c241c0d00646c88060f440d0210b181c2814010301038010401c0500190402c07100d101c41d880d580c3c880749d0000c805075801030112994950f8942040783c541c4480c08a01d03010340603440104419805c14010501d4010001c00c4440c056801c050701003001e81c941b00c0540421504540740041c103803050320001c00701c03070042035215503603480c0900b03201004250040d1010088400c0d111440b000c500003186400200381c04a0740541d940034052000c03443e21182900b4030481d420001200010007080e0381c0030f00300a582001600c880040b841e001070b0380781c404440600740840c100140d9240003408020003009410310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 828488516 1250 828487266 828487291
    0x50f01170a0b010f11060c070f060f021e0310120f0803010e240109051903080415170112020409080c0604050f06011e090b04090b10060311041d 63
    0xc400c800284848081e00c048000790ba81e2001c20065503031200d6040101c075880e04240103081d8a000071295503410040100c43c0d001c1c008981c1c1c0080058a40424000305e0300180c09110010844030403400a41c0284840c130306508a032414000000c100f0b03008d40f80b04000380032014080c5c601e0032541c0601e09803502d40407070320302c202e6940139000110440301440c041d03d484d50486030640303040102a5144a41b200d5100003d12081c1384950050785c0c082d00c5001601e4065071515000005c0560001140c0f00c1d54100503c0d40c1c1d00410042060301c6480e82d0549620034034bd80e0340501c06030720354011010707020a000b0808143d407402c0e07120000d81855040001e07954442e044c0949001c99011942e400e140e41510110340075048025030388010f110800a241c0500450361341520500008044418500364504c55000e01580702c1314840c0f1240e17905d0340482d0240d500304001500d1403400f41022040007584d402204d003c00e161440e040507440e10300059a09982c1c46480051000d4020503072070080b204000c11a200c01314 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 828489766 1250 828488516 828488537
    0xf3112080318060a14132a1502010902040b0a030209040602090f0a0b0c15010602281e120806010f0815120307061103091c0201060b0f07060c03090c050f01 68
    0x60104001c41c8a600c5140000a002030b14140c0c1c2200c5d0b00c00a0305000300e015600c0b07065400700380d100d001d5211114100c1c0e55000c1c0000904184070203021207034410022001d400c1000c4018503019000345218510898003088035100c900d0805c40b01032814000a50840382c10b400040006096500601c000ca1b801042d08490744d07000400620030b02d482d604041c0c2c030840d001c2411040141300300088050f480f5002c064091355030612130003d59034071800d03058081c45549136250843c0302c250b0300c030131504480d001900303e81070880d80305034a42c840104103000c079880401282c0702e000e02c51003506810f02602c0165103004100d400c941d81100d0009018005940b12001c1d09940c810b10f90320040406015a001405075440746014146141241c3c1d0040304112482000c20400051003404101c40301240040c66206584071000ca070b003240140742e42e03007091009a60008480c8807500840700541807462250303009008490311201c0450513506c0070080140a070744d81f010103000300d141146140700100c40c10300d071505002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 828491016 1250 828489766 828489811
    0x40f080c0304060c0219030b13020a030c0605131d06040b120a12111207141009050c0a0803270103111306230a03110f31120803 56
    0x507802a0f0290b00860003944440301181030900d03001044294840318580b52500e036445a00c0003520091980d103101042c0c903245811941c0c1e494184001d1508001c44140b0240c80d09030160072070f84262440800c2500404000072045280b981400d5007080081c49a161a16030106100c0a0f110208845034040071032045950451020040d03246003c0c020400401018203004000d046084201000211038110300000300000d40c1200860b44080da02002062241c14002c8800b41400201241d4200341400d26185406002c00083c5020780c1c8a07007201c20114140e920240c20303503280703e41000487c41604441482c0e042c0300c2017404050100b8418107001c9108450fa85080303015030701c0401065100080014180046a405442c1100548410f40151000700c008403d140d10740c019854800100740c0c40c0d10550341c0e800c0a08040d50240140f030b4038516120195814018881d4001000584006049820000019411000c2c5108544030211034498510311526207020661004101c128011004000c82004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 828492266 1250 828491016 828491023
    0xa060e040c2d09050d05060f0702070302090c041509050f0f03010b130f0b092205011508060405060c1e03040831140627130b04061508040f080c 63
    0x2419440c400601c079416242001a040340d455130403642c010280b102030503000a00000c3e05541000c2901c44001c075541e22801d04a20304119a00001d4102c1240310030b000d103c403541c0020304280c0740c01030602c0380341c988143e404440c0e0500c64800c1990003d20840100c030181403810782000c8100f8090004552039a03510080b44400300c5e18140184429510038105080034035611482d400414211600d81090804143c101d5408412449000d2841024048103080110940c00701c044510b074100c240b04c1840c1d8800d03419440341d104076019076141c002d410010b0f9003011000300b110641030f042e00b2040f40e0301000c0c080038011a00004c008548601040001120402d06a4240d26140c15210355202c0f030354100c42524610082c25a020401d2203d0300d449903106075843c0000c2c0e50a100307940b0b00c140611084440b0030010f060a43c20020780150b10f4480302c65100080b500305110a03001503406014660381c4695003000d10030020b10140016005001150014400340001840c150280c11510300340b04104028908 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 828493516 1250 828492266 828492317
    0x807030c1b021329060304020907181223010501060503071206050607050d0207120b04123606052d040305030c0c0108010b18010e0102100e0109020108060a060e040c 72
    0x450005846913040c02c0c1100e01654072406800307903091421414541c3c08a01c0c0c1e150081c01c040e0a00580c94465480e00800c403581000034013a042d071513840030b81ca0303046c4148200700c8941044c010100a040300e640c100701c1409054100c4a196844924542d10380b03004442c4400071641c509102611a0000200e507a9850003030b01c0002d0090000d89100d40030144080d190014a5008406001c045070060000c210180ca940d944160000380740807000c420903c0856902d0b07040d50004000c050000a41608000c17058080c001444100d58030f06034113521420f042c0d07034a000e100100020352601c215a40310103107003a050b0488540c0034800c028141a160b90314a03065800061180300c10794803032a0302442643e88031a61a00500c1d0400040c0d02d07007812244004100303003c804a15050104034200318060740d01c200440380040000c4002004085824a1380074042c0144c00c00a0f40022032580114800c0d18200c5011030480390903480f036000030b544500c2030101070311030010100240903000c2d6840c1007200c843d500810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 828494766 1250 828493516 828493541
    0x80a02100608061e13030302160b0f04020f040902060d0e0a05070b0c06060d2006090a030809041b020a03211a0301060807080705060322050703030807030c1b0213 71
    0x5520301c0c208406a000d016111640200c81c40b2113401d10401c5001c0f0f112820440b909843d01590307512010111401c040c0100c3c2c0700508a4900104000c8050344080d02c040c0954030803105440445442002c10082d40d40f00040a0f6014608001c039148001003640616002c40303512054503801d5030161107907404d012041d44038006030140000c405803541800d01207280e2243d0202d03503c01904881d501e820031508601070400307aa0b28002d906403100c0c3d9071824203030b03a00d80000511890321251245840307070305504141815405035051094140c04296140701c42d01c602c11241d4000d00051825071412100640f441042c3e40c4c4001d26040e147da1404980d00855043c0c0c1d40b600c00b070510075910301050600311001540032020981006006010541c80443d04504603042111510307204e441e2022000403041c1068400d000013280b0000d024104440801d0080c120f0703000f43c890004035600c400042e01681c83d41c00f01c400000320007131400c102d01c00b82c0d0000441403900140074070808044c50031800044522460720f06 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 828496016 1250 828494766 828494773
    0x8121602180a05101410210c0806310603210e01082505040506161502030906010905070201140405010e1e0c101106070503010603050604020313080a02100608 69
    0x2125504a02500e40c018003200100c0040c2850420305200d4100d0072808941b01308401040350600500c518459003030b000754296104c1ca14940b1011100040c01a020040302003240f010000b402858035074032194515506107016014281120070304420f030701d488012606480d03903440e40400420007029000c420350200350192414504240c03c090701000b01001c0032410480c82c00d04005150050ba140c00c4040300c0207651100540340e5409054489004e542c00c07603074003c400804c1e0358142002c1400950b01d0203020b0400c400480914480000991200711031401d10343d404000100500c100e00e600c11a4840441d00c0009101540d0520b040750701002070742d054035180e45448148007048800d04c0000707168203544200320f20f076008e0b41050a0300e401c2982c107485d200720340c0a038070b48441600074406400641300c00c900f0f9540d04c1c81d1880019100c3d4000b802190700082c6810000342441c01c0c2442164002d10b01f00783c142c0c18440c42a0b490b890710f907028461800450041200740545401a800340700d020f0014500074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 828497266 1250 828496016 828496021
    0x20f0105121e01050d03020d081e1003061107050d0c170705060a0e03090d020d0302150405060a0f11030a0c031b11102331060e0105010812160218 64
    0x102202c905060704114400d40c014036120002903000107000c0b000c0c2545041c002e036035a540003800c240488803080d0880c0c2025030001001000310049020006407841203908028080f0a060104071900130000d00400c103520811248802c81c0c0600010f0042a11400641102d18030304c00c1854032030342148808689540c0100f00380700300b14405011308115801420015410449448000342c0d01814034080070b0b0084415290100500d0300c240650801c501003040c10790f026041502e06a0b948000480e40e41055918005003450180b01030701403030b0004c00c500700c541307800c50f11245004030081c5011805101070598810040b13400354810904c014030520a81c4030444150700c0028031740d003041d00000748400301600d0611014902203140010032810700c04011980156a120f164000704a02e0464020010790b1504241d201c00c9100c581d05040e00034440c00c4180203808404500d0746c20790b6001e01946c07100da000100d2055003001d410018240064006540300c15441141d00030405060307041995444000d1000704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 828498516 1250 828497266 828497311
    0x3090602130b1918090e0309100f02060903130323010608030a0320030c250f150905030906090105041707030b100608010b070f060c0e030106060207050a03020f010512 73
    0x7403d1031030031107041203107100310704072044030803807580303010782480c0c1c680ea0050382d601c0020810566102c8c03c4060f002500c840301464000c0c010403071000b26000188600e0b000181c070341a01006aa00c0030155964000c402c2c0d042da943c1c402c032407500d140c003103540c12407240043ca5611824011b0380020051040610741d1030b0500320380202500d0301d111701c4ca4400a0141030000750590850103d175400741d09604a5a00d80303002c01c240901d0040d01300300c18044410010030391010322001e0001e03203e2242c4100741180c600740c2c00090200c148c89410034081c02035001402603542c1418080014804003205242407807416456204c010b4900e8a65540d4007402e6000d03000901c10051616207181c2c100b07081072903903c1090326080c401001c0d00f905009810800202050710740812100c030101500c0541d00080034001180c1c0b07850002c14600c150748410f0b20942c03c00d0340018102d400031640d001565409450800301d60309640900c014000803044e00c40c1000400c114001841074407640300ca0181550040da07072800b03550202c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 828499766 1250 828498516 828498547
    0xc0609080c010503220f1407060906170420131b021513030306050904050c0108330111071403120f1b01021611030d030507090603090602130b 62
    0x7070301814482c0070400d02891820740e0400200c5e1450955484110030351034948a84056080d880062500e03c5030008090310601c04900e800a6640070380d01e801032603642d00740031100ba5800c40559004407081401040c0818405403d01d940417087c61043c5e4009816200420358182c2284d0020011075501c03000745145040d4010140d0401410b0302c01005402d648040b044944003018008894070344d0001c4148040502075004080240b60040c41000186000e0406a44600544025030300081542e000100d10340c000e0500c808820000d01d4210f041045041101a01042d111030280d0501061039080500540100702c0d0001406800103a1038000075104207040c03030982c101984030683c0c0e0040c85000400100d050076150403c18289a030303030b240c400e00e02c81c4c0b5009209102040405031364001c0c00801707105103601d000f450140140c086560b041144403046080310b8043c3c0b03030140020030054042141c540300741c000f404a00c0c0035020062400c0c5980110381e41413503582d800781c1404000400c2c4000c1802801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 828501016 1250 828499766 828499783
    0x1518040506030c1f1b03020c09070908030901121503031d04021206090a0e070b04061101110f03040303060510120c14030112080403020301090f021306150305130c060908 74
    0x281c00400c480c1003403c000541d800760900c084004030358080204c0b40b00c284500e48407948800242c0c0101c0e25441e060070000d4983c8101c82e40c0314011030741d01c000708442d64865140303801220fa503040030f1030520302000011a071580321121010305143c0c680507015100c411023016034008500c030b51940307603403850001c6821081c0a01c00f09400d101da07206125800c82c400150040c0c9a10a1b42202e4504060365081d0b4000001c012180d91805c0c1407107541d02c041544413108004109030b60350350300c681480d60140078a483c00d8440c4000f6400141c00c052040d0080c14602d00d020f560014400d00f004103085031141c01082602005010030800510f0304207010071510400e03c80c0c807901841902c1c103c80e00c0590240d0221040c401849a1490002d04408000501c88888180e8000e11341c010002c0c400c01410742401c2506004000e801c2c0e10441e040c104118461120340f04040c1128000c10561181e4100b440d402d03070080c6802420010500e20000d0100c001a260788002809407005413a43d006840c04c00d2040c2e80741c003001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 828502266 1250 828501016 828501019
    0xa0507080307050303040228090204080c06070c0b210705030a1a010905090a020d2c1b010318050d08071b030e04020f16030c170301050913021518040506 67
    0x1c110b090b01240021007242d038400d03015144140d00c4240341c6100003000c1d01440c0c1d02d141d0003059000204014207240c0040c000c68580c40200c0e00e00360b51031070402ca610310078600011b00b54007841e00104a24100f02014054401c1e248000d010310088605642c107100404503030140c00201d001040051010340c0380300e0b501e07224261030032405041140200103042d034505801003902c10945400000d14811187d0122030005d29074031000d101c903004008054400c00c0101c100b645520f8a92031508111001c00510020240c40d203072040e901d000b134100b00540003055800400d184086001d82c01d040451010050203100407503942d104007032480c040100500b0340c0c540d1100607542c07840e4080d401c808a40e03c00c3c07181e221840100c0b03005950724015544ca80742807181c484162816048401c881c0c003072580004406c00400c0c02941215a82c111510351100303284801d0041e981d0000d40c90340421002180b412600018901c081c2440c10503960380101c0000caa00040141c0030b003071765828890b400600703107405440d810240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 828503516 1250 828502266 828502273
    0x3051312020f0111030903010e070f0923060a030602031e0c0f07060b0406091418030418090c0515041a090f060a03090219060e15190203040f080a050708 67
    0x19540d00042d007a01216007124100203801c060714103000c00038012a00c0b0b4480060003040320394183c1904c0c1d52201150701c16506034042403a0b0000d50ba03402401504055111080b510b070700c0e610581085040382d20007408a54110046440110000300d85100450040100d00c8500c20f2280c40f040e0081c101420041800756601c1c0e00384041868071000c041500c0c0c03007a43c06000414241c0c0c040c0c01142c0103054a61101014508000d090350540d4400d40107180031b948500348140c06516100da45550301c0c4a14031030030f00410144091850980413983c04802d1103845184921149680d40c030004054004c01e21b806000034000040401c810203c00324564000c00408102d01d08081c0048002200030a809031210b00800c40007c040c103d062090b84854030680d0b0003080c20903130490440002ca0700c01e600d802100045455403d06904519100b88801100c0741c00d1203129161522169080d803035062224020001c0d40320520000c02c2c1c0b1064521803078040e0240c00c00508101c807103410b01d07030302e080f1966201111641 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 828504766 1250 828503516 828503549
    0x408030609070c0830160809010b0307050907110f0105060a1208030c0903120307080610180303110705030703060b09010e07052209051e1008060103060c1407030513 72
    0x40059058600c9004103890b00c1d00e211a48400760101c017019000340c91440520042007101006512000115000d0680e5441c1000d941d405445800c03a98915651941a48030660400087c40c214118992206080c50401051041100441e10305481c950841c00c2ca65101ca0404c80e81d0308203400000700412070303030a200d950160b050f1240380c908d100103040700968000005102c1080c5d2000c00c80c0340e00303030303560785100c5640d07407500d039000401c045416581c3e02e00c01d080c00e0030400c030410b2080007103450001d52907814000b11481d694040d101290008202c84407402410b070300203199034003442500021405118041030341403a0310204210b5942c140c001810442c101700600c844298840c2c203031418000408041641001c12030100c200e104810f80c40300c00403c2c103010408c4102c204540c8100004482d55598203003d4540409030401d0260034050806164000c82c0104003185213070300302c4141c000d5141000058810500c00300c1c10180c0c4090015400b00d0f50006645c0d04c402211b02030f180c02007400b443c030b6a0105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 828506016 1250 828504766 828504773
    0x606031d07270f060513022d040b04030f0308010b0307120504030e1804050106360f1a0f0105160807140706020318030318010e0a0906120b01050303070b0417120408030609070c 77
    0x8100c0c2c0171040c0d41d0b1112340da144031043c0090804031400380807101170f41925a0303502c3c50100d489810000742140010254000002c2000e407030070aa0380600210b49a160300a8180c0c0714200060000130015070411041801d108907a4480c2e000b4040140b8070101ca4103858507141c104542074610070703030110b40b8540031508200c40c6500b107840e42c2d0444502010302c1c810714a150700e40c0704016111760f6140031504c07841c11803805050409910700c1810050252090014482d09400540d2240156021454198503083c0d905002808140043c00001c0c811032002080001c0c00c0307540f514106651f04054007613400000e09410508200400154107902200110310305101c0101510402031003070038190500c6051021407002d1f5403021415400f801390940200407081d03642030005144a0b83e428190f40e05e0482d11300104180c140070003110100c07600524601c07400d4445566004905900490760b040380d400511004213660501600755000710301030b23a204d6499051200801440d0311000c2c25560900041850b2803000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 828507266 1250 828506016 828506047
    0x13021807091809060f09020f010c080f0c1c02031215010e04020304032007050f01020102070209060f060c060a0501170303071707020304090f0606031d07270f06051302 73
    0x30b84a01c07507403440740004a582c5000c003070091002c00504003400c0c8280c2c0000c2c043c3c07691049a41034021600213401e105000015a04118129001707805030f04100701d030b0711142958400419081c1843c5040710035060012a00070600e02c5444e1402006030000100c0c8074104072460043c1e5003102c40051550181c00540c00081c1014520041c0d540c011900400054180342c010115010384501c9a07d80d0720a202000d40104d40343c01c49402964031580d11403840f117800b54030502c241e8200e69070140145c1e800b41c5410080056561100319250343c0f00504000c5055042018010103010b86680c14011880394109007501804120b0100705c1c104a5101f4070801c221140d20500d030130501e940c41a0a120f0036210018201d084d40b040d500700401140c14200702c040f182400350700c00c0c0115803055504001c0015501041c601c080801c0b080d1000a038440441801003442110000d102519084000110102d105808030185c42807002414900707503a8590800031410320180d074001d20a0311140462420580b0264a0320 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 828508516 1250 828507266 828507269
    0xf06060515040e04150c09170f031b01060f09200a05120603011107051c0c020607030503060607150509121c05040c080106030b011a040e061009030602031302180709 72
    0x7440d40030f007000f003030070300c0385a051405200d92491030500841c900600068a21820341c03041c511a80311100ba20700a41d50041164134068240401135440c0825000010191008074128000c49550310b510000f00c6049801d241e800403c40030710046101090030042c0700c10504a5600001005000c010441d0090b92040848040002200c00d10040d070711041c2c04280101010007c022408200281a00a1202c00580c0044d8120032070703251751280d403940b14219074072001c03440025000402400b0000000c2d010708003a50380050040d140a00300401903e41480c103000f01910074801a039240203104401d41c00307104803030405011a00c040d01c0d20910481d5070040c11014012030000940d620b000c03030100f2100c100780300b00a241c1075000780700d0f03d9142d04120030204420701c5084007540039841c1c1031030100d02e5407054a0403500604845015541e0717141c144411a01070481500805c0324880c804000201c540c8065401500b01c1040384540080321b04c14070000d005a802d80000102e40d480c104240340780e0102701d590 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 828509766 1250 828508516 828508529
    0x30209040f0501021803010e0705150c0102130311100309020105030a021803120408150402012010090303060501020c0a030c0306110c0616090b18090c160f0606051504 73
    0x45140d80d85003071250580281550082403940001152a200b00740c8008030072100c0400c0780208080004154001e54801c0b940c82600d40061840d01c0f2084c4035040c40c405004c40c41801c10016103072580d481203803102c00384940c2003241e081f120036103540c8030740c100740070b9a000031845400d040101c1c14081c0c0018007a40401480c10301469000221808500122a9150003452024044841000d034149103010607070030500a01966105404c20b0012419010591902481d01a1147c01100103e01d01c401703242d2880a001c01c00b50300c41c5083c402ca00c0501c0380f10b0040d81900a0344c00194541c00c4c803000a081c13180310344a140c4a403c01480920100f612030900108695104100103840c81c1c0040c0e501045000c0c0c88400942d600966041000700510007001404032070b07075a5140e40c1216195012281c3d140598603022001d0620b0301d0740c8a1050400340c03902500442481805030078040344155111014050100c200c541d203102d050a481088014007405000c1c01048030b0758266055100010402c6010700c5c85610b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 828511016 1250 828509766 828509779
    0x8041d060f06210117010c0813080711180106020f0c01022a0a14040c0c031b020a0504020706150f0503030706020904060b0a03020315030d020d3c1202040f0302 70
    0xc14051500201988401c02c000d07081001c4d0795407803082c110420442e24282d119400c0800e4019494400e03603400b84182d41d4680e90801220164071032081640180030101c4244110f0030089003030ba038581100741c200c2c4078542c004c09103030340c10180300904041c1c44064400b0a58407a0000c03200d9070713801144000324640c068942010b0341070390040114442c002d4401c05908a0f04941d400300e00c04080c600310448600c000e80d0103010141841e1070440d0416410700c0043c00261132041d00106500c159241070324928002010501c040707450304001012603001402c2220825900c0c00d2201c8604d03060102c120042c0703000044080618039210201e51640b15000009000c258005601e00c0c0c90381d142d90150300944100d01c40f0039240c036400040070b0025031041d501142d04440000b00043c0618000566150040490b8003801a200c0350740740035596803da8803a91307a002256030000c48007070710759000004040505034081e10f801110b26000540f0f440c1003140204409401040306000400c06030340420103c03179042c0c2c0e04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 828512266 1250 828511016 828511027
    0x51e1504050607030203071202060f040803070c0b070504030618080a1202040906030b0403120e0d050c03070501180b10030b070e0d020d060204141207052b08041d060f06 74
    0x446191085400c9294001808501c0c44203040e80000604500c0d0301c21820b000c0301e10b000900c140da40302c070101c49507060022000c00090004040802864211070a81001e071030305942035540b048101d004070746c500c00281002c5402c00601005000b080714441102c001c003044030760540c6a0601510640e03913818144040c86c1d822a00d44401d0703a040f40c00409110000308119500d9140c0a0320481007601c00b900000c2e50031518856203540c5c0c0c4500300810100c2001080c281c07440807426a004c1d00030303085004aa000611003840410400c2c003e0400c08054185841e025801c1403518a01745034015103410119040640c090002518010045030098004e04103000b94140713400c0011801c05c2007107402500b100010070303513004101d403580103442515482c034541243e00c4100002d0103030074000060340451692081004200d50f041203515040da603402c6503594207940d2184141109107040041040703a82c0000003a0801880c072050601580340e00940411070360a0a00c500014030100c85080711600c2801c00162 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 828513516 1250 828512266 828512299
    0x10905090f220f171303110105371404060c02060c03190305090d09120303151d06040b1008090106080d02032205090703050a0906020c01020c07051e 65
    0x2001d07100d0845140e04202e00340940c1c503041444812001003110000703140d0507040c04003d8014191888131440c1045100c1044c5140c540c0e00b45000900780b09818040d04100750350180d000101d5650b4410000003148801041e900002d40740307034006100800c03c002d88100c40d10392084039a003c40d800c4421a14000c004909036000107841c5e44110f90724603829200003c0c0500100c100072142c50803480803600e00700b00a9070746005071903c92044d022408006025801d0500c00c00c1480211418001c0c0245800900b0145442c0ba500056003960404070030510352403143d0101125108006912510a0320103000186100020440c4000c0484004081c00304c510000b5103005025404580101410300448000a0380100080d440e076003c1c2200d0110f0860200300f19401401d17503c0c103242103c0000c2c01e080b00d04d94440c80b0440003000f0280954410030386400742080420300d240090b2651010030340c0016a00e5500c0307018103240040a6000030300420690041781701d074101d4101c0c0781600718415550780b42c41201e0f204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 828514766 1250 828513516 828513541
    0x20702040609020c0c0a0b19111903121107081914030709031506031221060e0612010c0503070e0d1a010312030b060a030902010c020310020315010905090f 68
    0xb00541000c0c2d1000c00c9a280d0310b80b0005100403c600203071111a603968a1b444620418840c17000203603812841090a030701e409110300f150001c1503007400b05948610300b80350901c81c510340300e43c031054000844002c00c00f1484040d0348103001440d034016020501c0d1417080e40c1d030300c007240c028095185a00c0891000c150b100c94000c041c2c42034203010003801c8a07030780e1030325a03000360031448140000d907a46418400c0f030340054000c0b0710812007030303d4202200510b4251a45001c461644c0c2e03000349040060556241c0e080c81511038001c0798081d0454540c42a02031501c07005001d04188800c0e4100456814507076103441144d0404103d030b0b004955850800c00100c2d4140c00318070700d4500d000c001001445604c1e0414030401c0c07044005030580c0d2050b004090501c682e21405c0342034400d0403014541c400700400c41c07500140d020794000e80c00301d441818021500700d45500081c5c02c154042c4024110107400204009904181d200d841c80002c50909092401900742400b09035003600003410544814400d8000c11840d40080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 828516016 1250 828514766 828514769
    0x60212090d14031309051e191b080603030a140a0e0d1203110408070b0904060b0c011e0e06040813030f11030d0f02060610090b0c0c0f060901120207020406 68
    0x80d031004024582012550380d134000c89169007040000e102c041890300250041d580513092510340340901c410000c0f501801e61a016040e50390004500040100306c00d800c0c018a0716104243c058002d0200544101605d904030081c0280e02c2500700300017409500342c0090150311600f40c15103059407a1034140000707440b08031802540302c2c0c1c03003c200c20482003040703100707204400400701554007441444103d0700441e2484c011070041c00c02d1600b1007003052041d00c003041c0c040e040d11a0000d0011504580e2084141c945500c01100c0d001282d44500c0e9041d000004403d03040845103a06100b00040c1c6030705001d45071513030805030005000c80000240000d4807010955981d014640003622440891240c0c6080d07103552900c010458000e000d04964070000500440d0b0406055080d500540b825580f110b04001c1c240600d010034105005901c0804a4481d007200c000e000e02d066403000402c0359070018800c0003617001d00c0d40d298a115410820181c86280d80c400f07440000b02c9030300c40015032207000e02c0c80000c0250903035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 828517266 1250 828516016 828516023
    0x804120509060427060509040b0603010b06030411010f090b090405090f030a0f080a1107080a03150f0303030f0e0c060a02011103072c0f010509010e0907030e0708030301060212090d 79
    0x12030f02045040c00003d4004c15540c49207501e01030700040c406540142c4000744196030303020203c0390014000c110100002c07607104100800025158080c1e000185150b00259400c0da42400c045500b400c0c40d580107004172849403080d0030300c21030940c41c042001c0c01a20a003a8030a000741d490b000494030020082001e000340005e02001d80b41c0302c64084800500c21064501003400090300d00002c265220214400c10680748450000580340440310780768502d20741c2c8000300900c101aa107403130703803600c0545125102c00134002503003c800540d451800c0c000e042d00c845240081e50a4907200420000340700010380d12016200036105141c0303c020004d0142d004000d4001e2200c10503100104100c805607200300703040482072040b081d004811140b1040040406520754080d508042e00f030008407010342c05003014003802001450a459646008400700b581d40340181c41c40c0c00402c1e142d940942c0d040a061044201504191004500315850070303500966841c1280c404040c80e510003e0542480d072524001020460781 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 828518516 1250 828517266 828517279
    0x402031b190308130b0c060a02160204050a1d1612020a08010c0203030a0606080f0619050310020705010e0d080105040f2a030506010201020a1e0c0510021801050a0804120509 76
    0x960f4100b01400e075100881405640003610004100c0d940f00b0030a80e60b280c46800c00401441d96280c030840003d520402e24050389491240c1c10307200583c0c0d1805010b229070381c00840415070341e00c41c07100461001c3c920180c2c20041e82107942820000c80c600480b80d421101c506241429841c0f960010039600190354120b08525400c000303141801a80000c01503002e00000c0000b040080c0d40c40c0000c5030b61460a0b00e00304440c2000d10b011a519142107001060349192a8202c82c401c40c0d52900081d207000b4604418481854001c42c482d001e201c404c0c0b14100e054a410b901801480e0128030004246c0c0d001401940d11072903850340714907243d000607480101c0305111103041242407600103003044155400e00800d10006401c1030005601540306001b92440e0004548807000d101380550f00410710310f00009880810005500d003910040342c000c01c065911075100c0c22005a880b00081711440350a82c51481c02c6040c08000c100384402d56a100265a5100c2d030040001f048681d6002d030212101d100d401c1d4200d60142 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 828519766 1250 828518516 828518519
    0x80910110307120f110c04090326100b0901050403030f0201020d09231207021c0f08190c03050d0e01092a0f050303040e101a210402031b19 61
    0xc100c4801d0400b02e865444d48500408104011070b68980e00c00c281a55540210a07030019504058000c81402840303824800018100030711011901c011508207102220030381000d02032020604080e40d405090354103c564a0071511000192040c072807484001c081002400300d42d09468400c0d8199040403c01c010207100c050354034101400b84000040750880c00c40c100c1d11445080307440010381c411140100d90562800c1c9101038080000310540040491a08485044001e000405042504100c0b0303100b11a0389848000c1d03403488900c01800c0055617024824148002400310b0f8101040c1c2d85407181010f00442d80b105100751145c0540088071000300180100c118480012482e41104cdd41d40ca260103c0c2c42901664903180802040581c0c40340a4054201704424000201d140c0c140e030380d10200d4018100d00c41a07541e0b13136110904030001030313108940101184410318240309050780040c542c18140100000c2c2031580010340c42d003450000d4101c1d090621a00c920441d2034602c480c40c1111030300d030f4034894282e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 828521016 1250 828519766 828519773
    0x117280c030f090b1b0f0307081014030601121a070807030c020610030201080405150114490206030f0609160815121608060a09080910110307 62
    0x146911000c4902103420541c0d001c824000b2489407807403140e005001c1910940300c1c1c40c00304003102c160f44007610b52241c041000b0341300341031018007c601a90302030351903840d1840c09018a152101c801e0700401915180000e0410f120354001444506581021106000d200702600d42602c00075000111600395411210803c040c01f604902d030039200340030340d0310300b80402c100b0034808a8894808441c1880a500c00b00818405548904040c03907015200c1d104172a0b1030030310f0605d1031481704004d902881c1b081044820034600b608007201c0f148030100d4250001903400500c01809400e030881000c050040300000000e601a1066a004130140d06070041d01d03081e92420142542c45a048044982d94043c0b00104d01040d00b00d00c038807044415910f40c60317a507000b26448042e0303101120204005a594005002c0c1010f80c2ea5610900800d00440080c1d80740c02d0055140103190b50402030001c05000c05e103807500e42c0d0000814141400c0381c500700402c60305040035480180080e0b0b940e0b1098603405030148804140c40041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 828522266 1250 828521016 828521021
    0x170c0a09090f0b1f08011707051c02030d0807050702011215090b19030b0f1f0e1f21021309050a060b030606010f0f12020c0c01110c011728 61
    0x1d584040d0348024000345192600582c105200c00c1e84d100084c0f80b807004002d0548000e1600310040c045000b5922515a180d00180281c074080100035202802d05029400f14a820010f280010059085c5089189800340c401f511500803401c0c0681071040b4a58034000801c11540214101c5001443c903840294907112100c00038091040300b2030142e00382482c0500d0032945554031100b100d911144811080d80c0ba03e00c039515a1034050440500c0022104180c00e1007002c000004010b00501540039980c0e01d890060081c11201400303800031714200d290380601c0002a034030419010031803020700c241c0ca82281440800e00da0240c04410754006407800d460b91042007004160ba000d05070061409000481d000010540c43c3c031802d071001804288101c94803901c2070300410b002c1ca174105a600f825540303074007034144a4003a030b4424103102006800054460300c080da00190210f1441940200030a0f48564080010340090452034001ca00428110000b0384c4082c02000c0854048450225480748540b00b40c902101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 828523516 1250 828522266 828522281
    0x822060c200607030c05031e070201022406010c032304081204060507020f121c02070e1003081605070906090b040b0f1e0d120f170c0a09090f 62
    0x706034454400300608481007031032030003940100510140c41c1c041c8079502a198410fa000c2c04640b51700051007407400007070312542114685201103034800e0b0703660403a10009003013607050860044515100d03c29201107210180344250701520a08050388a450a403c0555103080a9040c00800c01592405a4600d10880d0060012180c8003c101d480704a850a1405028091070007113000003401441120003600d0615103942c2c4a42e000342044400d9822260f0060a0600b00310300c20740d0000150801c004001d904108102c010041c65aa40300d041c2403c1c100070801c24071600c40038109040c0420190003010111b060505150381c000d044482003030383c0f0f1070050003800141c0301e058001840c010140c4050704060080e210139a1008202c0d0b2024540e0300104100300308002201100140e0300b800001c2c49440d00c04d5950003032402550105d03e2040c5400c0010a05940d0b20364041c00c1001e4426200c6c080045030100c41d4203c3c00d11a80941c88550009017240c0612141e4000c01456043c149480b90341c0384550300605 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 828524766 1250 828523516 828523523
    0x504141b1312210219031b210201020c030315030c0a0e04030206061f1d04090507050f0103020c0613020d0204020703210b01050d0203060612090718050708040822060c 73
    0x910b00f1020296100440c98010306000541c000070031034141e4151081804902ca4880e0a241d6a410368030001d0702183c000d000421a030202d1a201c1409045803644902e17005502144029842c02d03070b860300015100e002c050319011407600d51200411b03566606009040341b010000d01003400c0c0594613520700c100e20b0002c2ea029805401101c000c10b40600300891011221760340e51050080d00c102090040350b4007040c0d400048903004110060116072750340c500421b00d02502510040c52424240030400c2150301004600f113040c07510400201904580204080f0b6201140b22000d9454500301d001007008500c00201c001d60203440083c0c0c0c0e00c03c164203c500135840108080340d401c00004034a400750111200c500825000c124144070781c03031000c4125002143d02c820301600480c20804110256034151805981d09455500045002e207e2280c0e11010b046444e18904002d0120b1b082808010f8411180a8009003400c0c20001d203a11440c0344c044011008450f500d0f2502413010b664201c01404c02c0c034500401c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 828526016 1250 828524766 828524783
    0x20c0c0607061d10061e260d0c02190e040f06140a0203010e16050f0d0603020a03080a14030112320f0705180619080709060603060504141b1312 63
    0x300380202c2d045040c1b0201105d885000607030798207250110b00c00d1001d6040011002d0903440d2030007041d190610600c0001140c03900c480c84031500c0751040000d40d07281426981c0c00e4100f1014100700d03142c4050845030300145c12003d01c808400d0542002e501405190041074504264202071080c4101c0907401103048804208244580303032a02d280ba108151084c40c01400007420611900200040020040c4030701114a44000346c5a81e49a01046640e40c4942c001d4510744008240c140c100c43e0484454140d030070b002c4041c3c5246605000d230608441d01c0721103010305150202e00c92420400200d1740340b6483e11525000e0b011048040b041029952040c4100e0401300e0700400780f00190505040e8407021405201c10034840c017a076148000c0c072009052222901c000722101c2100003030030110a02100e030241101480c080740e900c3c1000b6002d01503e800f9480680568a041d0984207140790580115800000248a14012844080240c2500c1c080c00c41103140c081c100d5200080e02d8003610040340142c0d031184010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 828527266 1250 828526016 828526019
    0x303020a36051c0210031404080a090e01031a1b180102010e0a050c121c03140606120a05070908010204060903050f060108070b07080d050108030703030b04020c0c0607061d1006 77
    0x1e1100c0c0d04580c0607583c40341030216840c40c0043c40d003100800440002c92034000b951205c0e0700a800030b40d00c01943c0c150303181100004d0450404e54800000005405070781c406101a52450351006869210440020200307801c00700407452041c40030f07040c000d120707840c00117281c0c450301c6440710700f44e5000d0f079590498013545c038240c00300d900c40d0400303c2c000110540200282600342d4064007846800800e0b5001c03403c00e8000e1300803158160641441c15a0b00951594000540c105103080c1040c0c1c0c800302400041c0300b8201400544400d4805004444d0301c0010a4808a0710340c03200c540554081031a5084a0029400880c1c0441d805a01c82c66080441c0d00503000c40f17404209520005858803802c6c003411b00c0c15082028180410282c00005019044c49200c81c5842e04110704c60082c101d800a8121400030703040008c0d903d0915074140904c41407907004030f40851408120b10341c0142d03140010054140030b01c1001c114003060106d942e0000102e4621421807a01c804040c00701e841d150000d103e0130710a8079180120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 828528516 1250 828527266 828527269
    0x40606090b040512030408010e0a0b0f0f0a02090d02040e15100b070818130905061006022e1a120606060f0706020c160617130303020a3605 61
    0xd1089506207082149003d0030802880394030300d00d5526100c1e442c8130410000500c42024800c1d0084000b010300501b07840d5240e45454421040302800c118003015000040c07201c00754a40e03001c9a000b003aa003000583d10725116021940741c0100c018040d6201e0f14100fa001e150883c042482c10308040f241044201954a00800010002250240760b00030b503010700c40d113400541c21400410014007580409000c0c40010303400500c0e08050900c90405094988642d4030030040104410b40d0041c3c4020405c002003410070308002d64409401d00b0305e41041c1c82d14449122105240d1034840c402256801040c40800f008058840d940c11003030b22541d01a400e10161121010b802241c02401250020042c070b1800f0450750702240c0e6a0840541500c4440c1c0c00c200024101c00100180020400741c0d80c2e008aa0318940b51000e81100354a02402000c21120740400036640c0490404181c0315606003401a02c03180b00402c111612149139080b881c0c01c1c5c005182c440c071408850701000140041294940140c982c9420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 828529766 1250 828528516 828528527
    0x10c1b06030c1b0602030603070b0301120210171f030b0103050303060306070216050118050607060501081002070f0f17030a06051302091c060b100302220e04060207030e0d0809040606 80
    0x82da02c4030320f4000702002400103620350003e54101c500203045901c0785840d84440007042c0c0c8203a2010400c512200541c400314240404590142400382c01e002004551700c042c0c482003980300801390110f030007290070707a10481c50300711004034040d5400071000c600c1903860b4079095607130303503c15206641b19101e201c000641c814400500e04007031a4002d148580c01c0c03480c000043d1500c0f4111003880e031540074070aa021440b5143c070310180100714020500840c155240a01c2d00e4205140b064155100c00d004004240121300f42420301207110307502460a04d20346c5c12500700480300e9581c4802d5911030400010901c80410040d03005030741544c50840e0b040c6c41009442030340d58102d20501c0c02d0b0301d40100602040003080380c0c0030400009164001c171070116039580b400c80025104001c2150742c0f00404d9020682c56031b03030300600d01c0d151201d10f00104540d4440341084c40902c44c0c004000e000404503900003a040040612070130704024550000f8012805200d110701c0c00740c0f07094111581c450300551800c0400035901b423041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 828531016 1250 828529766 828529787
    0x7030b010e0c04090b04090f030c0209011a160f0c1511210c01110a030f05090a0317090c150a031a01081f0b0d0207050f060f15010c1b06030c 62
    0x1002000d03d0945000c1d003280103845036101c0d055215a4070134896010411414040c11120301c0307540d8141d00001d091041090103101a084101d041101e4a001c02c0a240000115444103c079505204101800743c0b8200d6001c04000e000180300032811400081c81e001c0003448076000c10400c0c0c88034071140c40702c00691a1f998a06041f50b02240011398a03016500103448001e048510303215000ac50204854090005a0340c803d10b48032000a50300c80c0040342d0751426100b2241c0000210b0040d1266141d19100280000c1c40350780c3d00d0f83c40d010f400020030040c04007042080d014505c0179003000340071300303c05103410400d802030342140d004241800d000c85015031400404d030305070010585400c0b205482d0801d55040500f4100000c40e0032401c100720108419a0740c030041d0440346010309026940344010302e481800c0a140b14440c42e40b035484441441110300804540b2a8082d440042c0c4901c3c0010680040390400d0b2050303006000c503100f001d00009203008425120055921a4909000303a90b14441c2c21039584806 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 828532266 1250 828531016 828531031
    0x51c1e050c04240b0c0c060c0304060807180f05150918100b0c0601091409120711040e061f0f0e100e0a02040501020c041a0d03031d07030b010e 63
    0x15448005071030280c1c40f40c1003000c61440031403465855000c5050000600f9080566034240114942070800e8082105013100107056540c14200300c0c0b03030344d05141c0c2c901590095105000324840054031440c8181184090f080c050700b42c05032402c0e6901071000740080c460094a014150880105880300d010400329003105c0f101812280e03420005a4000e502c489002c0c11150880007085800500c40704510050850381e42410060300306545003425603c01c4884101c0b1600c54417404104000364200042511160f903c0456020b5541d61030314540030100100300d107403403944649004850303040c01c013001030003920500e0313110b25201c40d101200595000750a01171213291500b12915a00740883c60009003d26080250701081101142d2a0040b4083c0c00c02c088641840c0d4542c0810304001030340e410031404076071410554ac204240c454124000c00391000c0001c0c040d004030412900700d420184a9400840300d2480441d400614402c0c074a003032620345c04035200584c0c00990046c0081080d010065100380107042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 828533516 1250 828532266 828532273
    0xe06120312060f040212070e060c011d0c03011b1101020f07081b1204061803050105040f15060e18120409020409050c160b0709050a060917010504050c0f0406051c1e05 73
    0x5c03a1751f022100e4018159000e900468244400e07000070b0001d005032218180d020b44410580c0c42140501840c00e844107403210720a03070501c0101490032011400150a0550381d24100c1e00307011451942a029206000a0301c07085540007070140c1c18800d5020103044001502181d040c02c1c290710102c550381d141d10045000414030000c01007088054040c514462903c1c0041d08040d03c215030383d0700c0300390071900204d405036038000d4400380352002c01c487c01c498202e00b00c40324181040401d0504404402c03041000341942c1444c00030350340c0000c46080800090240e5890301d882c0340d54441d00c6801c0711001e900903102d0143d03030303906000118444c40781d404141c4410700110407450090311416181c1c504d8205002d000b40080c05903015022895442d074051000c003425468484503060380c60f000c00154511003130018940f25900d400705020000c0c4000c150301030a81001c60f441c0080d1215800010010038540c0d20207076100038009038050055844200402406004283c0014280d803510050b241c010200100101a40c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 828534766 1250 828533516 828533521
    0x110405100b1812030d020c1c0903030f210b0f0114030f0c0706050c07110f0a180e01050907060912150221040303050a150605040e06120312060f040212 66
    0x184105044010000105840d10301c610b00c070300c00c9085602017590f4180e40350b00082c241c00542d07400c204c0d80b0840002038403280450754001100420614150000030100316038154100c1859208030070075003140f047d818107107070381607115440d6400405000c0841c0f801400440141042c640c01941840c0342039881c161094a103580340c0d8900080b066004007401401031741400f810003c0380040c826948240b19000c5117981d28404c80c1450120312418158603403280180e0940c0d02101d48a400d00042100c842c0b070034041c1c4102c0c2c0c5850700800750a81e0b18034030103550f10f40b10030420543c030000303000d04c02c0714240e480d005a11391325400022000c804205000e07040081607400548280050750050070046c1e615051148030403000519500c923130609403001d81c000703a120401d01c502d40c0040d210780780c5c905003c1000048200d1400602403e10300681c41400c41c080784120000d051600c402c04c4450405502c1d5007a6540e4440c0c03001c2401080340d0a0300ca080c0180c0011014094909042c801c4074994400e01d610841d459 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 828536016 1250 828534766 828534787
    0x9100e0618070b030705030a05010e1302090604020405040e060414010c021f060308070305270d08030907030b0115110304060518040f1503030e06070309030209041707110405100b 78
    0xc0c06000e405107410300c40e5010000b10040300d00c001d0b502601050b036400c0d07030320b0a20014000030f560041e006001480102c2c030904c04031a982c030030412000740e0b042e5111070840d44d40e000051b0090045a2180d5081410012040c1107080042461882203100d42d54442c10700c01c2e103803411400c07915016020300141e844010040c1592030592610140718180520219409403665103002e41c0e40c100c0d502c2140405e102054030000850b1001032400041407000ea100741da10b8414001401d00170040ca00900500c0b000004900d070f8100c188013800c042d5800c4035440902d941d454400e00e00d220503a500c000b0002d920101680c02140010044804850f4955105401c1c8000c0c0010402c1008140607104d520590f61080010108103a0180f960070740c250340582e5180314554180640064401c0c03400501c03c0504000c00000a80c1050342e4005a83e0152208070050b51145003280200b071048902051080c404601a01089031552050038858415101809981c82d03084501e410b000d001c1c06a101840703c01c0c040380852 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 828537266 1250 828536016 828536041
    0xc1b0f03020913170702010e01020a0309230904050d18050906040e150106050a030b010201023906040501060f060c02130b030a0813050906010c0b13021f0809100e06 72
    0x85800542018844443c0d5a0340c222110341d42c0300030350b9050501180c0e0f50103640c1c0000d941c00500c40c0a00181c140b407042507400600079042c50145c600121305107d000034550082c00c40348240e90801812502030741c1414140690b40d26490240180002d42d4803054080442600b0204400c540028240c68015150b944c20000940080c800e03e0b0190b10130480750782040c0d0740c0c0030102402445680c0b1065174810061780020281c2e900741410a05580c010440c40d840040e401d0b00c0515690071041441d1211000c84010701002040f14400e44051702c640403d00c42400419441601200e4808940f1401d55645441c1603840c4500c00001a43c40903001802850b13409980d0004648410010203590800c3d0195031498007a400c40c8100020020301200d007440f05080c441c03103c540048003400c06035540c07100d2ba0b6030a460604020400f00c000c91150100c00c5c05c64491600c69146506407605448140d0307004203004000c6030741117926890030320903060449143e00d5a0b00c80e44144030884809400c2664403100300440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 828538516 1250 828537266 828537271
    0x2040e0f060d051f0e011a090106030b090115020304050d0804090f2a022401180905030d0c09030602030f070314070203041403070902040b0406080705090a090b011701060c1b0f030209 80
    0x41e40d03a295000d2005e814000c0c41214035441e503044d103d5100c024041d0a21031210380507006141810301c1c2c80c5082c403495444007400c60468070b042d139505d0068201054101d05602a07540030941006020a1020400c0342050107002504c6a10000f041410318614100d402c0c3c420600d0003180091a400140d04540d0b004111542409103a0044804c0107a60003034441500c00c0031010410315600e90001400a081d04100028003400d9140007407080e00500d85900c0d46910078243d2044074a9501e000d003000b940d000701c002c90000c58200da41191a842e150030544040c00d002c40c1e008001a02d040c0f04030010385040c8501c00c2c00350f203066000b181418101080b9010f4a520312100b1380d81482000d400081100c1c0e10300080001d0040c1c014426103c43c40c3c0100500702e000c010300050f090200511044943d80c070360240035000c40c0d00c11100860200300a40050312503a42c148829100818803900105d080341e04403078580c0b4050311039001802072854175481e80040301e5160207040096084900100050316040316a02e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 828539766 1250 828538516 828538573
    0x110a03020d09080a021e0106081203100510030f1b0e041508010504060c090b0a05271801081002090906060c032104031209150c021002040e0f060d05 65
    0x801c8074050b00c0300307103c3d50082541403006078082c0078900040303000850b0a640d031885190090000b2401c00c0001c5817280101040340303500c0741000c0006818108812a00310052038041e02070440d80c4c1c000b401c000c1c0601040c03d00303612902d0412080000e950880c0400c8040c54025070348001520150b142000b001d0320014004084d85a0307110004900e1040030700c40c10b406140f1a40c000210b088800070054868030403907000c2c040300d0500780300001e24190020300b203603040041415a041d842043d4521a207014890148140d080031315404107200c1c85000a4480f41629840f10403220300c660390344050fa050380715080b0425080300e2500c0100c0d4a07810981c002c0c081d183c10500c1528102501900c01c1081321044d0b0604828201e040f10501003407540110b80100c00220520701441000740c03580300c240740c005a54400107000c41d0b6070785030101d14078802d02410043d004004000d65846640c0c000402e55903c0680d9928040010240802c60b10301d4801c0c65440d0269000d13014044007142c44a00031041d072000c58005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 828541016 1250 828539766 828539771
    0x50d02070507140a0b030c0306040b04090503160b2a030411090f010e061206040209060a0b0f0322030c0809010c060504051b0a0f050d080d14010315110a03020d 70
    0x140c009038003484504064180c20008054070b92000041183d4010300b54402c00b62585c0c100180441024500210f03580301c00191400b080101109000c24000d10b90010040e00501011404d0054156040f909584440c0030b5448014143c4949814111184002c5501c0c5060a4041c61032020000100081c0d9407040c0215900701d00708600c40c01007000070354100e400c1c81d01031908000500c41d10081d2135140e50840d0007500c00500f82002c1c45215a9200340250002e84140c80c800b001880a9075200c0c6000c0152042c6107030ba070340300c0751040800e00d240c2e00b058980000700c250300100c0305c1005a441503032484a5416941e161a10b944540301c0d0302d9954021410241008080f080040100c1d00303a0082c82e00a5204100a140711100040005c200210314a40c00b8440d00301910108400500351040d581580c0d01160345c2c0380e0b11006071070284c0c0b4501c5860147c1114505040b404980f405002c00218101c0e40512244040c514203102d8020440e550110044051001403045c001c400b8825400f404e480c02072060300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 828542266 1250 828541016 828541027
    0x17030409020406120e070b04140a0504020d09030905060c030307080a0b0d14010c11030a0e0f091612021908090c0310151e03030302070206120702070302100e0d03050d02 74
    0x40c1aa40150010000700d81c8040140c4420760462091844411950300900562414000205507e100c0c91003410b04c0e102c0c4a42d603074405a03485000d1031008090007001150350780c5045070280007a14040800b68007180c150361300003400d82815400c0300d00300d1440038061455542c850070141d500c1e0102030030680c0709540c0c0745502c9449490b294200c00c409800b5030300108911406103101d81c2525812510a82007100d500c2c00120780300b5000056071103100107400c121140700c1141c4045520601005925680720804074140010608000308400c1000c1089c0c0d2814040c0702000921000d80c40b0301043c0e10b04a000507003609000d240305800040c1c21541c00700c150355640390010002403410506c1240b14084950382d64851105600f90100d41c0018484410510b41c0c0403440d40c80700c0080e071014400a424182c0000340001195110740c1200d00c000c2c540040303c0e00c1382c144100000d6480310f00b400304070301807101c0c11000b114050186040d040000b1000780500c5d040030407640d0880701a080f4003411020079409001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 828543516 1250 828542266 828542279
    0xe1903210c05100207110f0d0605070302070213050649230105060d020105040905040305040806010b0c1911150c03181f1211040302061908150a170304 66
    0xc942c42444a0280580c6880711410701a6003008141b00340d43c0324140240002e09251201100c0c1406150003010001f0550b41d031003c240c01a00c90100000c0d070203149100e030001c01003a194803086c02040c080e28015814030405c445000442600b01440c0d04401c04890040102c004c814100741a0151141d1400325440c1d5580d00c1000c2d50340440c41d0590f08075403048003e00d106200740b180c01d0f44041b04685503040401d51390006415842503016460490b0f860710000303400c0c5030140e0300721402080e513030003102d04543e558040404281c0202a1400481c003400005542e800c00d24152421640d8204c014024410510010007000e40b0107840790b5025800e0034030030004048402d0018141c81c95503a2400e03054029004100b104405004040394000a034402208040c694005c800c10402201600e0000b100964503100c1d190b14043d941c0029030010000840c140414044200b04006a000ea11180010788035240b400144041035080c0c1504038000c450100b1400e016040d120340c214402c0801e80785410384800303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 828544766 1250 828543516 828543523
    0x4091109060307020d08091c1b0c0602030c060604060b1902012406080a060806070c050a1209140a0825150801031704060c06020a03020d09030e1903210c05 68
    0xa03440f0700940c010400b00000ea940004001e0f40c001a5003014011170360512440d0012040400c900c1010010050b49681c41c43c0c00c00308513015443e80000c02c21a0641c1d1341d50340203680703500810b01c00c0081c3c0146008240130f03091501170350301500c00c18402c50381005141c030342603050280e81203600703c11503488200c022100303e040c9010841c03e07103610250803101810700b80c1c05401024060300b21802545401d4040080340340c04942103811458520b0819941c4556040c080c0c03805030700b03510240075000100031000c01c1a820881101c1103900d040c0d404140800c42200308070f008410340c410b01185e03410505410301ca0741d07048400c9480b8004102c0007030303001c26262208100100340c001042e1000c100000014400e00801b000c9070310f58084411001b0707240606042004141c914229401401c42d50041240343d41075029170181c0341076000d4091708000f0003000b0f00f0020548a00616a107000300400340003220821448002c40041da500b000c0b84820014081e900c06101303800221514040100d00f88a0310001241130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 828546016 1250 828544766 828544771
    0xe130e0c010908060f0a15090501080d300b0a090e06060f0a030c0b0706060312030b01030c020120070204060302060408010b1305070804141609020d0b010206010b040911090603 77
    0x100900510329408009407080c880d40d041050154402d03000c000600300d1382e88015500c016540030108414070030b018004200d440982002019500b800004a02c00d44000b030340610165441d0789007441182c0a04603070309a82c004800451103602c601c50f903814000d41c01d8112481c240e0f0050403044030399503900303008422105488080003541d0086828003455103890018108000c03000c8504044c9145166140b90740c0c55010b00c40c00c880801c000c544c0d582032040e0791388164000c0d030f00301d03900c501001c19a00300200100f4074040b10f24040b9141441e100c40041c8140b090009111940620502c01115031086680607080940200c2c0c0c801d844010100c0181c41d1540074100031b040100010540075005001c02002050b81401c100d41240340004120840c0c0c1e000b45503d030032031303000040c410b0303003020508405080a0b0580340c100c245040d100400215999264020400b50000d048200401226070004a0700c500c000c3c454084210741c103000c03e02c15410103502500c4402524100b281c42d0041c0200412201e4104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 828547266 1250 828546016 828546041
    0x51315081b030c041407030b0d0218100f0605160510060f0e0f040c0b090d020424170c2112041401020703080f0705150108071a0307020a030e13 63
    0x41e0800e0074504003048690019581110240300d03440e0103100c0e01100e060010112403c045e00c81c030803008a52a85880010310503000740800d401d41000c07150030319814000303441141035400055000550402203140050580d0416900c062420642601a040128040f001035409001e011001901403a251040400070319045024001507490728543c24001c004c002e21107443e10030080100400160f0808410083c0c480755401a07884500040120b0314000500000a40042ca84404407400078000b44001c0b1f24000035041000a040c0c0340e50031050003c4c01400301c20160343c0000302006ca14034103001500c90038541d610a06152030b145020399890046082c007032158411b0001003c0c04010105e0310842c1c03401400b80000c0420616643e1160440c3c03054100c80c010048011a4070403c100051040a440d6294002d0702105d80d40c40303602c1c1c1911181584250b09070b056401100c6d244c004110720a480c4265001d4000d0406a10541c0341a161044401b02d02580f10000500441c50038041344202683c2100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 828548516 1250 828547266 828547303
    0x925050f191b020a030f1104050106120e15071407080f07110402031501080910020d0b10080408041a0913090201021207020f12070b030901050708070905131508 70
    0x91801010b09214000c9141c0702c810070314040401e01584031080a4000c81c0e40c0b10b450342d9101415814070750003240802c51502e03070040c00c0c8400006c0aa6103d00300d0344042910391410044072842203005030b074501c549a8007021039070b854000614000d0140e503c80704000028012180340503c1c69236036074420f5002283c9203c80380c82c0803902009221316805d00d103c094109450843c5541030061802e00000d0303402c1c2446041000d010005201c450003800380540c40000010300307548416500302613001401c3c0c20444680191080c0760001c110900c500442070265030001c401c01c0c1f62504203403000c140d02120202c07180c600c01302004000074984844540b01032000103210005101105d9100080c244080c410f18401c142c1c0d4240041400759607003201d03101e980c1380100ca43c200c52840c01c1180c00c0c2064102c1d40440340f00071010080126030703041900003901c2031311155111042552011416a0208401c2c010650860b092247e0002443e4069200e03040c1080d17441d84114a196981d0111460914000c21610340c0c0702 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 828549766 1250 828548516 828548557
    0xb0306070f080a02030c1219090804031401110a050a020313080a1a0105010530180d05040e070e0a03140d030b0301020c2a0612060108060925050f 64
    0x142d00000780354001c400c0c40029451801d001c094004680169961007041102802c045203407031f40f601e0041c3c904120800c41c1880700c100300b4100140150018401552114840b100c0c181b009407042c03040384104030380300e44d500e070034203d078a0403c4605820010032102076120800a401124056104403030090002d140103089011b4a80350501d402d02d440c0c42182c2c06500c41000501440ea00700007a00d802d000e856507c070503101030064004030301c14041461101915625402d002c80c821320147c0840c2c020b261202107402440320344104440c9413007144103d40312640003001140c40c40c0c0c880c0900399a6120000d1141e400c0daa06c0346c40d9007070700142900c02c141440d40602d40e05030600e6014003a100c011340d0100d0085041c4621505283e480d4460110462403d4601c44024a196031411112a04980300038040607240c1a8503c44c0040404c4242c600c40d01207980b0400082d0603140c41001980f242c0250305c44003501d01c8041d5046405440317080c3c000030178481e092240b8210072003c100600f4512806001040011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 828551016 1250 828549766 828549797
    0x4090b010305010c0306150f05040f080703050d0801030314031503010c2a050d05030408040803030c09040e21090a0305100506120a0309030809040f0e01090302010f021c0207060b030607 81
    0x5441c0c0d404c048090609101d4104024941ca100c40c020650190600303424010070300c48101d44901c41c030303040348812032a0160040b4102d13000080000c00c0e00d100b0011203001035034064003603d2140c801d110040001d0841814001180324030303c00356800c000c1d50524074000c441e84100190969101d01107080000d180a10744030402088440000685240d4240c1c01c4220029a21100d4660340700c60b1883c024401c001003c00c0c1000f11000171140204481d90a4945a00f420024400c6079031110212501c036600304040084120800309105015004c0b0701801031014a50030020301003900604e440c80d501c8500b4460000201ea004d0040a07a641094a00040d8501d040010452000c03001561407544d0f50001001000282d08445090306032600a07041c0e07030b12241c0b20740004000e00312043d81c52040c0d0342010020b250588054010602c5584250000d01c480c0c0d0100140788128041e2502c2041c40c0c42404d40303540c0c00301c40d03540e0090840318003400000c1107410005011034941034007035540c01c1c00104603100751001c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 828552266 1250 828551016 828551021
    0x20903100c0915020c270708010609092d0e120903121903050603010b061b010f0b0f041503081215010c110103051024030b060909010605160204090b01030501 69
    0x14004448283c11a0032030f0800c0295030361170005940d801180c0d400f0802a4074100d4182d100b00440040c81b198040e4907200d000103042120030f01c656000b2a100c4c16000c00d40b00c156000d000c0d0130242d800c040030445041d203800c291700f2450303481643c0411aa00c2250410300441840074041504650100f20360381c0300000d0030b051030403928902140f04e03404103200088421400c0590800704450380e00e40400d26440300c000090043c840e003500f40c0e81c04440000c80312296020000b1103240d42070011c000f0410500000412003e0310900a00340394483e02409420b00c1701d00c1c0c03641c00440036031540918410415286d030340c0c0b64116400450191410000e12040100b04c1c1c4182c00d60a030000c01c2803801101d40419a90703048508024a0700c518107042e01d9000281c000843c3c0c0d60603000074202498804140c1c52038800507035820401701104030000342450fa50980078100842241c000540c05011000c1c00da28007442200c09070026041c090350746074008004405030b41c071030180c0c07009180201c80111055145143c01c40c00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 828553516 1250 828552266 828552269
    0x103201e0403030203030f041a071e08060f0607030306080109050c12070f03020d05010b042c0c180705070f0c0f050405040f06020c030f03090a050637020903100c09 72
    0x540300d000308420320000b80e0100980760044071040040fa0907803901d01d056074a5000080360000e40c00d0090081044440e444041079850005810300c820308000d03a580100c4000d44129060342e040144024155442d04005005200890203031030000380854581496909451030042c00f038400b5030001c400072026240217181c0726403039200d04004007203c5150054011407402503100c00384c42550303d480070b0780502c9001c1d0010307100080024000c01044445507048902e0b07900250740d6108000380c2984a00315076070001100024004014400c002030918220310464401c80241081c0801c0014400c0c08001001001070b030350f071f103031203401740d2441c103400d0003842029503080341d0000c2d105074180300c14000412449a940c0d03911030b0700b21001690354450b5800e0380707146115010030341e02c40d0540002045101000407428491040c480d0080d241c3c191106407010610800e540062120ba8107100b41c2035124400110365017554052050000d410191414002801c110b49109251507042d2039442031040300754088075610 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 828554766 1250 828553516 828553567
    0x4230a0c06021e2e0227010c030c02060c0f030403140c09040305070318050d0813050612150f1201050a05010b130501081905161b0f11010320 62
    0x34104296841c0c102e035149140c80d12140d20320b0307201311501507000340750119911012000100703659403200360254241d01c00946075440c02c1070282400c004469031046801440d15034041d600c055034402680c080005035403010400e00810b104072541600b1403403052002d40011401094044075078018428114209011121303010311503c0100c042200283c0c02006940e4807070b03050300d4841d6521041c1c90001c0c194003d02c0d00820307402111204801c0402502d1002000140d030f01040c01d00c1010b50382c505001c1c1600582801c403807491054400100f0309504441c042461040c02007803140c0b40a80c83e000b05100d0342c0701071320740070f800e9458000300035444c9686d01610b80100320410869103096103101c1c80540510090140c00c0c1001300c00d0001c1031100c04650490503890500210030040ea080c244030011011a004c51800045951039040205003050f00801d020501d4100c042c1d81c07007048441d6204142e005003c0c040a041c142e441e4000102407094644540902c0710301c0b4819a030b034101a125070b6181200b802d060305c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 828556016 1250 828554766 828554803
    0x1507080106080403180506031518100e09030f120402031506031b03010b0a0902070b100e040b180106060806010e0406140121020a02010c080c1204230a0c0602 69
    0x401c10035a0020b0354a52141e0545030000400148510145800e101948101d03404034000c0184040c00d40c840026005d50581202c8045981d64010311081c04d0a00880fa1030042c0c0080450400041e400905195806400b400540c1d2902c1c41031030aa08080c0c10414802030704203c00e10130041142070400c0041a914040c4c000c43c00149086000696199080940301c009500c50b1382d84014179403403d40000c007070a50000c004155082d2600203100003500154015110000802e01146e60f81150500400594000940044865445444207151020041c1c0641590302c2100140e0034401000c0c4210030240c1099541c58049041501c00101030401c20000940b096150100c06c20200c1d40c20b0241518408003030030310b00304e0f01100495003c100482104402d6a42c0d000040302d01e1042d90640c004a2204c0054a46a14980b60702c90441c6280c00303a00f044140201020000c9004600c41542003c042e000d5041c4640c1204420102142000142c0c5400c4440c4c3c0380c03a4205001558061101e0341c83c000c4080e80b034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 828557266 1250 828556016 828556019
    0x303030504020913020916030b1c03020c0910230d140601060509061207020c0a090507080c04120201030f1b03020705010f050405250e1f0e1e090102040e01060215070801 74
    0x500c0804000d81780090105084d070000407e18025040140030072030040880c101c0686001c40b0307410000c0e04000031801400b40c1d0300f20205526000000310301680c61121800354460528090a000d004016144448406441440310040d46c1e0603031450003251190140c61070044150308100d24141c81a048a000e1010900000c2416280d045c141c40c9000c50b00320403d180780d01c0b52001a07003419100c80d00a50485d20b00600490311392942d40125003e6100717940d9205095807501000030060246000f5460300d200b03080c2050f00598842e400203002000e11020000b80d42013188a0840000080648403011a401141140074800207214158030718400000510030303840c02ea50303000e49a0103200a020301c100303131540c0705c000d81c4812a5112805030000384041452410a007201c50310180c1442d038030003440792481201007060300032070340d40d0360240c554000039001c8802203030741d1095803a00c0144500c4440d03500340400550b2880042c0c606000304055000b8000c030040e00f10f11402030200003001c442c284070fa105c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 828558516 1250 828557266 828557269
    0xf0d0e0d0e1e0d020f04090c1406030103020904110f0a080d0311040e07140f13210c06030c0c150b1809060403030b010302120405030a030c140301060c021306030303050402091302 78
    0x2141c54021408860f1400d0100003840081c00b03054126010541091070400d4070300412150707480d80015903901d01c650160b64040081044054072090000941260304a40031500007101c1052005a40703800801030944044550b0110740c0001d10b03640415010341c80f031020030310700355014800e81c41c2c0c01191107255840c06007030403010324128401501110401031040280c4400c8000c4006803041464880c2c101584e030300541411801d51884d40c020078801c060318921310900c800c1c011100066482d401b807240304501c0d1500031301f80e00902c500e42101c070502c60180031a60024008440134403c401820794005041055441171007a40042540300310b201d20104400c0c0064464000b8480f584103a0514001c1210341554004a0190107030700c2110914a584405100c05c00c0408006003114900c1c0d2340e010040d00f134061070202c45044026003054804042040107106040c8a92201c060060000d48115040308003a03d1003070840300c040e4010b500003580d440600c811440c00c119201c0d001411584c2284960840d40c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 828559766 1250 828558516 828558559
    0x100201390c0c03080a2a0303050703050702101a030313060f0f0507060b042d0e010213030b1b0c030d060b09030613151811090103030804080f0d0e0d0e 66
    0x50300c0c1300d00104140c2d407010300c541032580c030b00500a03020341c010101504141c0a115034000003140031030300340790018503000e20a1080300d11400712070b402858205140f4044e1001000540b4003481c801d03c4072203202a00b074800f04014115807040c51380219100d4039022005010f032004110100800036802505061540d00205450540d6003042c000541c072003200c40014010280302c01e0b00f00515003265101075203080e01c1d140d4940c0c000c0000f8414091501030044040c203e00c5083c0b050100010a00d406101055217010040d502600c40c21150b2541800c01042280c190031000390800c4a910005410f2441c14007030040390010004410650b0806401c14000b07a00c4100040141c0c4203441e0340c0c0c140d10140104403010710340758040302e4010080601b08505940712a80905025140d4102c1241c1d0801c240c00c180d40e0a80c100c0e5010790350031a958541c1c0d40c0e11100d99200fa4a039000109092100010322051482120003c9018a0007810f040107040d401034055929052840c0c454000f0750f41050800e940300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 828561016 1250 828559766 828559769
    0x301060801090b091c0212180409080c0706050c1906090c150f08010b040b0a0201090209240307050619020c190e0a0b0f061c0204062d050702100201390c0c 68
    0x7c0301c0c5a61640c55000840f100c04007041b013500d5100382081d444c1414001c0050003004a000144152221240c03250402d5810780b203146002c0c95240c1c040c5122002d10500501568915441000d02048130812903c9450031181d96402241d070b1035020500300074100b604800868607941290415400b01e41c9401410741d414010b07480742905545000601d060b1986c800c1d03200410003a4014078081090621030b040d412a42c41b101000303603810800001804451800003116801c40307100428140c5814048010484144410a448810b601c5100c0c0007814940d030b00030443c10b0300888806525000380c40d012018040702c802506440341e1034030703000410704c1603143e0319200c0c880c00d6011380f510f03a900d080e030350203d4250708480022149207500c04038020820551260510449143c406400e044400581d012840010f03600d17500b1001180c01002003c0c01400d20320202510407041c2c0c000024640454084aa0020009000d0034800e40803000103002448a2100311006030f00d0a2030000a00d02650359400f9090030075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 828562266 1250 828561016 828561043
    0x1103040f03021608160902041203030207080c120d0c031803140706050a0b12070807090b04090b04050a0b0a09020f09090f12090906010804030e0409020301060801090b091c02 76
    0x81503241850300030008000d401c042101100d44150b41c82050a4546804880940c425400028001040f805a000f690300b51480c0130500c00c00c03c2c6082d54207038000c2d40400401c590303210f000d00560b00a400d041c441c4068051281740c0140c1d03a0b0f01c40c008801c080391000100c10f82030501c1d048110400c0400500070018441c1d00d41003401700180340d401203403054003802900a01040c24441040a00070080c0c11100c00c101c010f99566060a5500e81850348460705130040b244141e0180204116005150b005040c03100001390000800500b592200d8040e02011203003541c60360300514885041000c3c181d04280c1c4440501420820b10600303a0000c0c3c0055401003e0a1107030a041010401c1c6680500c005104e030043c0707004588050a11031446079280d000a000b03540f1941162002610320f5004942403480740e51305a880a501d0980b080421005062403901680c01d9980c1d2100810503010074820704010074062003115005147c10821a45001d450141150440c0c0d98208000300c0140c000404030f445211 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 828563516 1250 828562266 828562283
    0x6030f070c02010e04020a03061d0132090c1305040506031002030405151602120f04050d030c05032a0c031e01151d0906070f0507080f030a0501080f01110304 69
    0x841d800100c2e50341c0702460446170310520010341e418006800d94801d00494400403252540c5c011000c500d0306903040309204040e02031a8040b984000115000111103001b9054000010050000710100310401000c03a000a51039000040b0700d46540c8200000a005081c201c600344090310300340001c80d484079007804c20020b8454000c00441d080000070300280740c500248141d50b0080380b802803008408480ca404031031015020f8100c402c000504e280c0205e6181c40030360350110b841c2520b000d09000220303441c0074041d070421003940322031000114180f005044007409100300c20803001c01c00381c140c2c00080d8a0514182250300ca001e40901d1600c000c9240b81e441c00611501d01121100e0b41c1c1098090b203003000710105030304030448000c034204d2040403a26140d0800410803d42556a02074001e50b034080c1500d48202040c00d459004a4841c0b2074402400318500c10b405003800c290410701c505030781c1d41040c1c03000944580c88500500c01c0220400007141000e1454000303010041307070080005035900c40a88013408030350 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 828564766 1250 828563516 828563537
    0x30a231b060a060f150507060c0305010e0f0f0103020d0317091b0105041d131406070e030d020c1311070807050c06071a0c0405062115010203040b0a09150807020c06030f07 75
    0x5005006079011190040b405125210b044c8600400032f000c24000c5652000102000c41c51072020300c0641442403980c103031440c8559003590200482060107010880030019840c1c1d02401c1d000d04408428021541c000017000a0800c210301d21041c4d0780c102060b07604101c03041c481009404501755280540030350201383c45410740c0b20288440f907042404400641286400c06e00c60705090b000180c69403040e08155554020311980108054440c0200c2111f1001030788000d11070017841c0741840410481d00e600300c100043e03130a0303501d60705c0c01030340c0013907800352034040740402e140d0107025040c4040c20440104031815072a05001c0e507956402d98003003a054514103207500c80000c00c40117000d030444014102c0105400c0d110784418114000d81420700240d01030304212a07003c62280e1017211102902e088058001c0d6081c0342c02c2005544c0107402a520040c2041030080d0009a10090001c0f030b501684620390326403d10b4a0034400c040e18004061390114011401003080210310031003280741940004807440c00b01842c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 828566016 1250 828564766 828564809
    0x30c091f1412011404020c0d1d09040f230a080c060915180c0d06020c120c10020c0109020d03080f0105030a0c050103050901090813030309050d0302030a231b060a060f 73
    0x901450030029140d201d901d148c0311550f50860030000b03601c0190958012031100304814403140c41000d07a4010140c580034003804001542d0182c101203058100d08601c00042845050b00d8640b0304900c1090320080030000700c003100050207100566001c2c241c18000d00c600b00240e02480640c0310010020400341c001c0e24001d11160509001592403894005c280507440c10040c14a00002e600030041c00c0c0042c491240c50641e40c00c40345040e207450307486d18000340c50360708240d10001c4003951040d25045520f5507140b480c8001699a0000803880c1c0e8000d0380c40038100e15054000341c85218040c2c0005200381d101001d0f580002c0d90400e0b007642910828030780460310b621003915860140c03280b4003006004540126000341c0348800e005000040b680695503c10459903540140a0103560404000d00140c1040106000450249110010041810a200c480800540b0380c0d8180c03070f0088440420b101808600190b0400c404010703146e001091010200549031401c604d074032244c0c15074030805414018000600002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 828567266 1250 828566016 828566021
    0x6190c06150608401502070302030a021005010e0406022d1804181707080a120b12060a05130515010f121205030c091f1412011404 57
    0x5074814034044036542615034101402e240c4085881d181880404882458201060403000c1800d010740d070070b400406403480b03044103020313561520155400200c844a50f01800441d01c020400c040c000e41c050346e00c0d01b20b0544000e00b000007881c4c07402c0441e424a401404500302c0c201140e43c115511140040e940e400004035503007a1544911034050f1100e20b81421000d040c0304a0060600111401d448615000a141003204584031100755004e032010000640c2d0000c0c2d400440320b84940010700d041030401031aa83e46500541c08400080300289892180b001511500d00803415001412a2401d4210400b51041c503030b0750a00034440c483e40c0e901c1d180071a0300f072100715041c2c1c814140c0040603240881c6159035404510b10082c46294158403482c040042d560709403c0300011220303031040081c4078840950310110741031780003d070664400c48810003c1418903a034041d981809604116a078269203121000c0142c000c0440f0300138031140c0c503810848050041e45100806043d074090152600441e100300010600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 828568516 1250 828567266 828567281
    0x31003020306130506010603060e0a020a05121801051503060619052e050a05070f0219080109060c02060702071e050613091b05030c030628031106190c06 67
    0x416000b000e0500c00518000d505040b42c86005808039011640c3e03d210840031104107100b0380105030314800200301e40d01d11a800070520300ba07840c80c029080030001c020340c01d5181000e0702c0c0c480755414600d000e1600406d081c001c1c3c07039002044007000f90407080420007198840b140201894820885a4600b11111035580f108901500b00942183d100070390902101c03034070590700703410a0f005060344129414141c1c82003040b640381c3c950039170340c142c20040160307910201303e10101030030ae074403000800c08032000200c9040e0312001084a4400414400070600380380085a005c801030b1011074200e80100f0031510340001d0490200e84020080000d0324203850b00307416890f100d603000141c0c41500002e2034400c4400040c5101d080d2868141d0801c1100340c1200c203c1c02c40804864604082001400000d50300d4415101079548400c002d0700540b04e9019541e090369001480f1060015101074480b000e0060020b101d021181e10f100030b5404918018801c0103c0032052a0740803171a082068900301c04d003c00050303802c60754 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 828569766 1250 828568516 828568519
    0x1091107020612180d02030d0e0a0c0312140720032803020a060f020a02060c07150c0507021207300602070503070b091c0c20030a05060a150806010602100203100302 72
    0xa12004170030200039202d42c841c440a00c00e0754140900ca0134049008078208140c05d03408200c2c01d40003071640e0f4417003050300c81900c0c4480034040560100481854003c0007040c80f5032080785803903d1016040000b0101201c001e440c00e000350310100000680140507130101c200007085150100400d803035442e0807460440307043d40060030700782040304c0c0386c1c0c00d8101e5401a1801009a13025034039140d440d060380454034012100060851100e6030b00e403840f101c074248d101c01d06854192418074a00090364000c504180c0800e64905e02e0b6920249041020160307a40c075607a018114030601340700240303c1c00c1d95100701c0c0f1500d120141000d68000f51490421004000b2102e02030340c088558a030502d002041c0c240c0b211418502c01a1030080040142d2407544a50301c034004076984020140d40a00b408007188210900c1000c145400d4400c506404010500802006100d96201e840205410000f13030051000c00040d5400b04415520050044c06415008101a101c805000c0700041e12a0340d4210407841140c1e80e640042e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 828571016 1250 828569766 828569773
    0x130e030711090105010f140a03090b16030f020412060c0c0212030c0105011706070e010509041a0a060e030d03020304030e060c010e06180d1211120109110702061218 72
    0x2901040141c1001001034441121034400c2d6a98440064903250000011a00000c3e51500220031041d0500e01421042c0e80c1880c0014481a4560f690113011006403812b94488210700407225085602d40214183e009183c0000d43c03d1a2900d40c03080301d0000211001482c09446102e841c64062280755003002254004007215641a00003c00507280c1c3d0159441c0c841550a00c800491200d01c443d8106202c00003400c0180200d5a519404480c42e95001791103030b0410a0400056000d40d80d1802542c0307201d0600d00780007a0128032101081701c0454aa40700505100151f00d0302e4060355808540c0c00c4070140c403424003580d29500d6103821035000700991046980503038003146048841030b056002100c0c407a100c0d4203c0d501c6407034080e038041c1f0f10368440603661030f1680107104a024091090800000601d8650b40c0824100c10240c158103060700324801800c0040790181c0100910701d83d0b401a045400c4407502644d192122580110b469407080400d500b0600c2c0310240410814181c0000d00c0c04aa0400c6095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 828572266 1250 828571016 828571027
    0xf1d03072405162c12120a0302040503060f011a03070302040503031c0c0e151e0301060f1209030504091a0a030303020d0b0f100305040c030f050c040e030307020a02130e03 75
    0x200c0301034454840c0c107940000c074044c0600c805125040d20b072032068542c040801c914400c52008115942512040c4c1e40b000303004a8896208001c0310344090140d1b02e072a1f407009a1a142414140b511b8400c0003012980a1540a00108610781f00d02c940b43e00c000501d51490cd40d04c0e52102e038240c011f446507600058142c4000134541c004c01c5075580c440c0381c1a8100600500901e0a030b0704049416008000445600452040454185d40024002401160000900c09101c3d840038060038840d604243e201d20081078081600543e0070b13900c0340244071401038000d0100700044007500e000703001b40528003440d0781d0541c0d14041c3c42d4074168026008101800d0060480650ba916450010013a402c003030241000141040143c04403468026440007240d9000ba00740a075020710082e04602602000d0402d441071448607034044003041d1840208419a8000c500406400208000384011100410760804042d0020320034046c035180c0c04184107020035011961a98600307080550360000b001091740d43e91191100066 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 828573516 1250 828572266 828572281
    0x19090c052110030f151b201609020c0601050306040c060e0d060905010e0610061704061b09030203060c0a1e051b0a14060c07151401090f1d03072405 65
    0x109039284007800c00d00340030f40c02c0a55082038806d00100c0e148008a180c0101018445178440100d0702c010000c4070490f504045a47d48149052105811401603c0d03000039104e80810b104004a84c010281034004161915068540344d55200690007028100000b4070340d0b5003001e46d01c14904130003407500240e00304284059407401030700901400d40c1e0502140680800116680031002e183d0080fa40591114903100050f04e24606090700d001340111142d0303686034140c90300108895030400210000740c90b03400c81141180109490010000d01d080f140c41c008102048010ba840010000c050302016040080d4010100c0c040d22140102c03030301d08450080b024682c44041f4000565100900d0080660b0015034011324480d5854100407580c915100108022501c00600081c20701e00070480c041d000006e003030510000c0010184400c0c0d01c4200410b4541c8014145507401d03100310308a86190001c000038400c10840d05d6516802071450240155121120301c40b040307410342403925410f00240e10300708010b24101a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 828574766 1250 828573516 828573533
    0x12070503060301060f230d0c0e0f0606090a05040c0c06053c130314120612010e0d0c0c090c020d080109111e0919090c052110030f 57
    0x11a014441e60134800c2c00110b450645a2a40c1984c02034552001c1c0e80c046804201165450142100e820200c041d554401045c03074030365482c015124480c500211400c0034540c40c1c948620141c4041e1248104000c414a155140808036081b00d6055402041c0300443c0d00c4182ca095401c00f001510403030a1004012450f04e0340034039820a6200b81b01004c0d00070688842c0c0e1510320314101045281c400b0590041080d510b001c851100c400d500c40d107403c5501526540f4003900c0c50b0008404a06040d09000034043e0350700d86140c400007600c1411008004c09032001010640d82c851700c100c01020702c03840810303c03c1403007001035881c0c000d8080d0380000e100e02c142d4080000e564440082c505000565036800110300d1708440d000341d56006c042101c2d41401c0071007017003c9001c4a21071414200c5d0b004010085010781d80c030703a03c0d401c41c68084c078041202040d03442d0074551300036107070308148010070010200f00c40791082d5202581c400c0010303100c44091546c1e17078400030f4071540d2000c01e03040641414480e100d0b02d0100041c56 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 828576016 1250 828574766 828574771
    0xd090b07110a05060106080c0403120e0a12030c0602030703090c0e04120c030e090621010507110703050303010b1e03150109050f090406050424020c01110405180702010212070503 78
    0x16a40c0400050711500010340701d01d94000000e015420900040080510900455402010205500340b81960b2075490224840c5175044201c003140c0844801d101a184c50032904005000c1c032b5000b906ca00ca62994018400f004820000300100e0740440030541c3e203441380e403040d40f505510842c1002036680720320b110304065001f01d03411036034400031584402805110b0000c1c1d0025a52640703030045140c4205080040d0f04100402c601d42081e6a4880c200b000c040c441ea89000d100000c00c0009442d0608950045c0350391103032038041541d50700080003040020320000032a4110350070440050740b035800114003052103194294240343c0c205c2c8003005004804040003420710410700700340c03101c118180e0b9910901484a0a0151700c980c440e0300e820000340854610741003180e110780310304d10007509142c441080540c0c401d258001d84105a5010500700e40c95a02446106e8007629504580c0e0f04140c91700c000902000c041e00d0050001080f4480030a0226000750141c401400745004180058030300000000d20701c2c0c108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 828577266 1250 828576016 828576031
    0x39031b030f110910030c021005070c05061b090405040218010803120108060f180c09090a03030f050c0f0f040f03080904140c03130f020a0e010303080a0506060d0e030d090b 75
    0x2400c902081090800782240c0c0103c1001d0140102060540301c103034000c002c613208800560141c03030301441c040c00540c80b07106d206d090562100d40301da0703426040051500d60002c02099680c84070705c0d802c038896800318007030b110540d10441c0c1c0801d681c1c0d0355102103455a110050f901381c01e0b402da50004140c110000c00508000022641c26144582e0b88040700380d59490240d5491015201c0d5a0100703400041da55030346c810007101c040440c2e80303150b50342c404501051340407200c000c1c858022103030920406030705005460045c41d1000051123281003890540c41140716190050384580400250190103207858026a00100707610442048807070f68034285038401c0c2d480000c07171a1040b40b4210b407100241410b10401402005044643e50560360f800103043e40030030301680c007a43c0103018800740358010ba031203c54038006098241c004017078551544c40c0241c02800302234504a0744605140400c11180c413044103a4001000158000c100e06030414119070441c8514041c1c011314031300b80200101030080101409000e181c2c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 828578516 1250 828577266 828577271
    0x304030605090f010b130504030314040309090b06040320010c05030d06051813061a130f05070807050a080c190906090b04030f060e01061701090639031b030f 69
    0xd0743c0c50500c1c201c1d00d21100a0b580045002e55241d200003180c1e0149511522909001a4040064041c030300814812941100000c14449081c402c1c05414010300681480560b54107003000c0c115550103480020894848802a03001c82c1c1d5991503a00c40c0c0200b0340b10540020039207580302445440300b0f000e03101307501800340221100e07451580a00300600c80307207204c0c0d60040498030402880b83d985902421840d45040b1a0b1410b19009910550310450703281822800f81c02d00094010b1400583c80503504002d0000050010910400c000160494200c0703070069054909400155164000c1c04114010305081c100f01c040640f085844458001c403c003c251440360703c1d200c240b1655401c008496218500006200e414401c58980002e04142c0008810028540011030041d0700c580303001c0440e00d2500744200c2c007a03448801d400103001c003d1251800c541c0051220f034845851402d140c400c0710003032040b2101000d190861411031584290b110314813800000706450b040c1541c0c01e00040142c90111225004140b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 828579766 1250 828578516 828578533
    0x90a11060304110909030d020d05041e0309090c031b0c0c080c030304091104031703040c060e100e0f09070225080a1202120f0a031407230903030403060509 68
    0x500306080d00d215551050f07000207a014801c092219801010b040000c4904c07040c821224038030000d0016122803c5605000107003460300e0705204030490619400140310040d031710894804264404034400c142c8000000108460f9480101200104510300c8400c40c020040790f004407003141d0000d44546010f005100111500f501c0d24107140d01e420044044a42c164004c104c10011004650003000307050326003500c080d0500e6941d85031004165008100d862a0080000400080010080c0340e01c000c0d040a160260001d59004085141d50013000072200c07e1002228000586694200020600c10b00c0908403550900b070448000e565a0b2032844801d030081d51030120102c1d00000950114110380c006d03c014075184900341c49281600315405001d1045001d24941e00050351030080007006203010b800801c0d03a445006140080840702c200d50b101d40000b28000a1180da1035110594440c0d010b08100d40c489410708500c052440d600c9010740b501d4140c000441c00005108260b40860320500c0d11201780d900a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 828581016 1250 828579766 828579769
    0x180d1406060a0e07110a05030310060207090c0504170a020d0803070906450b070b0618010b03090a0203011a0f0a06050f0a0302280e0118050f030a0b090a11 68
    0x220b52a004120030400d9880c0080c10b0588500780b4a645110705200341c4038201e5081c0c0710542903901c21034030000800380040007004500e604201a00080c481c5400412061b00c038420020014400c3e441000c014801048140142540a106803000d0307590007441244544507618010398103400488582001c01c030700c4440080ca0300d006004428001101019101c0d50070030078034401000720410b4014480352214540d0101c45d8030002a01c85000e0315a81724050f480f280b06151607513034940001c1c0b0140c017882c0f8160000b00c030903000b8000981568000c0c4d548540f69a00c010a031840c0c2151018081d61548c01d0074500d40d21400e60945681c0c0c0e611054941403400307a00c20050101801e074500c15000001c400700058002c2d801c80c90b001c1c2074030b2260f07480c0152801960301c400030a03500040c0310b8485417482c0002d40211041d0030031190101040c0c00c1c200340d4002d03003450019034003210707407485854010b440803413504c4c03000c0c5d405010980c0380a91100354101c2d42d0070f04000031a42c4030002003044540e201005607007100c0b07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 828582266 1250 828581016 828581029
    0x9060302060409050c070b04140714090a0e030c0307031e020c130c03060e0108011b030b031f0b04060b1201050613061107051005090312090d0206180d140606 69
    0x5880d0003901c028a0207141910080081c4002007900c05002d0091001c403001500d14130805000718062400c21020740500400c690505025a20050803410400f0311800c40f80c0361401c82c145d205940c2c0c40c00250520010325524290b00c01c3c0d40d80300465010005044003016000301026201e100c41408200081030010401d82c2c1d207031003501883e0340c484101c05840d58080d010b50042c08412556150214030030381d0361455006050f0003a08282020307519001d002c44041c000314600030910060b0b14003881060b000300d021a0312034010500039000040340d08442c20581206030881054003030060400c2254680d2002400d41c0c580011502c84000c0011000009a0340b03040c009a0700482c4103085075a551919044041c1e0f0b0301649241801c03814000c900c000641555112203001403a13280c0d4032140c0c1c1d00c0e14007008050a2114070184060031510038098003285071a80d540d4084401e5068500a03030701c6044440c080c00714480c07426a20781c0049244083c000b00310040c0a01088100540121056903c0f00800c0148 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 828583516 1250 828582266 828582269
    0x1b090b03031806031819030f02160b0d020f030103060204170102120a05090f010f0204050307060804120e0d300e0312180a080c0a06020708151503190c0906 68
    0xd03968803102010070b192030101d00550300110a42840310221513042110307818000c483c203985903200b04805c2c1030b1043c150405404500450b492000e007a2011614003001b10b80c01c01400355450301c041c00300740740a81002c158112081c0800c064050754496a5a00e00603002e98400e01407003056660242e149110305205000740c0e241983e181400754000d41d200c079160700041400404680c080d00c00c0e40002d0b4414003081c4545011140c1d80000035940c1c1c0d08280c02d0524201c2030780c2c0004100300e1a01c0c00c110200303000c0c05508a60076441d280c0211b20f0301074000098140c00805030090b005d486226484101060099060038101456000e03030780c0700784494042601d100700c02521454158116a10424214005400806010311070928006a440c650000315035a40301641080d201a402003042254030301d00282200010011807008103650350601145a4541e414455406844d40088c0d000ca441840e2020000300c4a52010341119188010781c08440c01440034404281d500f00e6617100040b034003010038040c950 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 828584766 1250 828583516 828583537
    0x30301080a0303110702040c09050906012a14030a0207140f060d2d150801050705071205040e0a0b09010602070f0501050912060106050d0b04060f060f0c1b090b0303 72
    0x1589034940c0c40070f40240440e1007418042d210f0400a01005075500d00c58404080d410390790b1103c00d1810541840300005015010313a042c031a80d0200440030810f6032100103802904a8080c1d61245820700c5d01c00b01d81c0c1e44c07120a003034440c0004222401c9030740d07000903503404860b0081208015440101e00380024a0858820315412602c100034100c19400242c00c24003042000e000003105180c1c45203400d12550f140100b03244817054441d020103506841c0c0c400001c000c2c0407400000c0000d8180442c002e0898498000000c100904d04c188036041305000d0b10641e070040c42042200000c924113664804018400b030b400031442480e4800000c80d20610003c1d1039001d4400c21070b010700c112401d050040d215504080f42480c2d00568182081810042c2031210900034902901d03a26150700010491206868006046600036440c1100402c200525241b070f070350850317005080c108038031000305108440312418181d001e041722080d28241003e00f1040c0041c0e1045a807007003001c0108024150801d0344034806c05c2c0854 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 828586016 1250 828584766 828584773
    0x2d0803010302210d0c110303090d02130b0415080f070f1a04090908040305210912100501241e05091906020a170903060103060e030c0a05100e03030108 66
    0x5100605049008480c1500721100c61660083c10390f40561900c2c039400c00b40400928020030040c100040c2c009000300c10f01086000c4c50030700510f01c02251900d980d058001e0321404144d00c1c4281011540c0c1e008240440c0040d20038044140b10400c89007050440e442109464428400e2403c038250001c91010280c50034000081a00c0d8034000003806062003560030748164036800c2100049404141c8264006188111540c540ba2869400c28038101403008040e07540c200c40c246400c0141d00325003000c032041418111032040341e0745200051186020200c0c44084401441c05d1f0000c548140c41900c400405601c030315a021850b01c4130382040351402485502d9510002d404511403000c1c0c1c0c01070000e008511b001400000320181d00b980705104560030b41c0d018201580001c2c2d88802407110241c0d200300341c40346900e00607140c8040e600110341c1d50b1905100103401c2d169161052400804180110b900100c10f41c01280c0045c0380d075051081e11082e001c551052118642004000320000c040140e904944510026 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 828587266 1250 828586016 828586019
    0xa0e040c0201111902010b010f090b032d0603120c070509130b040803010905071407020f04020d0f2406090e1b0d0b13021303030c150501032d080301 65
    0x601014150091920080d9503e909401c1e00390907038030000d02800c0040d4000a21448a10038019003198011014181006411040c0940311900705e0480811240710783c2042e82d0369510864400c007880c00700e10b1a454030040c005107113409e07508441407150041d002101501e15a60030718005250310300c20f8204040c2203030000d1000b0800d900c2e0600502e0343c03120700404d1903070380e0303020542d038404c0242c100b02c1d000c680c101da0101c01408009002d1281c01e60080351801c02c2032440c00c0d03c03400c142042c044e0b030341e009202e030000111020443c1c80e02c3c1c05540000006140502181c14800307040310280c440f80803400c00403622400074242c0c51542102040031503c5641b00c03001440d0403c07014604003000209402907003007081c1c0c2e20789001e0902e41c0c0240701040c03100e4400968645203604100d0b070900d20102d005412401400605520180c004038007080304d40c1400d0109000301c242c580104100c80780c9410000103454000000248921300c0402203419054006042500074900500f41e04ea40c2101405812400103200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 828588516 1250 828587266 828587269
    0xe0a110102070f031b050306040f05010e06011a0306010915020106061706060f07030c020607030801050f18060f010e030a1a100f05120316121403221b06030914030a0e 73
    0x2090117948007950340a513041e180e60210b0716100d401c3da0125400587c0103a00740c00d0081c20300c5410520030140f8040d00595160548043c00260040141c800c000d40c00404245107030f0103424003400802902c10b044000041105000e4000c01e01031080360b02044600c107109402e507440910701485010000c3c2014100004c100c03030049540c000600403818400115503020160f65024090800c1d64413940d603d2040d507060400f40301040e800407404602442210105e800b902c88550360b80f0340c2c456010f81d0b035090f5103402200121000d00003d0030f11601401408801801d101600384841e62404c40009201260340304c140140b0300c0e003241d92203000e286a51a890500c12480e1181c90840c103440c500c01100e0a007111100c1d500c4003404096412525030029180e42d01d2400d4020149000e204461101a411850181000902184c0782c841c40b881d0134010b00000b000300300ca044030b41040c04000700d055071b449544400016000744507480c0150b50540c1514860340480000004543c1c06070342035a03642192094110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 828589766 1250 828588516 828588533
    0x6100e09030f031009020c011e0203040c050f010c0204140906060a0b03010e040c05031905120a080609090703050714151c05060f03010e0a0b07090302100f120e0a110102070f03 77
    0x44ca00074034505a100b0010f200440b0703001614038068000300004c2c80c5107800d41c1c0744039082103c100700c03400d06005104100c080340003414070341b04480302070381c2010211001e040101c031080406907009510600d054002c0b41c000f290481090320910341d61088440b1519080200300120b00315125400d1148030810043c0440b900464416400a1007000310740350032038071480003a007402d900e40407403404000300c030f4803800a200040060301124079011510524281010800800c0348100503d40c1e40200c2d000e1303000c11740000c030400c0188011354216040c0c1d054030f03882e1520042c00141d11990780d440b400c520488060303038003070800803241b0750450800d0a040944003a0750032405010000c0249901080c10600e10f0200e48080c040c1111180764080a001056510b143c5540c003400040d25480800c90b25003800d00c0182c54001d0000c1c01900982064841c0c40c0222a04844030035911194400e0b070303810300803040b50342e4400081c002c04142c40b420415012542c40301c01203a07102003511451144040340027081004c907800d035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 828591016 1250 828589766 828589771
    0x6060509032e0219030f060b0a03180c031202060f07050904050414100b01032307110a0c0e06010206150a06031d0102040b1c110304060c020f0d0206100e09030f03 71
    0x102c01e03914440303911400d9100f00d821043d8060002d01c111030a28000d15818440c4440d00036908204001003820a0230036581406511407490038580d075908c483c50b03141558085500c0081d0710500c0c4400a54403403070890a0354208900c8a0054800c50011540441f0540c641c14072809171580e8032030400400704100006018060400e0b00c189908041c0031801c0e50082c80300c0131002c4222900880c91000d80b0780010100da0304810b421000300c7c0701000001c40640c2d00c204103500030b8814501a40d1040e10880342a0501c40c84207401003014000020000d015500c8030031072442040c2c08d0302175a510766208900428a620b1846440380e00222804040c48928040d43c042c0c00c068000440341b00000c8040740e40076007240c0c81504a40e41c0b0081c08101c5241200c0c5841003a010150701c09400e2003a26121520314465000282008200645400075102e006108118920b04801c40300100c41508032114030103900d0f03210945401c42c0400c007080c00498443c0591401e14003078100800151301d8100803103000d0100e038101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 828592266 1250 828591016 828591073
    0x60e07020319200d1d010318062c06010513180201080c0d020c0c030717030a1d0607030309141f0c02070f0308040e0f0421020c030d0c02040606050903 66
    0x1058002620008200a41c000121150b00c0310081d05817001c80269144e41c1d00504d00d4101400c0000b440c0b030000240408030001ca501c804042044000300c0d4140c4450780e025105929000201ca0701d040300c1d80000903510f41215015200318005941c1c0c2c03000441601ca014040c06145044910410019441501100d03030141d000420300e0700304114004084240c0e03110340f10501c8145d0240c13035514860f00d0701340104001400d4080407100711480c902c150326220b0041c256600c082c004d265100810f00c100308005650704990090021b5950810761401a00900e0024420354010ba11f1000170014600300107441d55241c0c0b180740030f04c10030940d250b4864014144100182c402c41c0107440000401508403003034900514402c90310280c6842c1405c3c0c0c0241c0300540245100f01c098a040280008610001c0d0101050118049504400f8484030f20592816655211098042c443c541d900080d46920030b20840a0901c200e070180a89641c032031003111140504210182d158010440d040c0c0000035204905120528 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 828593516 1250 828592266 828592307
    0x30809090705160506040209070c05060c090f0a06020607120606051602030709140714030c04230a060c05070806090622051207030806100f030c03021c060e07020319 72
    0x21440700340500c0b0f40640f2021541540a14107100443c40c01c21501075100c030061400c040170340e1083e00d62a94031680908070b00c5c4124000600c03510a80c981c1e0000315502d50001d0603c455050707940384020754908003240c94000180c2c00702000001c9042c9070059501f158110760b10281848204e244010044055850499061054160000700744503140901603131400c070995500030900d880000501040307840c0618802d003101c100108403003942c0c42810b41d0243c1c0d95400700f10016249082400c01030103600761000340d10100104000420503030090f400e00d0303401c2c071520603144050364440c00c155584100b41ca001203203810290010300f04e020f21400c00c1440514400c1c00e915240740945400313041c210f00c00400762504200160741d000381754001050580010056540b4824010140d000422403001d01c0c801004264481c40f4000c1c0041c4650156031000600c3c00028004611044504008222078403c0104042069001a01c0c5600210550383c40406c050507520000c0750a0340b003100c1203c1d40482c1c2a94251 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 828594766 1250 828593516 828593527
    0x1c020c06090a02150a1706060c151e130f17041503051303021c050909162c300607110d02030f28030507090609030809090705 55
    0xa0400005004011078000303808070303109600500c680c02c0c0303039558a42074101042010b507041e664016a80900803408141e014007940700c01c000600c0d0342c824074a060415105400380000d44201001249008603a056501c80000000c0028654107000c11030f0045040600c0030803040200c0d16001e00804510302c203e00f08400c0009001412080e90132a4221010340c0c02c99044550400d070b0148213098011000c01d0200c0420050390394000e41d950003480b0101c20700c3d45415003a803090b502a00c2a41d10180c03005001c10010310f401000d106c2e40b55281041d44c00041d44120b81451160700040507065a190040000e4000c40e0103003040c02181c0c81003148a000031213041c0701c100743c1d80ac00213107054915a0107401034003e9003010f0000410060305d5101740f05142d080303440103409882e0000221107420048203003c50b280c1c503c4165402135981e005804084041ca00e820700c02045516502640c4120102e840c0d0551244e00c5071801c42d66400180002490714108111410039072401a850766845013451401300c1c6000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 828596016 1250 828594766 828594787
    0x3121005060d0501030215030c07030e01021c050c01150609140109091a090601050c0a0308040c030203030307050d050702030a0903060f1e0b120606010e09090c04020f040905060103111c02 82
    0x10b6119642c4018150b5489006104518002079248a84199480070341d0541c07d225003180043c2c07154160050038003500d500840c106900078404030108481c40c81100982c94862b0310007804030b600040e0486075551034000c191500e4141181030f50182e03500c65580740100380c2000d10000500c0109031845040c06541c0e440085c248946001d005600b03080307401c0d80a800c6042600b40402e840020f000d01e41401800d0001c05030008000410700c03589a05841c020b00c00d6141c40c100b04004503115000690035002c00400c00145a410100174400c04c0c0242a042116a03120501280c0703074040d501c10000013a45034101007010500e660001075031080c0803000040d407140c0704605c00b004200c1100441190a40b85c0302c40d6426494803001c8081c001d00b01c0405002503107041c0700006e00401440040e00d00c103440079030225040107010040d6202000000d08119551060b01210440c0c0b40c0091048845483c10080000c109c4d51082c050002843d040c861043d0401002c450540078440c0042e40961400703a0901088200d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 828597122 1106 828596016 828596029
    0x60f0f170a15050303030c2a0606060c010b0901090e150618090a0f06020d0606020307020306221a16170a09060e0f0f071703121005 58
    0x88050703569040481082c942c000c9500351001008211050b8261401007640da580080c040d00035070324148881a908140c3e8104407256003040c00441c40608007400540724070010200085400c000c0700380443c1c0289026400511007545a141201b440c034818099030b10004800317070015245240c580003280707080e811130741c403a084100410006031f1040b805200d400082c540c0042d405220503076604014010f500440c0866084038030301070b00010790600001c1180d2010b075000e800f6000e03031707a580c1c00503d0341c4001100f80710903161a003030041c20000f400c1035200c0c44001c583d401c0ea00824100140706c1801e500c0752a0050040c04002c1c0d55400c1c076403102c10182030f4810002c00b00445c0ca00e11134a004406031080000956070f80c400d454071a695110b020031400e001d10f502d5000c4454240d0740346000d8040c00f02c020060580e035041040140c0d00340031241d030203d500000c80b0204919180e0303910003040c3d0303 = true := by decide +kernel

theorem cover : BRFrame.Cov 828417266 828597122 := by
  have h0 := BRFrame.cov_init 828417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 828417266 ≤ n) (h2 : n < 828597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
