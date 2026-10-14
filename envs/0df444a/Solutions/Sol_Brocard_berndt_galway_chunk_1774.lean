-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1774
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:37:35.75398+00:00
-- url     : https://prove2.me/submissions/1e94cfe3-ddc5-4690-8353-51fa488c64ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 318884892 ≤ n < 319064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 318886142 1250 318884892 318884939
    0x6070b040f06050709170a05060c0a0c0b01290c0a06020903070807180c0f0f121410170f0c130902031504060c11150603010b041e24 58
    0x10070703840003031094840d140c03180045a8075044074508142d0503200314000b86402c40d40d00c1d4003810841001c203e011035800d03000000700d05602e55a02d280f40c8260384020008502400070f10750140001040d031034841030780409a5458144440f44500b580780d18005019600b803100140c0d02c01d03940c1d0070000c3e4403940181200e0b84001c2c1102d19240e55066454601103e58200d66440d204220b0b102c1c030999401c1c000d402c103610143c10007080c40002107400411210a1040c1141080400c148032481c070009940901070030044008860030a10f02050600200d0296105d102013140c911034088a8601e1f02048080940d144400500f48080c0032504020004c25100400ba103104d5490b2040300040e5020815000d070000e046401a40520f810308100c2e040741c010181c1c50080c0306001c25450080c0034045003050100d024041000004d88a00c008a030041841e0000f190708545090044800c5196030302c0100318440269034244544030003c0d284407103043d0310801c0343d03281048c0c43c0003d100081202a80401d07411951 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 318887392 1250 318886142 318886163
    0x210050c07060c0213050f1b0d0606050304031d0d03210207142109040f0f0c020c0301060b2511040f050f070801063c0201020a0906030b06070b04 64
    0x11600507080c800d0551040300815012101c082c1141040a4148030411000004000038a0030f01c0069046000041400c24400305002c6001d400c105000252127604a960300d04000702d03505d40c080a41190f01c00c0c0c03000e4021508404088044030340706140c0c0a030414015012108800030790b9815644503c4034071100d4080f0040e2070310088a5180c2c0d1010b045240d01a5940030840c4034011000e50400040c00d00c6d1500394001403a040c0c14032500e40f411035070058002d0301c00003652a8044907041c000c04142060b1024682003426103141560f000544c400684001c500801600b9926000902c082c812001e12020700701c0074201c01d080e40700220802c0a038a07801000c0000c220300380318001400700c5104003001100c1542c0c075010b009540c89030f8180107a0181142c20401c11030750400c0806420540b142400d04a240810490488122500d1400040c50204c00d0f807803c0d603043c08414083d0103034000680c54000030307498900004503144030b8022000502c40c050005403500747d29480c2d2040d6001300400030707128406007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 318888642 1250 318887392 318887407
    0x1104020f090d030e01180608040311150906010906090e070603020a050c0607080412030207150b010908070b0408010e2b0302070807121b080d1a0d050601050901090e0a021005 76
    0xb80c0c01d202c1c018600c2561807600c0c3c4a04000003616107840707078035041c485021184003401000e802510458002d03800d801c1c031000004903c0813480c03804101500d102454071110090049550000603200d060300c020351410300808d42c80d80110700c12103c1a502c080016400050200202e44c066801086890120f14102d45458440507400b4501002582c19000140c0f025003084103005c2c4004445a014491f03290035031400c03980d0307103411900910002c61200c00d15654400d41c413081e80108840b030014034459042e1422155501c1c2020003581040c4115480c5508000600034402c00106040c100400c40c2ea026100105000750601945800d5403174400a2541c200000c2c004a030001c006094074511622011089610000001704000002030b0619840a91400c4450016521400340c50100300050000100d504a040030021a079580c40800c503040007180c00f01506000c40410308a041c1c80d800d5501130034613681c451038902254004219912207400c40d6100200502d0240300190a84000303150840c1410345 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 318889892 1250 318888642 318888649
    0x3140106030c081b04092f040f151a0d050426091f1706061b061b03010f0603020a02010603020a0f03030311030f011502010f09030306031e1104020f09 66
    0x7980e41050401360321100c2c048a03030301111101203200310001d80301403104e00c07843d0b5151705116a80101c0044000800b102901c00507000305030f600c0311840010024000c4903901d280300b0340100104440c480b40c030b2031280c6020510081341180020030702c52104e81d091500b42c42c43d040000812000d402150602c10000ca1484103000941500c4850341401c08141d580c1e501c44020007002594088000342d408507403400c04c41c00d2035000039513000030b9200e081c0c0035070b001d07a20000054024852015500c02d08501495442488003001500078851448402d4000800480100800b4140000d1040d410082030303000040c001d0758420b401526900708140004502951603a000403200e00040e080520000750500040040c1036050082c2c40c041c29052900900e0350401104025003800c0c140a000d001c200a542000c142c00d01c02d601071400a500f00004006803225460b0003800b6008900c000d542c40c2d140c51441c80c05007403c4041414041c1da2021040c1401c1040a0601010703411005407030302e82140a00640c4003030b84 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 318891142 1250 318889892 318889913
    0x6030c0506092202070f0b07180807050d150f09021002010e06060103020c1c02010e0c0a0b09010807020a080705070509090f0c011d0925050c03030112230106050909030c070314010603 80
    0x1f03200e1a018a503502e484031000f030501c000f07500540c2101c8441d10007080183c03004941c401c117641c42a505028040074a00300310001110f11f54142d446903140c1216030340003407410703404051254421500b00c07200740880709040b401c1e03881d01d184004050b00401c0c0420481c0d80641d0050070030440d25070035988440a03803040652450354038030011000d030f5160804443e080358140300b0407058040c100c5680e46400c0c1444850001400b070205603a042c40142030225010600801108240c01d5100a240380da4448529040340c071481c061041d2405201e0722004030b8410880070031503000010030b0704002c15900c0340e114011501c00f0091f00804c0501c240f002e10071412600e401602074410140d00b40b0220025025010801020181d0b90030b02081181c2400795007040d01c030101c2101d0440c1c1c0343c6014004040654185988805a140007200c490b008138a901c1100c100c06400600413070b0400c07150f1f1b90166071a2280700340c1364450707085c2c1010103403c0240c0c1480001c251207050b004007802d840c00020b0780360301e9075904461103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 318892392 1250 318891142 318891173
    0x73807020606010e0d0b130201020c01030e060c0d06080a03020d02013207110312060901150207061d101701050108090a0f1106030702211314030c06040906030c050609220207 76
    0x344c1c0c51f02e040340541d43c04102842415000386820041604001e44c0f450311107002615502003c9400a1201d03104060b642258000e031034020141d900200c19480c1c069511912510782c1c001550030304070450301c3e90300d801c03c8003580c44002984030b840d5007159030707105803640c8402019002031181500000381481410000b82c2041e01d040940e580060522108125000505074040c6050508200c080c0781d690350702042000c11500c4605000c00314a004c0390003030000c425458002600034901000640e5482c1c0d12851508403000c12111400490362210f0045030a603008a840c0c0c0345c194060101c0c580002e000c83c8407120b11501a1079124407240900d40000c000b03a0041d079203500181c4c011825441c400c6109400303280e00d4110100400d203003801e0b81030144041c0c101803041d440d044412250343d04103518140060016500300402e80b80d51203466004040050140340001c4d940e19003603160114840c200380080b1107102c00c000301804031013100b03c10845420395540241d0b13440b003502030240200055003c00360f030030301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 318893642 1250 318892392 318892411
    0x91810060f0306231512010605030d110c061611040c1b0303060b070501091a0702070e0712050f0114010c0b0606071406010f090c05030403091a073807020606010e0d0b 73
    0x60340044170030852040a200c0c0043ca0b56403400a04205582c0c0028158407500c4041c2000007800c04500081c0b403c1071a42d1901e203070480b8000943c2c1303e50360207070052030012501c2076290141002404050004848c15044a88003003103001c00c3c1e9a1750411259410201c4510134600841d01c1d5484004502442e040b09400f01e0305a91641c490700d041241400440020081d414100820380c0740c00c3d08002d640300d01038814490700501c0d500c00300e07d050b0712842a01d005092542c0e024012414140e0000c0380d4183c0c00d00c25004c0e0040000c40d517100640c13096500da04c7c41500301c0101c41d500e48400c001c00065612000741190030b6890607050520306507081c80303610b008107020162114841e01d001600c4041d15400101003041000400802000035002401e040c140d482c907003d4a50080b03408600c102040c0f0811602900018601510440740c1d1581e1880e005600d583c0c00900168800c035001c0003202c044240d0703100c409030300580d0015185511030603100880b400300a03c0b240c2c144031161540f168181050320405035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 318894892 1250 318893642 318893671
    0x20c0f070b07050f0a03080a020325020607080105010c1a0601020304080a03050c0c0405040203060a27060902030f0114070806010311030132010903030c050a02091810060f030623 78
    0xf401401d002e040414101c0401404c2c070700c03460343c0d8010003281004051588803903000c80800c0c045031500402503104031010618028240c13503020060b603100310486080d00040e100b40001720303a0794800e0075840801350b48821900d80a1030500e00b01c440a18008040078110b20062100086d58a010425200000e020b40c039107941e80c840004100303080a9082840728080d0b07040a05000c01a180024880d600c03001d048030018842c8140540044854038500d5200755040d9441c4500b41842290361152218078400c42c1280c040804800210f4242d4a502d0305161442039008001000c4601a00b001d50344201d0500d030008403950080650380154200303030401f10540c14481d50725003840700580b0300c0b1080e03425442d140d1420007089400082603100c81e03000003000c100d0700651b541c0c10044104209144d45500038400d461510380100142132590b20720365880d050388501341d42405580c001d44664010b48415507403c80c030160458a9040140401403000c990f043c2e803100360281c2e04409013000e81e005a05401c41002c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 318896142 1250 318894892 318894907
    0x60a21050114010e01080606030c0d110f1201021213050c1005070602030c1b010b061608070b01062312070c02120d03050603070e0c09040b1504090c030c021906020c0f070b 75
    0x24a00381c4001d00590080d8020000100d080cbd07100d900200c000b076440341004041683c00e00219446c80c841c02e20481d040008a0b207200c42000b03043d0050704240c464000190740690358101c10030100254903c0142042c0c1180901441d5410540e55146401c191414074510780f0300d2940c0e480d0121b070b0040310f082d506408041408002c1400510314400c0c0406100300922000321104002034051144a12080890b8480301c00e2030200304c02e00d4180c81505410160105256a503480d01400c0f43e031200004c4850042c014400c940203280c610251082004611210301081c2c2d10742105850f02a143c0308160f078030407490003030125810802c10860000b44900e59020420741000c60074186095060303001000c646540104000e803400424003170782c142c601c1c112000f1840e8030250f17020680700002141d114240300b90001d00030034a0140c0b0b420410200801c0c0c0d80400c01c156401d0401c03078961440f0000c2c0c402503401440418003258107074000c0c100c1c04c072211060700c50391424440401d151004562017120300400c04500b05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 318897392 1250 318896142 318896159
    0x403020c10050a14090d081b1203010f030201120f020c011409070b03061003020708040605130b0a0e0d0302070504090b0103060c02010c20190b0a05060a21050114010e01 74
    0x5000c0c2400508049061000f400720240000e00e402040b070004103804907042c4101d9440c110340e580659040080c880c0e86418644499018544620024202d442034040d00e4035212031482c2224100e404800c6201400d50a56004450101d125441d000c11951074054100d0100c82d184000c005d40b00d40c5000008114080764045042810700405690316900283c0301040200c04034005c6a500940486d9800d0521800c2035003038000340107000001d801c00c40d0119003c02d0603504400140303000d00c00c1c001c07441c04c290b0343d48840d100103100300300780000003880c171854445040c1003648580c040e061282c0140c81c44107880b800410f04940e4443c01c1a19890201d4004000344079a40c8510140c0d24010300c0240020301990300d0180612140d1810034241c8081e007554080b0350f05040c0101044a0300f90020280c60400d00c0c20003246c1e9110665041c0e0280d80341c00084bc3c424640b4400075400c4485034040c0d00c55000b16800c148043c003d0003038040d20b00e0f54a800480c2c492514110106002e044204400a460f50503c20391 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 318898642 1250 318897392 318897409
    0x3010c02190303090218091b04150e0a0627050a020a0e011b051c11010905190618061506030e060a020319110c0d02011a04020a14030403020c 62
    0x4010554200c1c210404168605009241100790142000308802c41d01c1e2000c00c1c18200c2103002c20500c01c400c4000d0208941c401700d910106181c00e1076001c41c4003140fa0f0304000c120303803442c2c0c1e4401010000300c02c10003214030041401c41d0f00440d82c1c81d000501994408928900c1ca00940080080200401c08a4190708a902c00c86810000c24081103050821504000c2e0804901c0c1d0001c41c18021841041000800803807444011581d00000b50b030f04503007012600240c40117041030703000042030f040f40e07070200280d00502c600c00319181c008004001901e01100d0000306103080c0c030340540340640c445c000c00e603034946001546043d0302e200e0704000809604140743c1440a600a0300810100350620403401551100041e6048d00134000320401a0740352034034010842140c60540050001504100542803903103805806070000b42d40711000d80e070110203000c0c2c0487c200c8140c400301c02e903000c43e50a00c004940c20103a01400100c04207092501c1a103a21000700000ca42084074102c0040c1d10004d40101c0c40c3c10304501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 318899892 1250 318898642 318898661
    0x5010519051017101401060807020307031707051b0c0109050a080304060513091a0a060509030715031401180c050a0203070b0603070506161e12030e0c090c07020301 72
    0xc20890a210310306502d10082841035010344844a0610f001c602c400b440400e102444000003000038001c4a5910304151409204a0002c1040070000130003540c000700c11100007030381c0f41c0d845601072002d00e000c42c40c1e03840c80070304154100311007030107030b14503c05400d0718400c0c56000d420001c10507009104d000400101c5684c1205000c0c5402010410500d0000016102650b5103400e1841c1c9804e50224910032004d81c541c400f50038103040900520200b01078603042e070301404081d030302181501d8450400391402d2040031421601503000301010800759426082c141e1036501c080c0340c0030038911364001c0d8004080700283c010603000e018004280d248241c0768401d001044120b810b0450400541181c065160302a101c0083d2400800320005401e0340c1e82071121002600000300141e80300e4012240b00d4901d940c40c01c0048940d0004501c4035124042480e0041c480e2310b034004020401058441c3e4210060070440409151511464000c4020b5a80740c8070814490f4850000d00350f10340c0748034010142510140c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 318901142 1250 318899892 318899941
    0x1020703030e0f0a02010c060c0c0602030a05060405060406060c030509030304093801170604091203090303060e010f05060d0b06070602070201170c030c0705100507050703090605040806040b06120a050105 89
    0x813140320050f608000084810364014900082140202c2c0c400c0e0342410141e940100020f02c008108546004103900180c01240240d0b01001103a640c4014842111110f011348400b140c00081c525000a01c02d5000300301305071000d420f9a00b41647d0303020240980340520380a1010300c0c80d0040a4a0400487d8160304410707140080c3c1d200f01c14440d07000039020b0380d0701340c452041c51511140099056141d0b5001500226400501d046480301626030040c0149030b104001c6002900b003036030000701d2041404419040c2c07245003803648001d9140038104426544140707400003d050300d0729160442c5981e0180648001400703030b00301580d552000d1000601000c1d000c000c9541060305c003803d1003040b1404038240c9501c80e189014007070b55031146003042d134070301409003102000c100d091100304141242d01101a2140031320030746a049419440d100142c03018080c501500c1d40d0740e800440010301164034100030542103180a4202d40b4001c44016507903080480d81107041d50241e44030414825240c0954000301c0410003140c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 318902392 1250 318901142 318901153
    0xf010203011a090301180302010c2015070c0b010609052805041a0307091a0a08030909130b0906180f030702242b020705032a01020703030e0f 62
    0x7102039030b010a041000c01100c00416a0400c0351030950016100e050540c0307644400850a140c001d0107402e041d01e00e01d0000d0320181003d01a101c050032b41d054050a00b8026000012516420341c40c020320050114040020160401c0c0100f00f892907420701070030b65903031840312540c2003005104214440540409551105003540310780b518450a2a2058540c2102d02107903030400c2100c10700a01e00495180e41d07050040d0000051052001d030302402d00f41410070312000c211007820301080329039425886055481c1d0820005410030380b03850352425903c000001d1040c0302400454441290b0454125041c080b170b0b62100091001c002c3c0794110b00c1400308d030600002c09020503105581c603224091031000a00032400c81034907070300d40000c0382140c050303c1001685081d16004e80700e03602c010a01c0e0403122214050380740104001c1d94202c1d070007110280c0d50402d000b946061a90709450075041c41400303808001580c91442c51850340002e00050016502075507011800080120056041510b0406180c4450b07115 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 318903642 1250 318902392 318902399
    0x504060c120203040f121401110301140312036303131e030b06060a09031410110c0607050307050c0d030f20030105041a040204030f03020f01020301 65
    0x44040350029920081c054621076005074168950301494001640b43c0b03c11000224400c07007410301c04850035010b44030a011106100d40d58900b01c0f404440380f852051400c01c0148010403a0800160410070041e08449211003a90000e000c240c0081c0c3d000075005d03c2c074001c02900001884c1d100a04a076951220b003201c0e606400005020b450030149200f5032128030321501c0c0c41c6203d0081d40580074100902601d96640c0b0441d0780c0c44803950300f401820702910a111a11034002100880602901c0e4020102da2840d10b031681081016040065000308000c0b11a1010000a040a40300701c10185400700902c1c1e40e18003c0b920405803000c0306420480c0440611807c0d0341028002840c1d81c03c003c880c113155940b41c9442804035101d21a0f245001001c3c8940846515010350607401010310184a803c20400105d4009041d50807000200d07481c030f84581c1c148014082403900740e102000300c051420310900c180c00c07000e000c40c0903a000f5600c03d07100610755621200c140340d01032014003d03034000c200c001c5103103604 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 318904892 1250 318903642 318903647
    0xa060608072601080607020609070509040f020d05071712090f0f0d0f0b07030501090516050a090914090f151f03060e010b010f090e0615190804030f050406 68
    0x4141c2420054003110000401c01c00341550b0040c1030040e0a01c101a686881c649075561000350344203401440b581001544010307012800c08150352000341802e45035142d81d1034452480d0100d07113069030300010007180540002c0c0c0400c141c0d4014038040c0c154490400c40014564207101103d46401c0c000342c0c2c10441202155114044078042e06801c0b11041c2d010104440401c0e9040000140240b10b03c01504069052210344000144155442d54051000d0781c1c03640e00d5201038840554400784110404003260341038a0090001e02226941464450126aa181e010506440181d0b40341d81c0445c4070f030403d001d4000c030103002c5940400d503420b0003030500c4076000314681d40c591001810800700416200400c0d60480a47d03406034000c0d5000341d01802050480d00219008054075500e040c08640c403d800c11100a000e0307000c0c50203c8007040120101e0743d8036202407160700030250850804401c070801100c00c0100300c910600441c0002c81d5241255840d107890054000c070034845202d014800c040c00208800c0c1d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 318906142 1250 318904892 318904907
    0xd020304181404030e0a0f1203080c091c0c120b0c071a0c0903210f03090102070c06021b01140304020d1506080c1503010305030a0516060c080f0a0606 66
    0x109600315250720715507101420340c01464400040c482c075908850038002416806203240021310303012103801c0e401d1542c03810b024111924038404c8222148002280303002007401542210341c000a001c2d601494216460000b4000414281c0c000c2140300000f0b40701c105220319094020054616040d07203c0d00b03901c281d1508401c031980140440502000040e080d010040d08401004c640c0588070348035038050800b40310f08809078200303c0b0300c03e0007882040551000d40c2c0e03d10040151500a556860345008651f1581100c50352005200e10a199002c011110000d100662030300e00503d0158007a00c1034811040c01c081603c039150540a041024030b8942c8200c50410341c1c110b94126904451040010315140b420b100d01403811482c001201d440d0050000301800c011403040501c45049070001e00105422074506061300003800b02814940c41480b02d2030103540540014142c1c6040c01c00622500d0040d55a084181d4140e0202040061803880600030f10600d0070507401e13084034540724103022a03800c03d00001c3c80e14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 318907392 1250 318906142 318906149
    0x32a0c0714010206131707150c0201051b070204090f0f03080721020d0b0a0e07090504022104150504031e1b0303051008100902031c2102190908070501020d020304 71
    0x640d405c050381000501d070f6a4041d0070035801500d9880300801d0034291130140105001240c0f0317a0400c00500c0340d2a206100d1244500710340307801d140101c81c10003007144664100b13010072038003d03548600e0003010500c81c001a00c4600d114140f0611038800924004054007400f03401c2100b4001d07085401c003820303160010a5413508100c00c0c00141c45800072200000a40043c1c030002d0381080f5000d201280129400e2000c521491207615415203040d41c0d01c0600040340310f86142120402d403030b481c0840740180c001c1c042e1600729014166401c10b0340840c0c030302031003190400d43d0201c011400110381c203401e400d414808881035542d24145010141d241c20440c01802c001054000c040542e5079002480e030410700e204010240104004071600440c81851520080c90a040c0580c4640300b014282c080b1000c40710b41a0000c4402582d8182c1e000f0410758103111903040c240b5140500c1e42d024000440c80c2e0745079401d000b02103551a541d001001d4508440207050044c1c1d500942d0440d0021140c0c1d4090503000003c56044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 318908642 1250 318907392 318907411
    0xd0e0a1b030c090915091407080c06030c030a060e0f09070e010501020607080c1e1206090613020a0c140d080f011a030907030209130c05040c090b032a0c0714010206 72
    0x700a545856180c5c2c031102c529203c0d54501d00038120082c000342c190100000003550b03044650507603c1e103036803659580c401441160302601c200f00141c3c02c00324080c041e640024032040b021415075201c402d0109406011500391602c10807580800400c0d0400304a050000c04049000c01c0595042c140002d4403200024002010320603086c02048540d04800c007120900c18800c20160107103040504d0100560340409140d264010055020a00900c0c2c1038003050b0280900800076071621440d2403005002e900100504010b0112102651003c40c0701c402c5000011080b10010380058200104003601c03a8001600480410302d0201c018030882c80d401c40301c4240040e200c008a0303141ea1b94602218030340003060700001d410a0100081c404410703040503103444810320072082e040806454800348811601d0600021002842c204010880681c0403001160003203618608a41e003c1c81007042101031021901c8581d03c5040e001603c10784600c01802068041c0c400104c014144805000000703541e4180988403004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 318909892 1250 318908642 318908651
    0x30501060c0f0c030506160306141f02010618050402030105071e11250608011d0105090a020c0a11121603110111070905180102070512030c0d0e0a1b030c09 68
    0x1807100f00f25001000b99440400c4480c1490441000c4041108000f80c01011a04000700407030309000c1f0f100071034020300000d40210107580f80001112036840c045107001c81555030303400c0301140b50301c1080000042e4003031040c1301091505240c81031508682c1c000b8811010050a88071100d1112402000c3d0440b44107a4034000c40040600072449007088215405020480c0900c042401c04241800e00c0d5001c8540c282c84410007aa078803143d0344004003403000440708940b1414014001490725440c0070b42c01444a003001070504492142c2c0910b0240400d0f0107582103020342103103080c1483c19040c00c2c0c200c3c0c000701c1c0140c800b10984030480b41c4c1c11169800f004100c051090005210f03644580212034150050808070760609075200b12220007807006440004142d5401060b040009405000711401264070100038640c22100c000c0000c40c540000c2d00800f20071608001000f01303580b150041c1c1d07a80509101c05006140344a1400c00c100c0b01d1007c1809441ca5140e400c104040784082e00d540303048903c005c00108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 318911142 1250 318909892 318909923
    0x20109050423130203190c0b030c0d180605060f0609090601050c0616080a05040b0a0b0a08070e0f01080109080a080406020910020a1a0c040303030b0d0c030819030501060c 75
    0xc207a14200000100700040034100640f0042035007422941e03074000d600b07aa804048201c032410084034201000340200240301010000d07035102d10001c50303100e001d4100c0300e401d1a100c0d000c8a003c0d280c0c007400203a0300203c039803a60000c7c06613500c60744d07070820022180c0312948511030f40450f00c1402001c2e4154450140240055006c0c0d02480450751468000019100700303240016004da10401c401d5040030019901c800000c0074495a4800c050090390466401490347d5100412200036225603a0b0260700401c070390800084129040180c54060400098000039a1074241030f501c002e4041644042602d1f8100000c0c0008101040300700ca480e08003516000b5660780d038908243c0003070b20910b0200c98100016400c1a0700481d40410b0110f1480c1c400c1e0f48000c20300743c520f81203080050040c0d40300c0e5440b60007003000300000381c0203070b00c1024407210282004602d1040d0380c444040d42c200aa0064502d02c60024240e000c060640d9001c520840140c1000c000a506003d401400041c01e1240100b07000850030500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 318912392 1250 318911142 318911171
    0x41209080a060203060f040914060a0207020d02120a0c061d0d03080103081b031306081e0c07050f030d05061906051218100f0e0a0b06240f09010e06070201090504 71
    0x16000e406d0080c0090018250620b0000500c07021800d1103c01809080302003280501103000b22030101d900240180c1080f141602081602000c00e50704616034464206030070005501c00380414028001521841092501000842c40010303441103484d1094160402090010b81c0140d080c90560b03800203107054444102c40450241d00061480b118558800880c02c800c2800e00b0b8a80c0744180c03145035172182030680750409113841e0003514465440181d107000f00003400740c0c6445e0700585250703805142200d01c2110310300f00403030541d401418021001070b1610700300041c0d403c11490342e002c00405da0810b82071701850120020400d000300024140908200d00100304400900b1143e01c3c450928102520703a801111064040140301e0f000410701c410b4103004640312010308c0030461410003500301c0464401da035907000812042c0d00d02c1c82e5005000000c0440500ba1055218000e000c000d8925003030f250b51509a040003410401102e82c0d114400d0408024100040c0d920403802821628151804659200712135100e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 318913642 1250 318912392 318912409
    0x50a1d060a050c0d020d0c03062412151d060d0503030105010f09030b340c1b08070f06022b030903030f0213140f0108040b09010b18041209080a06020306 67
    0x40706819800800c0c5402c4502c46c81d03101503900001c41e113041101d6584c5402074911070300000c0048900e0640031444203206801252000d0401c0c565860010312240098801030045000b5007288100020410740520b41d400000c60041d001034080303821407c00c1c00345941705940c81c0f0050181c1c5040202d000c48405110703014140c1d84002c0d40d440060100d80b40383c80c0e40b0104581840b40d061013510500c5840012960410300014845074100343d513400c5004260352940310a601c0d10b407400801008030307440005500780b000d001480c050070108040034840c034a405002450a4607000b00828840383c089000344901e514410b8003003034a81982400300b164580c0381801d45c002c0034410304502c0340c2d500000315260850b80ca80c02e80401e454180c1802802c1e24030103000d01c40390600c850480c0b4081601500480c02041d005510341d45d000c04500300116458185a010541548912002034a0321004038240b00c1000100c62400c9600c6100d4584901301c0c51400c8a42c0343d540108000c00f4107c0c41d8000f020441d1510b45244 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 318914892 1250 318913642 318913657
    0x41e0510060c051b032b080123060310052e0302090a05090405150c0403050f010c020307031808011803030c020a030e0103111b07060909050c07290a050a1d060a050c 72
    0x1080d020b040c48000c61b1424541180144030010319140008a8003002456003010140c241030701c50300c210070550050105a81c0050034418010005180010f00d40c1c0c3c030354244d8000d8016529074405506d41402400d0b041c032800c2100b200a143c018000840700e51500707180b54044503821100d90031140c9442c1002400c0055401c00c40700c1c034030798907020450086020401081168894021184202c3e40401c4244c202c44c4865020401030300200a2480440d209101c0158021401600c1e403d425039266035103400c542c64000c00095002d80c2042c40ca09058040c410042c0b000c2d038a0015051b00e40203603500500b48034207a01910b0626070707502000303c3c84a0040090300c624a548030101e555130a00c0a80140c1c0da418144a8540098210000815070350461300030f00b8002c05005540606044060387c442400660400d0781003400d802d102c651034005079150b0300c901d0080301c402400050768200040704000f51600e000440c041100c9018460416103c0050f01d04d0748001518000103480e280c85001481a105002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 318916142 1250 318914892 318914923
    0x8031f03140c090405060109020703050408100b040e03030603070302040f06030618020a060504081b152101120206160303140a06080c040905030a0e041e0510060c051b03 74
    0x1004030400c070041e60041d0003410080112116188090200b00c1c802c0412100100a901309100400c8400000d030058071410740700b030404904294440900d03a02d480c100d002c60801054440c0820800c50400b4032903051341c041c400c0065450342c45d1540c0825501c0c0da161000034001c55803401400401c0c2c02030751100010710307800391041c06041c5010602e600b0b0300181036800d901c620807480000a005018104882c2101c9038440682070485064210760785415541c5402604012100003032256401402c000b0042c40d0740106150302d504107402154404000f05801180801e08030301c0d2550056036032035055610b1158012242d812031015071400324040d144540c1c0e1580001c00c528140a21250107401200aa600c100211050300303000c0310800c030644030300b90350140c550380041160509580c03190305030280c2400701500220b601c27855046840c5801161800380c4e014650f494048c031aa143c82079911380000d20722031038500e4000281c4d441d05501c486c20100f0380f0800d00d4000c04050250b807000c0c08180006040071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 318917392 1250 318916142 318916201
    0x60406150804151e0c05040806070e18010605071a07050f030c04030b0108060f0601020a23120a0903061107081909090c030f0e0f07061209020301090c06021006120803 73
    0x101e4901c082a0005428048132070404000207103080c03090b070940d01202d031400e00820031900d61075070a4a840301c0020000383c2000c1003540c505040c02019a010380204519034070701d030740d461807810003c1c80d210440480f45411f402d0701003802402544441070740c0c40100701d219100d0b940d031a54288001e407403042d03a100400c022801000050b008201007a0a44140607902d4414101c0e032700c1d440126101d015960380101281194404039460910b0001030310300d20942001201d01c4110104164000341e00031803440000518600020b104128842c069125007001038810f1038140303403a43ea1b45464130302034803600c64010303006128031200c1c50340320302c940300010a0900c208006035078044038010064203c15412800044c24280510441e01000414001c01480c12000e40ba4050030b189003143c140304551050301401c0d442e82841030140c1e90030710401c10030904c0f901c0c1c4a0200b910b00500641001e989101014816103080c0c4200804e2f0b0341000301d43c08503603014800da0b41e40d84d90181c04070240d0508800d150801030381d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 318918642 1250 318917392 318917411
    0x1503020408011b18050d0b1515090a080f070302040902060403060207030320030720120f03010f0806010b09010804171c0509010209130b03030f120f06040615080415 72
    0x100f0390086403005585106030707400c9900020406070924403a260f0819845500f02020904c02c0d480c4035004a801040c1943c0c1c9907212000440088021211426117080090742002c145003010b0f0400080c243c02d0050301a540b10b0514080d221209480007a00581d1921050001c541d62001100c001e1648288215103030b40321130800500400c10442040c48000c0b200c080c24003262225010759205502e10790340c0400b0401c2c071004030780b000e50000c030808440740304440200001002003800f4054030b80c5101c000c25100e601d8013410018441c490341c80044150400c000501c031075685001100c000000a00b4952441c1c2c0700c5140120700a00c2d50401034124481c08206480f22500c02c00b01044041030501e010300040d118002c48500701d1166002c0d03540e0000d003000c0c10150001c40c90300990719282c0d00034180d0f42010441a910b60781d65201c1a0320101800c101c40070849100e4200119541100090b00c080020508228500c102d240e800129101444403080000d0f0800c00160070214013040300035070901c01040e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 318919892 1250 318918642 318918671
    0x1e0c0928020a14040320030304050d0b04020f0a0b030703020a0210060803090102060c2506020d020a0c120509010f0302031803040b090a0905090604080313021801030b100807150302040801 82
    0x24030b00320001403030548000c801d0300d0b1000240e9099a4108007003e04201490043c2c504100210001c19054001440005429500c910072030300140c0c041c0b400540d0303a203020710400c6070000740707a00c01c1440742c0304050003072258007099810b4039449415400d0050355102d00010691900f860010302c2c02040d4204940410030520200c05032100b542c0a8080354500d441d03511681407580288601c2d1003141040c2c20000c80c0400c8150a40516503011f200c0041c9854415507a84003642d01c02101c28012409a00c1c0140c10007170290381080c848011441c0003410140104002040031242c0d441100070150044042454132581c06200e85481014030704581c2c1d600e0359000c10441c07e0b045038901d648140403000c800280e401590107402d01c00d5905130013030409541c0e60b58031544940c0011b080c01d825440244000c0c2c0040c0c0700d02c40040e030030a0510b130860300c29614501e06000701d00307070040021000800001c0100400307140064a1001d03914017140c0040e03061a9040300720000e01030b60f40003419139820b0900b4008000d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 318921142 1250 318919892 318919897
    0x130b04110d0509010c1e03020c0607030605030f01020c120304030e030601030606080c010810090c05130305160501030c021b010c061505040b010518090c0d090b06031e0c092802 77
    0x408440042c445503403000c1c1075a0803140350390300d60400301e00c0304011410013109000b00408032900e1418014145080255083d240c910100d44403000b00e80c1d100740500032171800f0080c2820003030084000390f140400c52100c00b80c640840c1814504c1018011001c00c2c10107020b40844040f07014040c04a4101d5a500d00f820300c05032503588500c4205004018104a40e54400d00c8882d04c2480520030039081c5a00e0641c0d40c1d0002c1501420240c108801805101c1c0100040c4907050300841c014170040044c0c00e2b960038644044086544001c1c141480c100c1c9541c0382c03039004035461141004980850340700c100b441c00103940341203040c24018480c43c03600c4000ba42041c41c0c8222001505c5e41640d04015408440d00155a58420050f071894002d6140201c54901d24010040313a034410004203a5a0410142602c907005650501e40c0440383c0c40c40100401c0b01030b040403c01034803e02e10b00021032705c0f10480c22190548a0141d40450340c00745e101d49000502c415564a80c1c1c00c01c40d801d078185d044000c0d4049a001e402034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 318922392 1250 318921142 318921157
    0xc12030206060f04060509010e040c0f030809010801061728020a0302070c050f15031b07060509011a0609060c010209090709170714100215160806060309030306130b0411 74
    0x2150b43c140704102a0030103200318401e450b0098075801090342000301c41401c11000501c01ca8030a10510000700d503109000d8010001035204a0040d034032031001c0c400251a0500503044a402c0054058840000c100c00003503880d0403111000c0480c8001c000e00d4280301d4520115004030010b640002100c03999a541f6a0003060340c64040d10100740c0c990348440801106106014001d680950f028944550006001008580141484010b01c50184603800048060f4010302c20076034041d95a0401c02000103c2801000001c1d060b042414402c8107040001076030f54082e806080e0701500000c10900310b0f44509604070342400f4401000b14507245010800105407641d03e0150007800c0e17200840390380c3d9510000070880292900c00c1d1106062082c10b03000d1040c01220703a00e4500441c40744018030354581d00d80d5416280513901150a81e40703c0e144a21380500b141c81d02800e940d0050b401001000600f207004004e0360b42100c2d0840300140c4621000b06140c0c082c00802e204154003500e01580b00c0900c01580b0001d0181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 318923642 1250 318922392 318922399
    0x1207060e04110309062202030703060606110a1e05010609060f0f12080406210608071a0403050304061b0b1005041a01020d11010905010501090506013203040c1203020606 74
    0x1004045652602c240001d44e0804080c2d032040001c10600100c0081c0c1141c07061240041d4000c1c805030750000b910b007010b1540190707036440d901c00060015517404000b080d4510040e038001d180502c06640c0d0800007242100c0794402c0303001403121000802400390013031030060404100500416850710414442000e80d4031410280c0341c1401070001e2000422080c1000d482e07000b901e894203080c80c1140540e08551807040d50501c4402e0b03c0d1404c07404001c10700c034000107000810001d00a45041c00701712500308662072040d8041e8030090100f003000a20020885055660500d403c2041c1c4104403504401c030381820400600160ac400c0800403021921140041101d1040360180034210410f200d0541050884040301e0058110030902c002c03650144240740d2801c1d0741c203400010021300b5a240e1a0854200f070b00405081c0e51a50203110643d0f0307202e29803d03031340d51342d2048903200c940a0030150316078445c46030b041048084001c00001c1c140038603058004001e00d551903441008512500c0d0085d01ca10045409622 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 318924892 1250 318923642 318923651
    0xa02090909100c0212071104020910080a204503100506030a06090213020a020f0c011707030b0604031e0605010b0901020a060506040e0a0308070306060e0d020402091207060e04 77
    0x1001e41c030028682c69505c0000741740e289403004075114030390349055400303105400603000c0000000689401c266880409080ea0300c07410907003442074180080d90010030748100f960b40800300e000200d04041086580c201c2030614103031080d00e40315102d40743d0200316075200a42c1c522010200003681400700010b000800086040c7d5890600c04000b1000725201a03540300d4240e4488038000740081d00a034031803000c40340002c0c02c81015040c68034465090740e116441c071100582000c0100078500308100a40f80501d1003d084c50354032200e07051b2244500c8500205168201501d0708052a101d0700c50300e0444001c0e641202c41c80107070424054844200441440b001c0f00d01d280340100004200410794152070326031205074041c14002e06d458407180060b040140c02181e0059660f8007000e8004020010809c3da207119032103403000ca2a145401800f12101540070f501480100c11868499a8500048079035485d41181c00684900035800450b2100b138110408194074442e00002040080e0810445802c0c035030100e13800d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 318926142 1250 318924892 318924911
    0x10b07050705031606110a080309010204181b14090303181309080a0c020f120114070c0b04150f050a0203090c06070b0f130c06050d0c030516080a0209090910 69
    0x5580e0805102d1482c260821181305100a51003541003414031400203040b40c0c42c54019483c1c01e042540180e4183c1ca16a6000030200060503110040d0070098441c080100300500086901c01201602480305000708400b841d0001030441e1018241d40b038041c2c01030206d07500d50b606110118010580d8503e85841001e08020344090080e10b030040000b0305900c82400c074182100031605031001e5a03030020407648800d4400045c1120b4590082c032121116480001155403000080780742504000a8441020054110001710114220400322130304150b00070b05001086a400d00240e00a1410346071410f849070518082c8050201150043c0d03004030503074000d41e255606082c040010b244104000180000c01700030000d00c0c4260743c18007140e8081d0780420018141c441036038417914914526084000030070000705031000107074031512621144141700d081c200814100309590f81956100d2556510800541d10000746440680b038043d104044805848401c103414817030102c80d15880050500b2102c681760080301d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 318927392 1250 318926142 318926149
    0x1203070e0a140a060e03030c1c030507180b03040f0602070627150b030703020d0f030e041103060d02060c0f15100b030414010b060301030609052a01110a0b010b07050705 74
    0x100d001403001000e03d4072680c60081d06982c9880b003200c0360b80e41401300f40000403c0b190248884490b40950540c46114600c0a030340140c2198006402c0d0f40400480e034403900040e80010b00b034442a01d400d810000c0d05c0350784a203082810300010190083c000790020a00c04100f0260ba04400311155103400010b0742448503080108000c400744602801c154070f5500e81c60607a05059104103203440307003e1300b921010790b01c903004507404040e010f4046030808030308044041810780c805100100741804031810b01c111001c1902c00707501e9010103040c0038854a050700161046555040c03c458440885409039008001000080f6499905611140c200310040c00001026101c1d0801d5400580b17143c82e115900f907444507141c0101d80c0e01070446460056584603689032665507148061402180b20341c0020030700c106940f42c0310703007000c0d20005c0c0000c040001c504001c00082503019100c920b54001e00c3c00c04172016032020781910b0108e02030400380103040000c0010600412030b0300245142405903084814803580c1300c0c04d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 318928642 1250 318927392 318927419
    0x100506060a02150415090b010915061e0c0203060c040e060f0a030f0501020f13150e0609060c01060f0602010c180501080103080a02031c0b010306050f211203070e0a 72
    0x10180180c2006541d41408201c404041c4d0700940500d00d0b000780000c86104480850794a10b2040d108901490300404c0380020900500c00d0b0702200f000b80441c00ca1900d0742c003030080c7c540200303030a030b4075035580651a80c558403d41007984d505800504440050822014540a65000d400740d113a404500030300042190a100d04e18448550019007801d0103189191074064614a407540112020f540801401150341e0000340a0300044c0010f02030007100030310780b9101601440f0062a503209010718200003c003036540300d0003610103640d01070750740aa80d48100106e032401414560000251450f54803408210750380c1c15071000c1e032681c9980e1a400c8014007940c42040d0b905e0a18440c441c001502000184001009280500140c000030b00450342028201c01d0488480071349120048025079441c008111039603854020140103010a8800c02c448a460802140000703d855003404294170a500c642040d1200400541580c0306609003842d0302c905020000514006407144103e20408460501103444100c0a41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 318929892 1250 318928642 318928657
    0x20306042a0807020f1501060f17010b0309070503010e06041b03080906160b09060a0501090c0816020a17070b0a0501181d0316050111040302030706110a0f0510050606 73
    0xda0030580c080300078121540c90004000b40d0440c007480a0624908a0030010000725041c1c4540d648459814000010880c9028078501000c20901c50f86d4841403403004680705040d100000c0102e0303600d03510f01c41c402c2d02d040c0b5035a10107a0598038240121442d41008074010b80a184200801001101802c1051031015a0740c000030341214010070181c1d00c103140840080481c00f400e0300030b400d0340c60016201e00e03488100c2100c0c85100740c0c000804112004125118090140020070783c100700703032000e00100030710381c040040c8180c181421f10a8281c0d9a9402007080360314889d4400c6c0302c0200041101032644090b0040b0714201c520307020140c017003201d201690003101e0580301d0103006c543d030001484c0c103154083c0509943d0400b034582d03110031003070304103400340024038a50034800d401c0c1160b0741a41c0791050031540c4081068503110401e001c1480160350100b201d05c01ca030307081d180145045441011302c40c1481c050000c01040c2f20907082041c02008400300c3c4007004000880010072440c2d691405220035071003a0035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 318931142 1250 318929892 318929951
    0x1b09110d02030406230a050703020a0905010509042703090506070209060405042d0c08010912080c090a0329010e06120309120c09090a0c090b06160602030604 69
    0x10810001003010350203540d00502911001c00c991070420082d4042810341060304031420741e46010407021501501806401403003500d070031450403460300350080c4000d00902906041242c000740265196aa0b038001f2410800300440200160302c1d0b14a001080c80c4a40300308030301007614032030300045074500001034454207030b001760074030072966500b1301000000c00c0014403c8540003001d100424110b6215620401640842000ca9440d01002e0030035010105490784001000d84c10801c80324002011410b81444c071042d2820000b0740c6403078070700c0000214002c130402c1b15000050040c0c00414405d911a03032503114050490503108104801c40707040800002401400440c15107200400c2c0d041c00c0c000080e05500e032030b000a481c245200c1d540000c01200c164141c03581c040c0d00c16444c210451030034030074007900b18000e200200318050855603488030b03a501500c1164100f543d522451900794983d80304440c0b0005281d044c02c0300c4001c80b460f200d8000d400c16584140100d02d04070110b00701150b1010403074800c00080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 318932392 1250 318931142 318931147
    0xe03030115140a02032b0509030301050a050a0513150806040809131a06090406030c1712280306050d0f0302062208071a0a0618050f041101090506071b0911 68
    0x5100d0600b884418000d1401d86c0c030f1400f14202800d00c2482540e00550108020399500d500d06002c101c0340d404141c0185100d45004d03d010441c1d030b920250904029100d038000483d00301d40684001011030020b500454842c001c0b24200010810f101004145d004811141458417000b0021180111808a180c1d90207050240046003000e18260000c0c0c05441c80003030003c514691240d4461400f000590311080840b07201000314800641c082c042c525a400256003110700300380f04400c0403a82c452044984040c9400d00007400e44865110390440e43c080d00c4d018041182111052402d5014440d070004142c2c01802000c02090b181c5c0303904070740c0c1182c90710224418000b40d60240c54140881d0f02c02101203511b070012542c04813040c040c0c10001e9214484080001580c0351420041c0c40d0652a040200c0e100e55141c00c0030004c1107141e400c40582c03c1034000b4100c0b00c4000103000141e50351072031504620350060b00420b48030200300307007400041440384d014440f4410362555408040280d6000d003000c81203d4006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 318933642 1250 318932392 318932407
    0x3010c05090d0212030f0a03060302040b010c0f1b0e0405060402010e010201182909030706060b0a0519020709020d0c110d200120180f03030313060e03030115140a0203 73
    0x10400407020000104c00d4a00d0000c0001840810354071000115001c00e8481004100b5490a441484e541c0107003820034044616035990340150510142600405400020300865840d102106106014007190f44084007581032a041a50355140d0445049000502d00a2280d08551060080708100c03e64034084202c0340d00c132652415044003030100040180314107000c0c9000406175195000f4003910300b6901030350361645142003d00685174a5040801042001c0140c0d251140c1d11034200c0f01c410190110042d00c0040d0080308a0901155902402c00940041030302208586113910401250b0308039110a6410b0703038908070701030310740c0321862251003c5928401c0b103070740300111a4405c0c0200c000c2d1000008098800340810441d040051040e00804a404a0301185260740d11004801c80c0c00d00720f070041459030326400001e5492000401c1c0344030907070f512002c0b4410401e0540142c0c011079264001c0d030381ca940c1c68440d4a141100418040400649480e2428034012407003070845c0c07e02c2400381d000c0c0d45003102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 318934892 1250 318933642 318933649
    0x6020d0e010c0503160c0c2417220606090e210d0902011107030602130e101701110706092109031e081201060e0402040602031905040e040b040203010c05090d02 70
    0x302503170080244403070b21031080000307013840c03540070003602c0c1041c0c02e00b198031f040702008d00c5510056078612050054450b454500e0358141c410243d4441e540d01d0800c0320240c036940340c25015110581c4010921400d2502c04519000705800c500e0b4a074a2000480d404c01000350324080d40300c01440c041c440c400d0410090344186010701d0300300d00822401810454a10040e44041e50300e0300a03e5071064074856408a010501c4040b414448002002c5030b90244186042000303605184245a2044551010307040d842550075840a401200c1202c403030086903501d407092401c0c1017001c5c00d81c210b421140d91008100d560141880c1d9008827124000c15070381c548136507045550b0760704181e299144960f0ba403081c0303814000024803100b00408510804540300368084d45840000f5110f8551000224800d41c01070100b80b0000380d000060300c0103845a280c2890100d0072448055a0780e11550b0001c0200000385820482801340b0058010b0059100b94001c10040329005270441c2c060207502d5103541c1c0010304d03507405000342c503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 318936142 1250 318934892 318934921
    0x3040602040815150103050405060a090606050409030905040b0102210c0703171b030408030f0f041a070515040c050f130507020f060903120606030c070204060306020d0e010c0503 78
    0x244619801407400b0307280d5819914064608a041d1803441e60382080000ca52841c030300f00b82c0000828203051009090030350311152543c1d002444610401e40d640c3c00401072042c2500804018040908200101181c500b0001c126100b280a980c0c06103040905005185d48001a10444106c0d50040c103604000d00f2400d1080c0d40e0300900307081c041480750050100120b004a01c590f48440d070018980c075550b008514005050f105940f201340f00c941c0041c0010007031000048125000e42d808812801d036105941240481d4500440d0030194103070711201d44103541c0904c104010b04000d4014421540040c40407862050074400c2260001c2c4061583d20080046040c0b0503e207403503d0a008143c228a8100203030840210b0354211421750050b031008081288442d001c7c48203540040008010718680201c0000c40600c070f0f1000741015000d1000000003442803001070b03003924012a4001c00c240405684c82c2000d6002e50407100c0001605c40c9080a000342c0e14005202d20480e80f0519282c881c1160fa45854500300a0f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 318937392 1250 318936142 318936151
    0x2101080a0f0809220506040c021f06030c03080418060b04140d0b0f15040504020d030e030f030d02130b07020a031e0503131a030114091003211d090c03 66
    0x2031100b0701c03860729565600d40000707041402503a215284850004d0241c02a0782e000303801d05000c1c1c1c0c03424203d40341c80c690208007a08041803180313030320201141c14603080e00100703a503500c05092010100c90200411450b41d0050040b03c06404480d91706a035403140100844a0a20600d40303c080d080108200c444d2140a00010b07040e07004044100840140c0c6a000d0405002c4031205240c400303c03401c2107456011002c8240005a080d42e0821592502c0d50100d8420703410084060107012001014403c00e0740c0c20801d012140c200301041c2e13502ca6400309441c0010750050416100b013045480b1001c1441483d0301d05544156400501200300c0da4070b15201c100b01161901c24449484600861900210708100014890f00310700c1e13030003003452500d00095a140c1841c001c80c04180842d0800c0100022026609600740c448401c60315444140c840401c8440403640030303800200030300c52004082c19507104050300450480c5075602c507005002e850100f20441342200e43c00c3c0710f41c407a4104012a049825402c09941e11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 318938642 1250 318937392 318937403
    0xd180905070905040c171b2508070b01031208131112030403201c200405150907020d0f0c290117030711060d090c06052101080a0f 57
    0xe02d92100c001ca81030b1070300300c01424081403081052680d510342c0c03d2540c85e4001407584030251105070640d5501554812407445540c4801d845802c2da08000b111000c40c02c02e264014a070b156144034071300c0c00701d02182e001d100c16a421080260458184c60040320640e01c151400080480c00381a03d5556001406c240c2080603000b41500341b0306501d54600308014000386000345401a41c1c3c4070240601c203102042040350500440300c17524194501444142c3c000512030703101c1d0300240103a1300301100120302c43c0c1c0041ca05034014140801d1141c0403c141a50924072032060310110019a265a010790340d525440c2c0780a0009860380000b14040c6102d202045442d52144001c01c0b4940f208844003072000c20348600c615040021500100500322148040680c112080409103060452a84550f84043c01050f011401114005101424031140b54000700d1550380c0070070f6400207203843d64401405034200b4103100b0b1940508104910600c010505001d040781d40c004010300105074544c2e40c2c04a07110400008554 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 318939892 1250 318938642 318938657
    0x31103060d06112d0c12031905041104140c04060c050705030102190206010f0506070305090612040605011404090b0c070201090e070c030f0c0c1a1b0105090d18090507 73
    0x1002d500f40d00080480d0709035156000416400c039984130405010b68080001e0a02d4100310800000c070020030a0000424800083c640725540d0603260190b150345240081aa2032801d01004200030275103e181c10742007000e440c00c010800401c4d004c284219025159404035000900080016034425404040010b00c03901c00d5608040d603520210f42640c102d00707003a1000e00d118a0050030038030ba04120060060403505241c2000d90301d401d01142d0f040c0701c1c0342405410460001100c00a81d00da000c100c0725a46960404c5000c1441c050800000500e801c1c060f0103820101001b85a43d40e02c0e0a0150301503580d0490300d03100300c54440b1078a42c5920352142104a0500a0b400c0d0001080808421810f10032600f9450b0340043e2029458010b04140c5116107580900c1a4100d141012035204e5400c001900c1c400c19100100c4203061003004114090410740b000d51031850840c0894046041d006103008080420458034442400320055451100f903e00d0000103211703903602003020079002d8001700c0d007040040c109145c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 318941142 1250 318939892 318939911
    0x3060f050316180902130e06070503010303140307050702120d08060a0503060a051f08010e0c0d050318060d060b1c0506060304030813020918070911070314040801060e0a0507031103060d06 82
    0x1096a8503010815166551f1001d400d00411014070140741c2c00503403450100d14541c11035502801c0225842d10000826031301100241080340101c00b25280650000c1599810305c0030800380b15a07400030b00c04201c0010f510040842c1d80c0d82092841003060b80c1b4028003501c4030b42e95680c03c20001707100c0100402c100308079030b080704c048404d6040500005010340f90000304421307140041e03003444c00f00860702090040350005644004190302109513100403030008100241c071240d840002d8100c1c00380c082e481a1091405400049426080c001801038440350183d25080b02d1000c003e04003101c100320381050300803c2c1000081c00182c42000c0856215241d03400a002481441d00810800001180e280407214405507014032050810021100140b2505406100c41e0502400000007401014401410705c018072881d81c20064154085d0740140603208020483c2c280d035008011200d40058400c03507032032840c10021500715031003402031b400ba505400058030b166403a01c00610400c0c00c2000d40642c0d01650303904484 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 318942392 1250 318941142 318941149
    0x60e01090b0405030301060f02060c0d05040c08160e1005010207030b07111009060e0d0e120708031216020c0d0f080d06090b18010e130302120a03060f050316180902 72
    0x94050b41c080d40003192290f05101e03020b40b807484040400d00c00d641c0041c0800c56401c40d280100c42c005103600b507011600c0e46803460b020300e81c04096017088940d40640c511240c10784281411010840703000c01c45051850f01c2c2d80c00c1d48103a041e100d000d50307401600003401c1400821070071404e07281c104c08035160049242c0780c4110428140840031103006502a10380c040102070040d00c0c010501c00f036542d000030749803185880b03c000c0c15424101c481640a10220341440030822000d012280c02020300390305580c1d40b01200c0158002400d002c803114044105900100d0741e40700d10003c1e4164240704040d05d24954010152500f000001d044401120400c83c01c00c04402100c4040c042c51000341100703113010440801941c100006006000c00c1c0c02e0b007802100004010343c07204074030306c5900f1541c1031119242c08003040c1002c0f81025040e40306960781e07440020b008a44258560310200c1200c145030170300d5074500e441d0020542c0700e585514402805a0240b5401d001c504080040003044180288001680d1181903020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 318943642 1250 318942392 318942413
    0x6071407060c0f030f0b030a110d1a040506010b0708220b0a0801090f09020105030a020d0204050d030207050901060509010e120f010f090204200a0f03091a04120318060e0109 76
    0x108000420542d0002c0c00e141c1c16015920381d80c504017600748208070040002c03031ba071001702c030b0406400010021000052502da00c00015281c0390498806044031800c2c5c0f6034844404001d0350704a6180c42203000004012a120f01030354001a030084440d8600a0030b0340404504250341026900c06a135981000507120010000070f01d03940300107880d405200e40c50f114044e0b0407140c842150b0b1840d58203180728076006031f03070090450b544100e281c1030050311400d422032810000c2c05241c1204c1e8000d0b0b60744410350300b07150300028464111001201c001000c1d0b070b21050201c8445c02014a00d80c0860381381c1022049601e860315844820724007410481c1c01090740c01d00080d083d26100000001e4056136400200d00307509142c06a015141604912101d0458091022408071710030101014100900002201051482500101312090700400d071442442c2c031b001c01a202c085c200383c030119881d5070100c0c0c00080690081c0a200c80502e140d130a5401207441c2038503841d014084c5030705040141e559904607400003c02201c02d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 318944892 1250 318943642 318943661
    0x120301090506040b100e0120010c020312073e1c031b0c1407050907030b011e05042c010b0c0f011401090902010507120503060307170607140706 63
    0x2030100e840d0824805120490b01d2811000b400703070b10b07590004c404180d0441c40e1400765030420301e17100207003410341803038041d551681300d5a0303400303550800c4010840d0079400000340c8030507002812050b10329217490f0300c1664401d03055085140072281c19031841c0c40542e0f112840d44200300010545402c0c40d24024002c0e41040710204600d11a01c0c2d480414401303076a8035100700c883c903c0e44640c0400c46540c00c041c01404a05190301c3c01030683c6041844d50f0141c0c1d609002e40c200400303000d44400f10509000c040035025100101c100f50004054407080c240740e0950082c2c0000707002040e11818685401d0a503d82070517a00c00ba900c100c0207540c61a03c05244103903400d61030086c0005080c80361111218003400d400c003181c040b4620302c0c5030304118130087d041904040c1340d41110011750002820b4040c030300c0140d40902600c000078001c0e4401040c0c0800b81500b0030020b52040c40d00320181c2e6080d41e2203052400c44650b0a82451155030320940000c0c0400e40900c1e80700c41d8042482072041e00741a03013680e03000281d0300c1400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 318946142 1250 318944892 318944909
    0x4050a06060906080f010e040f0f03030207061103060a1701090b1f0b040f0603020711131a03011107060e0712030906030f02030108150c130906150507150e120301 71
    0xa042006640c00000b4201078252890500b9160800e030340e59154000c01070182000e040300c110081070400001c3d1009940490740010000c4601040707003409002500908c0c03080d00c075107090408903118030b1040c80499115030170041c07090b0b40c0300b42025040c050300d244c8050301d02e401c0d641e580300c2c2101003043c03d41007601c1040717500400e4070303070443d80034540d0720041103980460240c0600740400c1c02174140e4031840c41d0646e0080d280050715100f240c280041030100c03841580d90000039086c80200c500032180c010200c1810389122000e03103d0005011b1600321a480c0d6044205c8140c140304480000c0c4064102c190320300001c070216810300c2e485803000d0080d0f0032041021404150302c014104440f039058000c10f4240d1905020071070440d0314003d00035031580a081c2503058580076443c0000d41e510200c10507a0f0341c0d030030800c007503041c0b43e42c5551800340244454001c0300041002da46204407a1403140701100e110366402111541442d010380b484070040c10b141c20a0080a0088040d072010520310302014600134090807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 318947392 1250 318946142 318946151
    0xc08070f091103060a03120210060803091206070c02010e1f050c0709052203120203010807090e01020918040305040905040b160905010f0e1c21050403020306060d080904050a 76
    0x70158200311409020122040312007402040f080b0f9540c003442c3e80440f41c010780713126100101d042040b03041858910510759220b203401804102100e001010f0300315108162046c07040b511510142c0e581d0b502007100c059000560351303d0310300010f51140a22024424019004003100c940b244010000b0001c00c070907143c001a008a170f0800e2500041201c40000c1408900030841400d006496086c03004010500101160454581004041c0310740d00709540300707020100842d102e50710355001c9a181d00b4035214058100703003418104060345206208075011018024001c899003191010303030554a250082c410760a01c1001d04c800035074507090f80207440c0704510031241041e03e450a001212230034410542c0500c00c0065070b40c1c0c1400036982140c0004c2c91064503041029031015440006030240d10303600c0c0451803802c0c07448880c100f0001444609407803203104400340129491403640c100d855008510002e035043e0302140c04540c0b9420b050034480c401c580100c5e405c43c80c1544003408201034400a40d40140c0d180d40c1c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 318948642 1250 318947392 318947399
    0xc0909020706051e040b06040e15090706141206120f012f1e03131a1503030304030203090d0609061401090506010c0f0209060303071502030f011703070f0c08070f 71
    0xb60360340004c0108104200740f014100742c1c98280e5400d40040c11076002d9592079000400f400e9040202e4010710445000b54409885d1640741503450380300702d100e2100070601c03503400c01d40d500580790240d601d41069800d08001560310310f0104401107035901d4800f8000d018025110f10701030000e000c0c1b40d03989141008040b0b41510710030500489280c010039108050b00040c0b00011300a04030882c0e040c0e08a0200400703640b20740300c100725a400d6407020100200100400301a018031000080e1600d44110041e15a200c0b00e0309061041c1a180d10044070000c0040e0400c00207070f1000e151a20154041a0180030b000a02003240d60300c18080b0350b140412a8058803c0c02e00400c0100d43d54007070960300c80e0003031809a201118541d00c0d1451030403035a000030b03ca50b8424001910036141041035644168010806400000728081b61000951041da84648203140020010800f41c20a1003100c001d032201344010761500080f502d43c20300881410000300d83c088400a0005081071003040700d4805007505409a0807080c1c034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 318949892 1250 318948642 318948661
    0x18040201140c01150e040f260c0109060c1718011b0509041a0f040e0a2a0509010609030b18030c010f0f0902100f0c06020a0906080a050412030c090902070605 69
    0xd25070100141741c120404000000304c01941d0300f200b050380038241101686141594060201248008421116001c1001000c002d01500124400303801984e04102c03001c03d00204a4404c041e0600c0d0b56400340015003c1031604036a5280511045003800c0001405030301d02c00400c044a0070340c070340307000043c1e8041070380c0216140c00d01c60310b200c18140e104007140c0f2a900e88085200c150f07481d202144103507560030760610745c1581803081071022580b00390310032010721510070601480b17220074042110360344c102000070071181401e003105c605840c80c1c0c2e11103c003410f00e15510140440402040170f8420f5250070030304400e91800b00301a00c0032541600c0085000200307680320100301c400015105480d9800c18000f0809600e0700000c0e032106240620309410100070b521019682c1c015000c500800152001400402041d8042142403c1d1102035884500c1510303170201c1d10098030400d4074064801d07500950081c81050183c0d02c880511076980c00d01710b12040d80d401242040340c104075415540f0307585410030414800d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 318951142 1250 318949892 318949931
    0x20304061808160305062a0706140106030603050607030209090f0601110f0f0f0102040f0e09150103050105060f0d1505060a0e0103051605060c060a15090504030e13020918040201140c01 81
    0x444200340400921664182e00c00407030050045450440d01c0000c60a090042542015401cac1e400240c400c2c0d450350303503160000c004240b103101c00d5490f40518000318040170303c68000c840d18800003d05000300e60f1500c50a0031240b94000c1c1009040c0001080d4002d41d04a043c020005c0054481c3c01404a001021398914103017000d03006240043e910420091000c2c88036142010191b40c40b14140c40b03002d0713503030304103240c40c144500c550b607a80c2c54041d000000c200403054105a224803015521110003000308810b0203d00d10407810300400300103403600750003880b40841d406a5489200108410401d80d5204901c40540e0000c0e00b090340c0720b4004d82c40344081041036403254001040c098510b6460042c0176a11980c8405014002c00070154948030780c1e4080c40e07078190031203001d0b01004a08000b40d0919103006441d0307418034a1002c2c02000305150300745030749003580300b1343d5401c0030042e041c425090741803c0410000e860040c0102d040c44402401b18030441404405440010903c00000030150450f800360340341c64 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 318952392 1250 318951142 318951151
    0x270a090c0207030807031b0606081b010c1212140402030c06031306020c1f0b03072301030b13141506040b0a031a09070306060e1002030406180816030506 67
    0x85050603155001298002940320441e40c110340c3c6603480d40340b146400c5422407110601000f07100d044144117820702c24264064021507000300215042d25040314200041d6030701900002c0d0204a1501c04c81e0080b42c0c8195100c6101030306458012200c00303070f040483e000c40f0014801d01c0d1032800c1440c1080214141003000354400c2c0d030216106821842d00620842d41e5089040000700712940100e03400c41294810003000d42c000a03400a0f031502c0c1d50000104500400301d5049280c880d2003200030000d090520040c4044c541d21001e0312141141d83c83c030006402030400c0d42081038000d0340051041c40801003e00c200c40d028000c0510b074070000d05042841c0c48412000d04000351094104000800200041c2c1c41101c2081134103090101e07607216050a480403503119a45030a400180c028200310700c082d030641c4040e040e0303101a15120b003034001d00c0060045c50002081c80d180503a000304130a02c582401141ca225000b03003140c1d002d8050307035185c840c0c890038002001c0d60712a5456407041c09008100e028001907512 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 318953642 1250 318952392 318952409
    0x6160501140c070312060506121611100218040f02211014120a0605010f121101031104080109030c1106210a02040b030f15011103041802270a 62
    0x5410b200042103210700c610030004062004800441e0218089034100c14028580188100d40318170400c41d4550f0400804c417400d0202030120100505403e01540c11140302044640c024410300c030143c00c445000350722803180700c801c1c1d6011100000b050340c2c450051155840454001580b984000100038600580011840b0b000564002c200726000354036020a03811194450002c900d55070303414022982540c0c98040550710341c040c0181c00402d0148031307017116040b14144203c42003030980c0c0301c2860701c44c0400c1050091070040c00100048240d84650000ca03040d18401142c14500ba07541c90100b421030b04054406c42c0030071104d0741d01d44144062070f186030a107180b081d2011458070400100790b40b00312000801d600c06150a0401180040c034031a419240900704031000f155403410b01200800c60400d04a03101d80c5080460700c5510559441641555010190800110304107403c2c10a04454240d20310840b03401654240312401180064242d02500482c0d04034081c544803d091081c0f180150140c2c001c15031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 318954892 1250 318953642 318953681
    0xf031a1908060709230a0815040c050d0309140f0a12050706030614100201020f040609150201060f1811040603020912030c07120f0204141006090609150306030206160501 74
    0x10b5042d083c0d822070340c0d00c00305d10a40d84042601400250800066000444940700c1d4880561301041071031107150146000300708a00c43c80b681c44040000300001c4140041c00102900c00801034080302110b80307522000c00078141d01c0885008408a000c11829501048581c1b1070701c2042d40c01d1000a0140344003411042c64180401801d0008180c40c8611515000d4061400740c0204200c80d8801e5040e10340ea40c40b100c3c0d11a54840c0d903848000e04101c100d0185941d003010369031206c001b0030b00510862085491260a41c1405841c02e14078107003d402c5051100c91560b100c480c802440200c8000070006041c0741d423401038880c940c1c00c041c80369038680c01041240c581e00800c00c00340c91a4001440000b159100704554039071458510b05928400c0d8059002500141081e0a000e400041c2401144c1b1602d80f44104034600c9a03034010465502040e440f0f60b03004500301c890144002d0016111070f0952008a00f40030800d103549a001c101240c1c81240c05002c6500c140c82d4907410004280551051020500304405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 318956142 1250 318954892 318954899
    0xb1b1c12140c0f0717040b07031403060a0317090301020a121503020109050d0201030e240a06061e050c0f030406020111030411040e0f0601090b010314070f031a1908060709 75
    0xb8030342d109242c3c1e5203e0354040840d50004101c080f891380304983c0d140c864100c0c0c560750713911101102134000400803130114511071403c420302091001500d104000080c032007910303a840c2d81c0301d1880400849865810340401045800c1c1c0d0f68500740020f06910010b60381b200400b0f01c065130103104551070000c081d40c000328440320800160782d01c44151415140101d4026200305000e03c0160010880006210001d010b030702103821243c403242c0c07944084064102c4801c402c0340d843c0c034107103011150a0700070000400d0210001448506030f51120000010b964108a80b5015240340003030703e040300b203188000343c030380c00010148030740ea03820302910b9160b020f410b8405085080c55651032002c00304014040d0b010b01d50700c400d1404030401c00c224030400d14400e80c0c00d035a043e51315654400090f018201503a804030781021009003000e01000364292040d0002c4e91036410f81c414100c0d085014200440f4401d4014001c0c5044100560b22a020101041400601240c000f0716000d009030906000802540c10f12030300c4071080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 318957392 1250 318956142 318956161
    0x170304050a080d12240b03070306051c0f021c0c03120212040b160c0609092a030b1f0207230d060905031603051809010b1b1c1214 57
    0x14030310300751405000304021004c8182c00104896000f841e8a8800174030800140c4c0c204540004c5008405c16503062041ca5201c074103010103480c010303040e0206940c03404103100c0811000c01d1500c00c030510042a000c500800d204503608420030009040e00da40301c1e00b840030010000040001603584030140041c0c80f40e001c00340400d03080d074000e40c804d9040ca4074000400340c1c120804603003556162540180c108040c00d864610050403030f41203018110540380f0708020002c0401c4803d0a8a40407100f00c605460a4110740070100c015201501031107410162181c1001300c04a049407400103100380329401803c04615200e41c865000310b40755200903650b0312110600689407541e0f001c203c00c10b80c128401080d51269846d0581c6107200d0701c074542203007150600300d25040590004c0101041402240001c280d0000d0101f080003a900a124040e4808010082004604203101003441d29418501c00c0e0390300041450201421030030441010b00000c2c15070b000320b80014029100b0105104000b505240c0a41f8002198 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 318958642 1250 318957392 318957407
    0x607140a08040218041b0621020a0c05061e1e130503120112060b011e11010b0406030302030a26040206031f03030f0210020913090804170304050a080d 66
    0x900104403107040040d0954844201461420840850800c15840c060404d0601240c503498101340344102218009041071241c4c1880f12445080d61403110381d52032441000000754881c4005406020200d942c2102165040c012648115502d10240464140c15079004501620051102041040d524490f60b1344000b000c0366145c1c004200e594074445403030f95041c03941c40c502800c071024111001e1040041030140c0341c0350300c0030402841180d051080388503010055401203a80340c41c43c0051001007000702c0801d807207001060881c81685000003030b50601903010500341c600981043d0050b030300002e50340d040d40f03610014082904804005840744030481d090408540305000d0800380c03080f003012003c21a9002c204038442442c0f0112004a03a0056130303071402400106000c3c09040c0503015140714005404054000c88981d10b100074400080c480c01103100764010140e038030003682d54240901011030043e51983d1443d40d00c2c150440215100e81c500410454280c81c0c2d0340084266802075400101e40e00d410004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 318959892 1250 318958642 318958657
    0x51b330c0f03091c02010b0a090218010e010903020a0902090901080601030c0e062b0c08030a080c0c011e050603120906030f0402010e0a12050f12070b06060d05010306050702060714 79
    0x400740d580d4030303030581503444d0260f1555418540405a0b5000480580560007038400070700551301c07640f03080c0e40e4152100407409100034006140b480c40e00005019032081642407103080d014104064655201d40100e001c034029500800001c0f81d0004040046240c0303004202d005001c400d002f01169811a41c3d00e0b2228400c0c1d01c01c1d41840f405030004107080e0313038602d2070b400d00c0c03c0d0b82144400391004005001e500c1c1419a403505807403040300710401103500c043c0401282d600361441d4450b06c41d0358985074220081507001740b16041e015540e528600308407010f50343c0d0b64400c507421560080b442c3d04060040604203c54a07071004034652080002070708030744800055030340c000900f005d40c10041c0d84030300050307444284181d942c0d60301c069003010210f0140d00c56503601c004180140d08540031211a003070a2540c3d0101400c40304040c8500348940300000c0d1247c00b003d0740c8800054905410144104225403e03030f082038008880040d190010001070702c3d030410820b5405a11441d044032508510303800c44119104203013 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 318961142 1250 318959892 318959917
    0x3010c02030f0f0f0a02060a11030106021e0f16030314040e06090604141905100506040b0a090503070b220b090409020409120203190816051b330c 64
    0x3c012028801980640c0c2c1c0401440144503660512124001e4446404031000f40980f454024801120146042034a040c0e0b00241c0040543d848000c01100c030b500c028400613030040c821642201024034041c4075088402c034801010156181c114500604a2604000c0b00c09400101340410007000b00607035081c030b800140603124800301d40c0f41c00010501038032a545070110040000d0040c040310010720520440322010045082049440c2c20b40a4407030704110b44195a0300c0b41084c40103204041c20140100a502c0e00350a18912080d503901c0803a042004550240188800104100007070a40841e40c0c0c0c64024913004c0c0d142a0b56082241ca00d1141c014020b05600640d5032b001d20408544582d442441c4d001d40080c450440c807403d4000007075882e8410724629441b03944043c0e0324080345c1e01400850380644010803d07950703610710102c0103d8283e0456018040c502800141806102d80140000d8800003441134020420609440080002100a80b034108080401904124400c92420251059440c001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 318962392 1250 318961142 318961147
    0xc1e080601050f0903070f1d010b03010e06030a120909050c0c060714070503030a0b0a08070e0a090c030f0b090105010b091507020105040506040e0a05150904240e0f01050603010c02030f 81
    0x34903d000c2c42c0039444440380c05100d2034102183d060500e5035400f04948035904400c4007003c8010100301704090a00c20342410b0001480103100305851002c0e11903003d00c001e001c4800000031902c0e031405007000c1150b000041003032002d062004103504e0140c150702041d0481c0c464a082e10001481b035687c240103055108200703180c400410f80d00042400c6801c01c9070007904a070f40346e04299901b50004c100c0c2c09506445507400c5070300022035a00100d4076104072580720f210070403941d8442a11b400034104070b800c01c4034000b20401c80800000e0f15409040c1405002e201000240e2514504141c00c440c0e06801140200b503081c0080c041c5a52088042d8540c0c0781034040c03054941d070341440140c03554002c5802c2142d000078003040c0460a041140344a51103000303a00030601c0301e501c5411094114122090740a5081006000003402003001c200c0710041000030040c11292600fa1000000c00b260340c019501c1c00d00b0b4000c107500840c1110f00340074541c0c204104030020080d1042e044c4029640c0e2098000312136103071902 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 318963642 1250 318962392 318962407
    0xb06010c14100218090115031109090106110106050906060417010e1e01140714030727081c091a09040204030b010305160b09040905011b030c1e08060105 67
    0x204503098941c0d01d41c6400c0341c030080000c0340341e0400b940214001014840706800022803502c2d218030310134102c1c4d00001048908107807e840403000ba0400410a0101d0700d01001000504e44405100070700914031380d9a01403924012030042c9003581e031640c0c44184540540e4052101c55510082141c0483d015a41c0c1143c0b9401c44000a9000d4010108100d40a00030b007507071409040b0503003190045260400001700035004032400300d418442401c0c1c41080014084c40340c1c03000c81003590401144c00c00c0103424400e008082032005c03a045020510490000001928020407051004002e00b0b9001c00800c14804103a03480014024010115441038150380e111408810801400d41e00440d0b00680025006642d142d441c0d06021403c50170a21003152103102b100c001c401204414500c00040d01d0040c152149440c1e4418200006800344820645180d5170783c201c0400d10103058080c20004c0c2c1d8143d14045424512010060100580010301c030150100c42c0c0741c50483c0d640e0241060358001c0090038004c2c2c03140c42 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 318964892 1250 318963642 318963653
    0x105270a0b040b061002031206040924020c0c030a1e0c0f0609140103020c1507030b1e010f0810050409080d0c09081b010203030103021309050a0308060f04090b06010c 73
    0xc0380d0005003101c00d599041c4414800041e41e0144203007025940f0441c0810b80c15422680c0c0d200e6a05d2056500011101040341c5103000e8010040b441c1c014101441c0c02d240481d990005a64810b100c0da1010f51b0004140403003003024001d18880d8001100036140141d90b41c0c40e0140d4600c014610710108102d040d0041c4204420301220350050800e89465484458965074081c0c030151840c00b91a10218001c0d81c1881958817034000c5031210610392025208005c0050111480301c1d1015064206054990b4481c04107515544042c00066284407204c40426051000140142c0d503021021404c101111003003080c41301c14614660704030b400640380002d0b40b00150034009450b000f47c6829003852424039046005040c1c0c0051950250b61040c41949d01c10380481030070b030581c6489009628056007041c0010005850300020380032039070812500101c0c0c80d4100e5520b40d800d0109140088010400ca1420b010540c03d000200712181d4006407002c003c084e0051701c41400d902c030000c003d14104062036200904200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 318966142 1250 318964892 318964903
    0xa020d0905031b1912050313120f0f151505100507030507170712030c020106170709050603011b020718060302130b0102330604060e0105060313020a0b0301050909010527 74
    0x4900480d42c132200010f06d0001d842c1d42c0941c809028a01d480d600109621006002d804c0784107500c018104015180c81e6a00c0c1d052111054064500d200000c00841c0011a40c0c014211704c01080e03002c03052041e09120801106d010582000d10800009000c10300c0084e4102e41294403050700080c0061038500340300c00c03a546038410030b42d00070a6496603140303120718250550400344125000342c0013840080d440311700c40111402600e551416642c40385504002c4c2000a91110360885001381c00480e5900c007040728008400d255065140050703100e00d00400280b044048001804900071f1000c2c07004a156400107003014407010608000543d5078154000b1507802004003a040319150310500d00010001151380300078142840704400103074020f0000483c0346c0780902c00c900c255149402d8035001642004d05008140e0001880d404000c1d001d1260a40543c0e04e030040321000709941c10005a8035814030f410b0105a00d0007804450341c50f070405041c044800710a42803c103c0d404140009018105401001854030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 318967392 1250 318966142 318966149
    0x109061b02150315090903030c0a030608160312020d0203070314090a091d0309130506121b0a09090c060305070e12010207140613081606020a020d0905031b19 69
    0x31200ea4184000b100019014500c2072003021030441031146510240a8a40d000701e500740480d030400c00018403159044001b50203c0340300c41c40c0c00103c03961180c00181c0b400ca00f41c001d07440315035140c507010002c0041030b03071102a800e861403000d8188204c070004017954038061031b50024140043c03401c48844821042c01901c0301c40000030040d240c2a640c1c0c9900e100180801c04130762031511400d420703030030030241e000040b50301c50071014214880c1090401c40c544001c01025200c01d9100849402d1000c0f1042c4c100008401c0b12400c604d0310364280315103000c00c114040254050f2450341d080001d14000f161800c18202c0c100c603420b04010802e41e56914088801d0584210366a0348042c1924501112103815809400d00b1071150401c070100c00035449040d561501d013141d62a440c682194411000901284080d003502c484117424221800382c141d8580090380c0000007000d00603407000c21444481c9603c80400e10003400158013a0516184800341c001c155003030100318600170818024180c0d1400c01c150201c4008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 318968642 1250 318967392 318967399
    0x30807050c0d1e02071d0901140a020a020d08191a12160b091302070501180b0403090b0a02120702032506030b061c090609050105100305010e0601050109061b02 70
    0x4a20350510241140d060841c41c0c04980b0320709614800140d0001405d2010b444450313010407a14403007070311200c000d000700400c414019500d502c524040c400d0310510060040400c1400580c4070704074070000074900381d400a030120401c8016000d01050301044c9400034031000b0308520103d651030300c0c2c1ca020004041c8030b03070103070b03412220200c02d0000a0758085003804034000c114500b01c0c0c24940d5500d1381c2801d4018a202207074401001071801d00e41104690051440501c078000101d01d4500700707410250f40752a815000d44a407440c28003040101a40200a1005004048030030381c108842e203c8002d643c1d06140035504011540050301600755035081082900e04540110b040d1440080f62031040358030041c6202d0900880d06247c264140c0386040826690818404010913650080c800c680001510743e440d000c0c1d600d595500711820228000b07001d501d1240c003005002c3c224407891881d04c40c2c210398440e078581d0000d030460001401141e03408000042250494500b03560300c2103c80807802a0b00d02e81c240020360 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 318969892 1250 318968642 318968653
    0xb06030106050703110d09061b080f030402040c02060408040603090311060106110610030803040206091f0918021809191401180902010c060f090203031605010b0109060903030807050c 80
    0x800079400342c010b08296209540d0024204681c880d000c0d910b000e0864400c0c0070490294052141d240b0030401c9201c41c41284e4015a41d0721482d03180c01600d51700c54114501d900c1070001c00c0000f0b60401e400b883d020000030784010181c5251a0301c0d901c03200d00850081008268490400200b8903100b0004080180451001c2e14440d59503140098255242002c40750900d0040400040301c2201009000080b00d40008103540340d0342c1c0f90790821040743e1044840e5a07110b42802c00850200400d460010034400d01038803003c1d07032141822260941034035080440c001c3e99004002007542e08800111b0400010350a0742d0000c400e0311614500145c0c00c10480842050f5480e2140c0c4600000c640304050f81200d42e110301071030519081c100e504054a18083d0043d011600c440c071340a0005040c3d5110201104d003550001907000c41541c0000d00350b50000d214004d04e041c081e00301c001070005c01e105042259809003010315400c3d00e000301c00b80480186100107400d00513620009403010307001d9411104a0001d08041d2913 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 318971142 1250 318969892 318969899
    0x706051e19110f0c0715050a080a0e010c110714210c09090a020a05060c0312040804080f0a0b13021c050304050406170618250906061205061e040f0b060301 68
    0x103c0da0018050f01e00c0320321a51400240101010920103990507442c1e03038462030485084001e541800002d84000051551413070740400d104c5080c818440007020654662100c960418070151500e10584c101d2241e83c0c0c2c043c04007070643da84d0f050503d48200144000300701303071000e202c40301e5040415020300c407078000c4550010814440c0c000b080128600e442210000107494544003401403e01072008035181562040003140050701a40b00340c80c1c1e10a219000722840c00e84c41e41a210b051001e025521140d5600681c180c0082003034414103203601444946070607400301d1b26038000816070760030381000011007001d14403444140001030003183c0180c90007074414058550340c0c4080c1c60010640441c06e0742c00d030103180081195244040c01e0501505007030320041010a44030004103002000340c0620000d10079203d080015104c00c1d40c06100004c0001c1c1d2a001040364040f004841a6040105023621500d10407000f42003803094520000480031042e2000140c501700c4003021001042000380c4076a00590100000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 318972392 1250 318971142 318971167
    0x90b0f040618060b0906090409050c130e011d030406080415060e09010f050403081513060603050709080607080118150b090103060509091c17040501020706051e1911 72
    0x10b001c051203140040107903c0c0e80702c821000d58001d021900340e001000304800038961a20340c001d030001d2801502601d100305c591100051920580082c1851201e03100c034104000c0c0705081c81101c01c4485006c40c0c40d5960000b101d542501c034440e6014043c180310551000c50144540303105ca0702484042c01008201d100d4036038616a220781e4045070f04118640c03c1000240311071050b801094055036040c0c460a42586400d03401d501d020440030307500e60304031110f080d0f50740410701d1900034100100080e8078002617504045000a1480c001504004c2840d170000d401d1105c03403548a660345045400c1c3c0e00ea014140c8180310328480c00740160f00c0345055001c0c0f95030008500744004100404011809032820405141d4030028048204e00403118401c594020b2004c0c1d2407500c180040d811041e503110f00e041c0c3c170290000c1c200c2072004003083d5030503200c5030f50104281701049400c0c4213250b00000d004a110441c125000c0403e440d031040101803d408034822107420503400c40c0c81d04800d006d440400985a101c1c000e24108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 318973642 1250 318972392 318972419
    0x3050c160b04030b01060c0210030b01020a0506130203191a0a09080c06060a1a04050d11120606100305270102160b0402090703020901120e070b0307080403020c031204090b0f0406 78
    0xa035903080c81c3d0400000c6c0d140c090820100d0440c0d01030400d100000141c0f100783c000300b05200c0c440b415800b07414000c10002c0d40512149100305d914000310081c48241c0c2c018907252110003d50341d0a800e080800d14400b151042c08041c1c1ca0348501004c030034807951515001300203481a500c0052a03294003040b046082d090201d0700301c1c86954140c42c0082e103596a42c0c5442c1c00030030107840e07003e44184100418007140c24810908519140905402d072083ca0002c40402e140341d4800007640099001441480043d01d428103503d01342010510307040c00141040c9901c1c401d8803c550544041c40215000400c00c03004003901610386076403440d20194294086400e0401c80001d045030120b20481c492000140824060703c02e4414a134010385d02c4212040ba0035402200800046105c03034a18400d03000300103441510301c80194811010b690701c500590809160107450600c1c1546564400d1300304c3c2100d04004400c01094404680b4900004102c61202501080540c1c0c0480305558005052103401300e000c0350352564 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 318974892 1250 318973642 318973649
    0x120e010b13061a070f020a0b030103030311040e011707080d02011e090c0e090307060c03020a110c06030c071e050114160e0904020f10080106090b1603050c160b04 71
    0x1020050540e4180e2a00201d800d01e02541c1e580f000040080038100c41003c025002041c8a85100b6500c0c504a8001658108456010903800b0340b0000050041607854099410800342030000302c0d040c00e051011100803c0d0050140705126210740e1142c494010b801c2081800030121541038884c20025000024060b207014a40250354442e030108400b180e5a0610034450215000900728146a00344030f101c040e009030142650100344030520803013000c01c241e80b240d007110070030b140c40059030340c640d4450282c1030222201e04802283c0200c100d0800035220002140d900c800740304d00d1a035842d4aa0710301492a42c00c070080c039040c880204e90030501041015030001800840d02c4150005542d202c1c0e04080305076804403078000000b40e41a8100304582001e0342034075041880100a0384130b0040d81f03004203445c146036516080000710300340010000c0540184944020b0866000351501d801e15080081084c0c0e00500d400400b001030018400e40311040502800c84001c0c0440c50924103259600c00c08081ca81007400b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 318976142 1250 318974892 318974899
    0xf032a02070e040512030702030705060705070b0105190b090102012a03110301210c08032a010b030303040b0717040b071d012001180804080d031e0c120e010b 69
    0x500202e5901c42a4110a00c1640c0c050002e103299810600c084045070070141ca0765042d4402446480009001803162034441d50b401e85d582a02d07601d00b410701000002042c2d001d18007411042000c6503120040324103d00a41c1c07581416a5540c411040040307004200e0186020040106030004540c040040e00401c0d0230400f2903a0207006039405ca14100e4800e12007803281044c00c0110011149030910450542d072006405005440d01c1159201c40c0c5a00f554030807900010303104603a09062190100070f8481650344406030000b001180f0034240429034a10014001810300300e0b100e80091582842001909241215101817400a04140c44c000c60010026902080462100351000070b00182440c4c031031685090596403201c1d1a40224640118400310350303580c501a5480d41131b200384c1d54400072202c0701654032460368940d03580d00e0401980c1c18001055280f0003014180483e0429601030285100d008000385040002e580760750090a454603046441c94440031410300d042c518491724194401941c0c41c2d0150f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 318977392 1250 318976142 318976153
    0x717060a0b030d0c0c0b160201140c0a081806040815150607080a120e0c040e010c080609100e040308040b06011e0e13020408070305070605040e0103030f032a02 70
    0x9880251609218041d0b09644140c141500c518454030444440500915010b4000e0303481d03040440181c1d04c203500c0c00c0184000000c1b0390086583c014520800c60700301040031414034900380c4006454802c5d80101405c4400d0200d071b4543c412448041c081041c0350300402d06035495680e59a9244c407214a0500404c40380f071030800260f0710740c0010000f00300b1106d008211919003925552a841c054102003021b00400c5010702016521044611800310594580c400400801c2c1040d0108410f072060f1003001c03101a410456200c1c0c00940011b519600200100d0b82080165512003104c0f00400325548440c0d1298008414442456040301c0742a004070b00074508030351190b503040019101d09808030100c04401c04601c3c00308994620685030080003000007000e000e00c1d250481d481c0d0302079811540003104a03412044041080040400041c4001e0000742425401c0c2032a0002441d100030052102905000010000c5400c1034465030203041c08a0340c58054079074036103851181c1d03011001c043d088034015101e81c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 318978642 1250 318977392 318977401
    0x31101090b0405100c030201090204062d12060b0d0c0902040f05010c02130b0a0e0a0f0507110a020d080f1603090801150320090109150603020c0303041b08071706 71
    0x2071000b1141070b610040c10122042c01005030450b0400f1482c00103400b155038501050300103a907140074920042c0110112074203c0b580e00c5204500c0a840015540c03090700c2c0b903141c00c0040c0012041051b0b05c15401c104005005407407980170900c4070714609070051651491140c0402c640300d00c0d5000d4010f68012845840480d0b0700c80340195800b551040020307600020890300003840e484281c0010000080c05028164000c0d524201c1e00d980000540d4003400440d00c4a48076072410015100d020b82c482c81d103161040394084800c204949410503080007a000310035102d090424003242c10100e0f080d401740c1f440c12030703980d540c2d248040440c00b40e564401c800150300107000142d528014002c003084203030511a4031000a180d0340c0e030340c01c406184913900744a0013020909081d542e03a841414500030008040301082e03902041e0010800c2c5001600003c05061041c80541e400200c0041520381c044da01088060915a80b550410041c20150b400b05485220301180480e00c1981c009001d000d51074440704440e60b03502e8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 318979892 1250 318978642 318978659
    0xb07020a12050f18130207200904030f1202120c0d0507050a1413030f05070603150e070e120d020a020307230904240e1c02100c090f03110109 62
    0x10044006948401404446695010407401001e12a1300070301d0310011550100c0c100090ba00f06040c02c0d1021018214540c03080c2c83c0d01001404011400c40b098200c600e4260380c0a854451200481c108001d4030f0001c0d180081395a0f4102c030540500d031003002105261407542c0e2441e82c1d115540d0a40c1e0b107800d0201090107580103c00341c80e42d09880303403140c1100c0113040c81ca03140c01e0340020f03580703044850300000c0000106001c4180440d403280580b0113001034034200a4040c003914050080b04039001140b01082003201c00041100f0b40040c20b40c58480400105500010310a80e04491442c90707500a0440f000001d540028003010f005100b40c040c4d031010780c0c0d22912070041012803525a148403982003050013242c5840d007501c2c1e0f4842c0c400c3c40c0f40d00e40d002c45e5900311180e001400c4d409401c80c5581e9644014412809c004040c008072220700c00c0002030303500e03d2009460f0b0a20340c01c02020301d600e07040b00800c0b050240d56928054125510506c403881c1d038900f492880c1c00100c8800e43d01140003200f001c00e1051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 318981142 1250 318979892 318979897
    0x30a090b010f260309060901030902090a05010312081501030c021f06090c09030c0509092b1409010e01030b030309150a1412060105090d12090e150a0b0d06030b07020a1205 75
    0x40f00000c0c505041804c0305115280c0d01c4132030f42c0c074105942d40c0b680c00016544c1303003149806400c04a400044542c110310b4880c07040d8054007030b20400e11410300100b00c00e604940c1d11711402c40600786804908250501e0081e80360111a02407141d41d21a007003c1c20b141b841c443d5000e801200c109600501152042110589949840d40000741080d028980d0911107030511210b0542c11120580888003002c40c00350380f01e00c01001400220141c403c02a0203500c074103174460000d075056040d010449191004180000e0074103240071100d00e05054441c00410500d40e0f06009840742d004c070140c012400041c15800c00540b40d48600030740c030007040e4031094815040100308107031520100d195034881c41c55184d41c03005450b0781c2c2110000940c0404031800c074000052071118100e0f0f241c807054981c44982400d01a062541d2782000349602c8040181e144049111750700c00c0301c005c00b00c80720341140654800782142a140038107282c0d000603003950004410f1040c030703640c0043d0111201d801040031014401d800d9000300d5051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 318982392 1250 318981142 318981209
    0x130902060f0f0c03040303090303080a06050f0409052814160306200c1005060108060f010c050f03160b090102041410031e0c12060b0f030a090b010f 65
    0x301030042501c100a5240280030303503001001040e0400070310350122071850b8002c1d0400c500049984c0e20410805800c8460a504140554020701040b410000030415181d204c0300d07914800e40e00d500155081c03040c14048551450740300c0d08042101706444038440c540690000080b1850b18801100300c050000203c0c06945040318100404421131035030b00e426000d0454100c00c02c9a407100090515460070706c010081443c400c004014145072034002040c0300c1100c600510403414000000c04004d20740c0da47e03449149464100342020100c501032418414a0404240100745a5201c001030190100b1000c00c0049c0040d4890300d544a10f60751109000b900340e0045200320006850f42c548050014500124a80c11a008500c0d0014850f5800c100044683c1351200c1d1001410f5501d2001003c00c0b6484507010b501c581c0344080510039240341000c0c00c0741c60312503520142c2c0340300800300116441c111903810030944c0c0d540041720010a541c40305c0d00d0909000d1a845042c40411410051014600c2846400000c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 318983642 1250 318982392 318982399
    0xd09051801030201080402090a0b0d03170901151e031a04150903050d0e1f0506102604170c060105011707020703030e01090e0901050907050307030c1404020720130902 73
    0x16501d40d82c7c20b010480e28080d01c0003055546501c109491038440d00c4545441601076030311030002200000104016450152401c0da6590500c2007091420000301800d00441d030b20030000040c400e12401000300c60303040a0704010f04540401c0001c81200000e0154140901d02400c561400e5100044e854000c859042e100140810824440941004415840f04a080000c1400c0e00c5201819808105400c844000d006803d2542d91040c40100d007810044070003103182c0c501f040800890320740340601007542d0054000780c007125000002820001298a00c0c401543c0c48140aa1035003490104a071700c62000b400f9990018a0840c401c40e0100400a035890144d4143c0d00905025030079520100c4042c03401041a03030501c1141c00000420050442c0780c01d105100c2f03480001880d0500c50520340c20a40d250340407034440c0e40b0041c000d1020a0442d0044412151641d8035000d032588081c0c0800c010b0b002c0d01350003400f14461f9610011080030324103545207848074125142440c0b0100346004004840032400060340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 318984892 1250 318983642 318983657
    0x1d0601060c080f2208120f07060203150a0b031605040b18150c0c030c06030f0f040204110c010902040b1c0303020f0c0717060703021611120d09051801030201 69
    0x100b502c020041c400c0d1141c0c035040c285043c2c6070599401040e541400c0008a005005104200010082c41030034050016941d503103182c80c40c00c0340c030036905002e88000903090396400030201c0e59020780001554110440503028044007a0348240908094000b00d4111220540c84500646418451400c840540305100c002605280b402c140c3c0c520500c003d00d208603007006007400e85190311082c0001525401a03980000e00c0030404000506081180c00c4c0c040901410044c4180400c000162a00c50740c003040840040b260f55036940002806854218401d0141010008003840c4600043d000840118000e5038180144071401d418046009000c041607200c0301c50138a00707400003d02c43c0e0020032074030b50400081403c0060040030b00741080d50607440b91301000960626104010b00c10f01665a0001c0700382400c50902d602c80c4101d50000100e820004c140c1c0c00c2180c0c031a801c23940c83d5001c0c030a0082e9802d080342c8040300c4002020389102c0660284502c501281d200c403070505000081c0071416264183d480c0d62 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 318986142 1250 318984892 318984917
    0xf0a0305150f060a03031d0f150706060506070209010608090a060c080106030b010e24070212010204030b0708011a07051501060810080109051b2707080604150605030a0605060c011d060106 82
    0x10403030441401f03819400030400d41100c0065883d100c1d038072003001640c02c50540c0e91801c6c1c0b409004807004c81e0300842c01210240403080150741d85401044c111109420001c841d03686400582d4100314440200070140381c50032070070100c010341c80400c0906858841e2020460017900c040191201049203801c0f41d072100e114220001d0017045c03a8211504040d400c3c0065040c40350030341c00a1401810902c00300000d82d80032030204144881d8104160700803155061810203941041e150f207a00684c3c894042030503620006070b90003040000c001c030304240d60300d10040c4031655031154802000240b050340e100c80302800403040810403a006200f0000c0701a440300041c140d0009041c0702c17450070464189103a40c0590061103406928090030301ca01e000c2c01030124030907900e1400c1c08001e0311107a03025040d10f006615121102d80700305003003e01601540c880c0d0811a441e5599400c040024041d16000540c00c61004200c0644543c0150803602c44c0350340e00c5c03910f005c0f08000b004909544500c244204c80006500b0500c0703c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 318987392 1250 318986142 318986177
    0x1208161e030b1909020903012405010507021302030702070f09230a11070302061e040503120603070504060308040e16020304090b06161a070302180f0a0305150f060a0303 74
    0x11002c144000e80f900500004600342d1106000155100c00c102c6a00050b9007121480d003842502e800080417103601484080106001c95030003828081c45045c4032000071100103550b81d5040c1100300c0e9103261010b56a034908008001e498a589105104c0170700c0e04503202103440051401511003140d201980b41e1050000c0c2d00d40610440d1018100900b099030300c0d00410102c80c030450061120500a400074003041c00d140445821041c1c104030311000558110080c000050400310845030102032070340e9903110584403100040c0c03d00780160301c103075032141c54990000200090580907104a46500500300d0480e03858840641401c4c80145091005130410841030190140d1640301800c3d01d1805085142840f043d42d800c0840490000c10503120a8080c0121589200880591303d40c042c010749415800c05480c03010722200c0d8207624010354407a00c82c0e1034240038070380c50394a020001903810004644030040c0c403881204180c882592010b50750b03441100068800e08080c0240781c116941503850320760500d05030110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 318988642 1250 318987392 318987401
    0x90b0f0c070219090e07060e01021c050d0b0306010609090f02130302010503040528110d0309060332070906020a030905060a02031611011b0f140a1208161e03 69
    0x10801e080e104001c085180300d04c9104401e000341c410341c000d24019040c500043c0800380711008403030440d403203070313008581308404d019800d540203241b420000e48800503404020b0240007003010440d018410380000049483e84192640111a8076908c02c00c105403e018801007644a44410502c4890300b080c010401944a4070040d54814010410f50700c07100c10106201c56064003600d20302c030000384102ca460b030a01c038005c00c842542080403500e017002c21030340c0d81d0098030035545845140c05241c1d941030307001604030500caa0340c4680c003140035440b24540000c41d4504c040303500641d41900040c07000d60000c01c600c0d0000440e00c0e112034240d110300e01614905400c000e10340e072101c0c0450046000030711042d200c0c00f903070500c250341141c860750b008055200010001030040726040200030300d503207054403e03038041084080700c81c2c4600d4126180191b0040c01306030350743c40c1001c1e03c08020aa20b030b40c9000300300941e0b030202400e4050904002c20405202d8102000c51b0000110ba18580410b9500140c6804440c0a07070710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 318989892 1250 318988642 318988669
    0x60108041403030406150806091c050c07080a060605091b1602040507020601060305090706081501170c19090b09100e060a0c11010c1a060102070306050406090b0f0c0702 74
    0x40301d8607180d2030765121800e54205072011210243c84481611240c90600c896001514418001701036625100c2441076030340140e02c0b45040e0054000e0b00659505109070100c40c050075011040320b071103590303c91829079036145003001034034001e10304200170486240c201e065178000c07026411b4104110b01c4107200c0e0140e99210042e072106902081100d48016102d90250f141306000b07a4000c0c00b983c1d0700d00700c00541501c2e0001d140080a4110034818000c0540100314240c1282c0c1040e141072040d030708000181c03054901c0c180100b2450005c1c1c8200020680c6000081c00c4010b28948501c1f00c0c00840d15090703c0e11000b902030071000d41014886800780d030400c40d1080345480700902d404100d801303480010982940c8408a441c00007030311268101c00b0f019040d50500300380c103000e280070194596540c4450020f8080da05400766503860f10008104140c0c8200008000345400a1742000141407d2a28200070300305000101c4801e83c0d03200000303d00d03000200f0b03081d110702c0e400e44e4bc251400529a0030481e03080c48001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 318991142 1250 318989892 318989903
    0x50c100c05220914091e0a1b0905090d11060601050706091704140306090d0926010c26060114070203010207120207031b08030a0809010219032f0306010804 68
    0x10002d010045406040c10a18124000484501744620b400741821017125850103c104242d191076601d040002c3d442103256040400d003400c102c1c06910700780c00880264840901c4038205420b200c40814003164001002e102621480300c00750580a505494010896642d404610144165000b01c2e020790003040c502d91042c0302c08840000010f6402d581d0790404c2d040014694103502c43d080302401d0403c00c0e15000042d4900034400000407075001004041107000b680780040c1c0342611410142c58403030042d850201c0100003400204404e090007007a42c0b9254484590f04001c0300c800780501c0640412250086c1d03c1030b50356850960310010781a0447d807140340126010340d400c0000101041c03265008500003091680900f40181c5142848040030240440c105c406000d071204c2040b8201d000030031644c82e0582810990b110381d8603075040d507009004d10306051002c44400080c0100b025851f078042c2400b0360301251241204400c040c01058100c05d81c0d9002c00e405401000450210744c02610340740c2c1d00c04e1151 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 318992392 1250 318991142 318991207
    0xd0335010e071d01030f240519140d12021615080106030e030708030f0a0608060702060a050703060b13170c010e06090307050a0902040f1d0f040201021903050c100c05 73
    0x2c041b458102d441d02c401d80102c48a0b60603107a621100c101d88401e00500e002c0702c1c0704a1251141d0041c0e511261580306642140081c4c03a08000d0315214154a8132105420120118801c1442030001c0d44075038124006100c200080080403420701a100d1005e4448103455032140f80030703030810780103030005c0c0901e49074160944010310460000440c0d62005610400c01c2c82c81e1039425042400e643c40a6130a66000800c0c030f40c010000f048a0380d580010250740c03249212001184940341c0000507001450b103a005072036015030000b0045803090508a8540494466403660035460f600200965100d0b6841142c00d030001c0c44000c02e81144c3e140070070292500d00402000c1e6040c0d955984c00140f02a0001d6201c590840e0f00440c0800594100c00540740080c011140840f03401d00c1d5a00c61a600d8150040070b0210380c0c05000701240a6900c20001a100302903041401450341351142405462038201110310030f010f10901c0d5070074240103080d014414000b0456180c443c2000d07c000088940908100ca14000400300c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 318993642 1250 318992392 318992411
    0x20d080418020d1a09070c020a0b04090c1205151504051009030c120b130609021e0405060d02012a0204090b0402011205060303090d0335010e071d0103 66
    0x10600101040c0c2010040141e4540c81401d02206440f80021310302c2d525079240110343d842d5224043e01036481b160034645001010054400a8149801a000704007841800304010074241c4641d4048101c0da40b050b02d90303450300c01c1d580100c0c00a55008a4103103800001c90307c1e281c038890512203143c101c41c0d03c0e9050094200b0340c4440108040c3c41c80000950000303035540e00104180003400403a10301402c25248036040402154407400301111000d04036103482132240e0301c4001400919880b900708140e000389205482c0f41c0c9c010b10f405440c407070049e12520440c0750801040d1140b4040301e00c0a00d842d4181c580d543c602002062a100050180110004103072280007520f0050ba00e620540d441d003441502c0415060800b07000050411f0015103044001503d040e040c010316903000001e031092610308032143c2046034a03501e000c40b1107a05c00c032000d0f107485d03070004082c55122201480905803041005d00212160b0f0b41c038035103007040d10b006031443c20229100c600d4049982d107403900c00308003d05040c140131410101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 318994892 1250 318993642 318993659
    0x31c0e0301050f0714040b031605070f150b2707020f07030b0a0c05130918061107050d05070c050114070b04031d0a03031b0311070306050604110403050a020d0804 71
    0x1281c0c1e0904140c40f41d002c0044540d00090000c142c440303269503c500307160500c80711003c1da20001d84091131400d0441040840144a5012945c115130b00110300300e00c0040d286001c0c6903125000d0b2180c0302d0346042c001e42612900b05404040440d40089101c2e002e039502e00c1c684940e403058094144000c60141c04003140c180c5904020000046104035a0841c003131034103103003134000ca40245a0403010003204010791083d00b4070000012056600d05480001d104c40c4451200c0b2403041c9104c401400e40d81405940441040c0341e401800019005d030b41607901209803540c0440c0c00c0c0c4103100d4003c04619100740180300552054480d01089041c40b00814540801510b1700254003030221003c4002910b1810007603518038001d0411907c242042da80c1148032811360b03401a0080c40c41700c11030a04420600c5214007818810706100c00042c2c00002038035a603a440c0e0a044002d03150031580c0301d010301d00303010312501c2c0580c08004482c106e0f40c0007005000d030460b0b03ea08102c6500c4008005890808050101051903072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 318996142 1250 318994892 318994901
    0x103201e0a02030d0623010f1e0c0506010e04080318010902041109040b060418050a1b0c0c0506091003020a020f07260d0504050d081c06050f030c031c0e0301 69
    0x3200c0c1c1c0003103490701380d5440000d0a40302e098000400d006e1038100d400c0300f03108846044500b482c00c2404c140d40d181d44010b50488103c1d00091910380701c00050031441c40c3c5603030013150010b0120701400540f000740c0e1300c403030b82032075059810343d07000b03002c072400b00000765645909801c00c41c018003c800001c690f06405400040c1504c80803640544c5403600024131000704d2615114203520054103030340c6141414500b8002e200406d007044550000581c076200010002c0ca201d6015054a041c1040c0c42d441d206520a001070070030032000d204030f504d0381c0d0811001c00c0307074034110f4240c03484620020301428844916190440c0a5000351b580401944920003405818000500244010b03204903140680700d040b4421450f02a0740c11051208940d0b000b0008101800e68808111001c1e5070099806207034900c00742c0303000b042070b1040011711045002d03c2607003441e4030802c1c1c0d001201156002c84250301010320b040105501c500c81001c441c2e506a0100a01c4070f03026455618040040a050418079000c15103000400d00b5107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 318997392 1250 318996142 318996157
    0x150e06070915030b01140d14100e01061d1e090c0d060b03060315060a030609061e02090f090a06050303030c0712020d080402210f07050406050103201e 66
    0x709482010300030400d01c8400341440000618050140d090100006403541c0c0c0200150040c0c0308000030a0000c00b400ca811007803650341c0d020170035101d5103003070400c40d1082915800340035031880a58000081c407901c5581491a00c0d66100d040b40115003039001045000d013007521010002048941107a09103688002038984125802035440341c2e00ca04640e03114003210b4294000e40000d000034070a0111540300096440e6110b1800000505d0701d803109000034a103016994070040165040c0540002008460340005000f034500c030030b0314110042d20100103003d81c0100000c1c3c9402c6016585070075035600d040b00c01d09801141e60b070301c000750311a01c80b80440c2c150350040342c0c03401c0342e2400001d0310001c00c81c074940003950b2070748a4806810f90302c0d5005030050810102901c080d01c202116181c141910550046e05030800075600100e0394015554808551581e1551013150720440c0342900024955000c1e002d0301c0002aa40f0350300b15204e1f080f0401d5842603400141c1800c10190b9514034454041408030001e0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 318998642 1250 318997392 318997397
    0xc110105090d030c021612050a0212010c090522050703060510020a170c0607030e15090109150219080a0b0a03081c02040506070605070c1e020108010819150e0607 71
    0x20900009000d42d00c02c001c1e00021540b044495000e070560742d94503101074070b43c40c3c7c10f101849240780c241b4030314243c152100031b0b41c0060980c001030103003a015030100840500f90b48800c0d60142e5910b0400c0b0f0040340020341c490501004110440a46a042d0300c030940c0603645042c00184951a0008103202854035842400540d00074040314051106448800e6030007039480c45154a414502009030703444800140521043c55200e2400d038040400510010313580c9006104030200d070b07191138082217000c1d286d108001e486000800c030b10300102c4040e60086070703840500c000301003102000c1000c0807240c9107401495000c005d03994950000f081d070307214030085004501030840640c56030b114951044c03a29030b910303158520003481040100800d17194102640c81c2c0507040387d40040e803659041c1c0240d8211f0741021000b849070328403040303103441c3c600750580c00c00c0c8140c001c2e80e40891981c1c80e0403c00355218140318a40c1d030b4600001c41400000342d01381d5805126284195000318160f00344001142c509481a5501001b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 318999892 1250 318998642 318998653
    0x30f04090501050d08090d03091d0717070912080c0a0303020912160303050703050714010f2301031103070b13050411120c0d090b01090504030f020706050a030c11010509 74
    0x301049025040c05441d045540d016000d44994a04039070f0b11403510064001e668000240d010b05004800303180051100c01d0b07014000c046c80d4001403c0440041702c4132004560308120303c040c440c401c2d40c181d0703104980360348402d00082d04202c40c22140b4401c4030303400c40f001e0340c0410112407061018400d107690310703102c0d1310056120a40f500402c418107200520700319031a8800d5041a00d80030900308514112509400d1503a5961058103003294144901035000c0c040c000d035422001030244055001c007010246900b0200140381c1d0307910a005140500c03070400030819262500600c0403e02c04102ea680010000f400c0f1080c00d60b0710381c09030b501034000c2c0c4040e00382107549440030071060405001d000011142520128989503e000740341240e40c001801300411180c01140c0b0810303441d0194400031100b6000000340c4482c0d0f81d141c2d1044080c102c221400c5000400201c50701984a00004995056074000d85a607818201c02c011700300c0040112141c620200302100314850307a80c017020300c102c0e4091b642c02d102802 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 319001142 1250 318999892 318999899
    0x5061318050c190312050f0a020f010c050702030c06160c0806010e0c07051504170c1e03070c12020105040906031401060b040501050406050d0605040507080405010b040902090f04050f030f04 83
    0x381440c0120407030300d0003802c521142100060202c04140c06907503010aa80c402d405c85010101d600d40101400c60120590002d62103c03001c0d00000d104841e500302e10020b212901c4540012a2180111400250941c0c40900a220b50b40351001c05459181e01c44400c2c04007010050b101c81c0a41400f5500146480d0000c0c8018410070366070160060303000d48042d0340702c0d00d004103da555650f14407840c2007900c00d45270744102107401c00c14032042421158030310089607511001754215007615a1840f14200c0c2410110b0012285280004401e0301c40300c41d045020b015005141c00541480703811118022410400100004120801c9601c1244080d40c0a800300c008000d002c10142400c46800341c100c2c00c0e5107801070204009982c0c0c04412501503442c1460065240d5806803100c0c0d000c0d0905421891f4401c0c01c0108002240740d01c080c0440c400d0713004100a011024484081c44200c038007001019401007034040000b001200c00d0101140c20a00c1076040781d900b0302e40200460b00710380150354100c0b040600001c040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 319002392 1250 319001142 319001153
    0x904090b0f0619031101110601090b030708070f05010c15020304060f05090a0209160302071502070201120606050708032205031b0f0304030b0c0f0406090609080a1505061318 76
    0x1540c40b07481070302c105400d440703400c59a0310100102e2100804070421408466a5a44500d45014040d4a07400c100c1c1d929584807081d000203000d5180a013400fa00c2030210000f2545c0300001c2c441c04603010130000ca12100d060100454010902643c1902c80c41c903038443c8604010803500c000c1d445180214800100040c5000e1744d00d00b659070152803003155034880312540c0301603541e4841a94000b8846500d81d4514902c841301540640034400300a000d0550012001c030303048619030010081d5501c00d81c0e0f00f04140107120389140c100c2d0704500403000020010300400000072105070056801920040c1d01c102d108500c0c2055031142008010211500c0d04045108901882420401241c02d6255409000b1500c2c0b8106060364a005a200190844441c03001003060b200201c0d040340c800002441c140c0782e6464440e60081c0c414001846244006101c289000170000c00c04100c20300079581c81021400310002c80d41c092030152a02401644c0e10410500d5002d400d24900e200f00d6030300d1070081d04c0400f400c65803810710 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 319003642 1250 319002392 319002421
    0x1822030f0f08041505180115050a0609060914010903020303030a0603170406120902010302040e09030a0f0806090a0c140a030e0105070e1005070615030f05250504020f0904090b 77
    0x1001c01d100b403040911002644000010340004049480040c1c0b40c1ea03207400c0c132240e0f0361045a9007001940781c80c0c101c08256640482c1e400a4403800d480800c411541e40301c003103d066800384210b03400038140030030038030007020442c801e486000c0051402411160326a00020b05541c0265a405545039450908100b0011504d007141451400c0409180c28a8501940a00356441140058000300d40e10f4005c1811a07000c3c0d4141c0c0c0140c40c04080c0100c05142c4800d000d9501c1e0300500004c0b000c50071003000744030303054412011107104000160122880342c4075801c842c400b8015882107070080c000031440444600c0d0b41c001c05888200c00d590350100340c0900381c100301401c503400030300b4080c00c0103000005030015880c0c150810f880c0c5410341c50200e070749070414207208008240115881400d50f00c50070f0b000080c80340b0107164070800c502500c1034920b00c520112058580c09850841000382590340b40e010003261030070340d003d00019022100524640000400040c044411046040303590350f04841c01d2041c4402060712 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 319004892 1250 319003642 319003667
    0x60c030f0c11031e0403080403230d14070203150c18063c0304080c15010501081f0e040501150e04080d020d0f09081b0c1822030f 57
    0x10040941c0caa030030701c1143c491055803000203260030301078100b1444c0300701c0000311030046400200e0592141d880b49460ba0400e4404c1204482d0f540030f0b640c0405c001c0a0104802c10341c0382c865200c1d500001c9803d054411132b500081000e81c0e041c0208031011407070039400e01c2c100d03224144111a140e50f0304105110703001c6151909103030314080d0600340540e80d21280408008200480040100c292001880440719003c50122104540008010040c03001300705c0000c0103044601860b1090340c8003114a6114500559024482c95001540320350100710560300000039100f142d031080c00164102a2a030b00754030103821091b80d04580580d510b10081c404204c0c0c0c0d030540000b41200e01d640d83d150341002c1c2c8516140340580b00044802c0c0b50b001403a104982c405501881c1c0e00000c0341c000380014003141c104000c0e50f81040d40d408401e52144100511303c00004035481c0345414000300400090269200c0c518051a00100301c2d489520303803240c800400000d60150410524404e0351031540c3e0200040c0002c01d4081c1401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 319006142 1250 319004892 319004897
    0x5060a051b0c06220c03060204210c05040b030114010b0a03050f01080a03030f091509110406030839030403060b04060b09010c030216180c110307030806060403060c030f0c 75
    0x1003034210b669004640b0f650000080208040c4e2900c05410f4680030703c09802d0000c005010b004800810000c00d42c001c1c0c0304880040808840c080b0724481d036000c0c91200c0d9040145122807002e000e104901d0554007a48000e44003500000303103440d1041e040001c4c62800e800031a02c00b074022450070131069140c06000e91150101e500500154900018607588460503a80141850380b0ba5103e1200e00c00d89074000126a501310b030814117214645554000201600103043e600450502100a10f508140c05000212644a4170807407800105070b00b5080461a014500d2240740111000f98081e1540c039803400b05004440c070301a640e59459443d1075400c03038641042c414021801d2060401181c404801980d014800a00700400f800102e8a0228200360b000d03c000c0c80880710150380402c041c113290146094101d0900c0c0c0400c540c8203480f106a4034506035101d006148c0c0d1042140a00191240c001c49170003507806400d0340e080c0f83d22aa542c40aa070b40e803090b003c5c00070755500c43c2007060324040c0c0100c1040880700d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 319007392 1250 319006142 319006147
    0x5031204060215091018030905030309030d030905030c071d01050103141311120a03080109021204021c0203030316021b030d050a05090a060f0f0302090a03060902030a05060a051b 78
    0x10003a407a4041880104a940f00941c00941d81060500200c0000ca5090b00304004003810103141202d0000050300503400629040000b0075213080000480b0300c0e04d44010014400030035200012000340800d000c00316071501040c482c84c12145010072009014006180c241c00500c3c3c8070904c41c000406c4164407090426080c80708640c0e0540007407000c2da4001801c00741c1e40c82901c0150801c80c1c60980c91100d95074000601d00040c110076800815820700c1d03d4070999403105d441c2d0780c41e11088180d001d001008015590060081001031519664042002c4011100412005420340000c0e0035500203c03a00b0500715604254000601c1d414040b10107003182112841c81007900002c0030030391700c01d0025912006d1110004c0c0c94400f0701d0103241917601e0800300520b421903154580d10018680ca80c040c0340e4a011071071030203400b00b10034043e0094a00c1c911020f401a0805403954030307220b02400e20324105a07054094001c3d40780100748103200044c07040a11610224450130f114584080304000540a40d030501820b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 319008642 1250 319007392 319007399
    0x71d010627050402250305131703031609030c090b0a06020d0c0b0901390503044d030f010b03030324030a0b0726040b0403030b0409080405031204 64
    0x162882107003a25030982d00184c4408802448402a4445492200701403522408140c01c1551190062070401030003291204e00540d50025400c5d000700766005d51a40b6081840024041040e0b003034162540e450a00d0005001d03a56519054440241030704070303030304a0b6101c6200080d5800c00307514039801401c1d548010310310f014030030780001d0032180d420200610b000144c901150f0b2130b00b4250403e01e016070b032040c400708030005c140c140302c070942062001c40103281001508203050140184181c0e48103d4005500d2000461000c120142d03800d8a5044030007444040b20f60121103c1c0006110f41848520400b04580c0355100c0c810149004440481c00e00c041e0b0400310803840d035440c040181d80c1c000d40c40c1018040039080005030040820450b50700550184a104110f800744400120060301400143d01d4040c405c045603201c0d20450441d50701c00309105035244000c1030002d002c0c0d035581c940c4103001c0d190002d40c40c2c41c1000080c040d10300300e12040c0d600c4000410144000c0c1380c180418a001c01094505507d0321f8035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 319009892 1250 319008642 319008707
    0xa020c030d080f2e0617010905060901030b0a14040303020912060c1204081b0709270311010f060b090a050603041e031e1d09010f1502071d0106 63
    0x1c001d0000c1c0e40b41311204103a4845140b0340801840b50603500e03090103101e6440c0c14008204101848261004809034800000da00704548542c6000f0500685162180ea0075920758140c2690302500e00d0342810f85e2107803180600154600c015001d58030a60700540e80da40391008004011107a024016200d130800014081098080000c131071005629000d000f000303580714100900c0502030001c2091201030b0302002c40c0914100450508141c031040541000300041d82c6d008600c076a0440030340e00c04190450a10500424081c1c0024619454101c1c0013090318440940f984054466640c80301001c0c03440841d000344640b40c11410b02000c0c0006945a80c02c5140944034403d03480203010700951007441d8442a030003818440c08200065080c243c0c0541c1c911080c12000905041d02009260205038a084071042a0316040351003e0403180b100c425516400d040ca4a5480320302440d4451078213502c60014002000a205070602c6d0200c0d401d070400303400c15071400c1c402034500d0594000a0701e11441c46140f1041202c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 319011142 1250 319009892 319009921
    0xe0609030d0f11040e060a0e061c1e050304320409031710050a050301020c060a0c0e04110a0905010f0503040f15090f050c04060e01031509080a020c030d08 68
    0x2944540c0225800d42460448401800c1c01c50b003c0d0300720040020003140004503400b0702402808155039070a159070342e8041b07011081c901900d0312580a5411100303201c1c0c400320841c2080e5014016682c003100f240d490f01a04402d092108030459480c1c201060402140c4140146140d941c400c88081011940103500f00404c15029200400c0c4940d0742d0310303840e80170301d4440c4140e040080c4c80190411286d042258009445501c43c0c03107070500c0750704c11300000301e030604060007600c0020310090014005921428100d01c0600311503010a03003001803084910f0b20564985c002c0c203003524680081d642d516107003040010800c044c942c2205051100c14000b49290681c8507040703d078410340002c40040c100c20246000d254441a2000c07900c02c050501c4d0b940e006100c0ba01e00000c2f1028441c1d0219002e01501a061009440301c510a20f03810410704d5004101003400e607a59042110724400c3c6c0003443c01c61550b11180c480c1c20041e01003005902c010356641260a0412a0f500e510a1038108040c25240c035451441180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 319012392 1250 319011142 319011157
    0xa03030c0f0c0b04080f19111b010804330b0405070c020312090d0f14100b0d110f060703091508010f0b1b010609020d1407082e0311040e060903 63
    0x2208001519188008088141c4000c80700c40f2210140307104600380020803489141030803101034040c1440c0c048903c141c2c01100c01a403081a16003412603560f944800e01c03926400c082482601030340d02c08400b07800d8510504c113703d15061100014188081c030f4288411920020040410311001208840c09aa00065030111900014001665803070303125021071010315900c1001040b03910505640b00400c000c4000c1c508040200c0030448600c0c441d00c9400d403050783c401e51b44243d003001c101030400c2c02103000030800c00c04840c8003500c884080081c82c004586168015071068000400600051008058018a11214822a1070042a80c0d410000c0030504040d07103109000b25000002a400105241c4d00500504510410020840715a4030300322100a54000c80200458615000440e409040c0c4035004a01038104d680c6d41d010503a442500183d0851490009408505654414904108080c801c0d400c06144a82108203030b03c040d440500040c0c41c44603090060fa90008820000daa100000c1640d00c0c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 319013642 1250 319012392 319012403
    0xa030b043003061404062103050f1b1902060a030902010e090106030614060c0712020105040b04060215070e0f100c08040e0414060403080103020105030c0c0a03030c0f0c0b04 76
    0x1001d2032002000020724003004140102903001c0c030030151160035511103c2110343c0812040300c02c840080c1004110341c6076002d0b9952044034a9400c0200d022024902c094041c401d0912614003000c90070000d849812130004030b60416492030550504001c103011425107907081000d03503103100c07441c1d6000441030b000316010704081503520054502560310500c030502130b6800c007038642c0c541942c442c6030041c081e003043e000f8000701c0304511000f5138080c10401d0403201c40d40c6a18018220050802c000601240011403080c0d0400c0402d100c00304541400170300420007402503800600180001010054052100808403c2030041071550007507203445070601400085022101c03042820742800043c4c981c00342400000e0f02200d00420003040070041291500c1c0240e01507012400070148c201d07035203a924007048070000d0028680303a00400c0154060f10145400410b1580307121f0420410018007481c240b421802030b00029210031184100d2a044021184114101e00d030131085140d09446001080e00c004d0402400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 319014892 1250 319013642 319013663
    0x14030105061e03070216060912060203060d05030d02030a0606090b090112020c070e090f011b0305091207061409010c05041701090210051207020c09012108270a030b04 73
    0x1901c2e140709050510760491226440303003861030700296292055902d944101c017020740c000c90072500442125040320302401c0401450000d5990340b0019400103414281c124016010810004209001a0505007403604005803607140500000e0251034440c1e00c42020300499420a02c986c034064030031a211100f080c00c045810350840c800b044005d22a40d500c88050380150240810b6943c0e043c07202078000c11304103003207845100080c13105900300c2c0e0084004003520741c003411740c0c201e44078000d4110a1b8800808000c0c1d51003103002c000114010f0707101d90404c0ba011030b501c0102e40030494003278520782e1300301a000e002000340e12000600500355102d14060031200000513407d4800504c0250090a0807690142c0501031840c42184050115004514044007084040300042e074050702c0000c503100c1841c401080903229921700707405443e03050080b128a0214020703400058003c034400718014010b40c1003208110384111410f54024800c0c1d40c1c4401c20500c104076900c020808141c034071340c041d600030340c001d040501c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 319016142 1250 319014892 319014907
    0x705090c0d0507090323060c0a0c12021006031103010c030b060d09060f0e01051602010b090103110409171c0501030804140a090c021006090903090603110904020d0605101403010506 79
    0x1c450401c1907000170b149200081c48089100c0b001200e806d02c4400600450302c1684500803050900e004a250420001c1d44031695903001c95400c0f034084019403c5401a201e814945e6400003040e40ca0755041a10007440100c01c408803820240b0440f09000350314541040141d0310304001980c40d21599158944154441c2c91280900c00158031503004000750000410104442d0200c5034040c0808032443d0627030b540d020042c1902c0ca070040c0503203601664010150f9016a017944d94181188114055981e00079503108840400101703145040c850304240c2e100130507148d00c04921107a603120110b100030450b807401c2100400000d03030305205031000d8869104c009010039584c6008603500030166800600c6480c1003a102114194010420142506501205112042c2c840ea105c80540d64065402000220200001c10590388241c3c80303e003800350750402e614502500c02d00050140d0304010b00e401503c503070f690820482440d00101c0ea031842c580700d00b4030007690900c0450b419024001481114061180001d040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 319017392 1250 319016142 319016147
    0x50909060106030b0102240103030e0d05100906090b040609020306160503150301021c090209150d1b23130e0a080906041d090642090906090705090c0d0507 68
    0x1060b07008400c9005400f146a1101147d20900080c8070a83c040340013200510b00600300010402a03c68101008000079140e034482d5038010588036500780d4031309a031081d40380c000610080c0210f008c1c07401800040b030200f181e80101400c144020380107028030002e031034003010300507004800c0c1c950002032655055121021003000c02c5c06445107000d03031521483c0003070070400c4400556116021640c002d03550341500782c0d204040340e03400007071810b12151b100003d0441180010860310300565850507028240c0c40c55541c5a504010039807449510601c0f150b000c04030620903080650081c09030644c0031a0a215424680c2049915507600e40741c054040791000450340c079161034007403c0380c004154982c0185c20302ca26104030510340310b0050b80c03a60141c1c0516008110001ea404000d081c0c0e80c041c1c0900e0003441c15a1100c5180300c41c40ca0440d2143d03520398948117102683d542a88180305910100160400d441c0c16403150b070074003a0f10f03041180300340d40100c1400000301d11501034504040308510001807586440005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 319018642 1250 319017392 319017403
    0xb0603011b0f0c1a160201050c07030522050406080a0b100303170c0c1204031203060e01120f0605070c0201020f061509150306091c032f0c060702070f050909060106030b0102 76
    0x1140060384c1d06906018603100650711001c41c04201c0c3d80200200d86900c101c0b144144650900a000143d05101d8501d503d05003070003d418011016034034400059032400400d054481983c04401c0c00d0300914046012301c0000e01da030f03543c021049168514a00c0c00d56502816020f46508100b40001704600003461460307001041340d01d8a00c025044070542031404820110341e6109010441e111140560040005802030241c907040d03561581e000c45240c0c0c01d080d5103aa03108d0490350281c6003079028a1504001c038146110b103500880c1107a0340c00e12004818000a480c104034003052200c15404401004000030a1403901001c00354200c84020740d03a1242c07184081400c028000b4280d041c05000c00307005144400244802d0701450790710440100f0101214107504549061445c601d0f503144c80b600d040c0101d0002031104107100358030007104d824210004002884c04e6401c03102540580d00c44013051007414032450090300100000c0722100c00130301c0c26100503501e842040c461041130544a980c0c120490b8000e016 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 319019892 1250 319018642 319018673
    0x20a050f13030c0801020a09090506010e06040905070305090a03140a17100312050c060103060e03070b0109060f0506090d141c020601150206041205030a0204030b01030b0603011b0f0c 80
    0xe035036445070462203400e2641d20351403000721840e002511001441803818001e8401030b0a040e12414003030ba203424102d002510008200707904106090680311415aa8007014102410300203000048626020308081c04942010f0030302516640403e190708000f0b1341c017030700c02a084591404415101c40c0c040109491521300c20702413110205586080105000c8c1080ea00e000f183d01481070806190040c0348155807601c15900703a41c0050700583c005101160701ca80020701d2031410a01140d1402c2c1e02d0392150b035040030f0281c00003051903456040803c802c06a44904038007400040311410302e40a42c540000340c00e450000305c01801c00316143c1c202e4100000030f0024030881d030806a01031804800c9501d000351111000d0195481030035005491003505403000071031070311555218040d407c1e5000d01090071f81d041c0d00010450880d0640812000c8005480840441d00952040e0180030507400c000081500791421042c503846035200940c0040e5800354040e800e0b00214580d810070b421400702c541032800780c1003001301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 319021142 1250 319019892 319019917
    0x90b04120c150507181409060d05010213030507061d01120e0717010f061208130f06090801230a020a02010902190302120304050d080a110a0302010c02070b040513020a05 74
    0x902010b021881a00554450309a035510508040c110790220030089000d80610803660480300710f00143c0d820010201504260010301c808003c80301030b131f240c1e42a40d02412001101880d001000c10800c003041140e10090000c605090b0381800d1990040806c581200c03580038108145c511007074540c00f1403588030302501004001030710703000c0317454041c21a04280100701085096180c0070b81d041a294030781c400c1d02c041d1454004000b004050a4840381070640100458958903040098009508107042d01000c0051200751680210a8540307034105e42111040b6540d4412090550300052030b0200884104e580001035400041c0c48409208049004061000d8025084148005030190800070890284101c82c400c80f0b01010100364104407580368041c0380b043c41d80161406291300c0c00212a24050646003215281c80030000540141107858681540000e80150350345814000c481a814088ac4001e4810098003524003441c00010940c841007d4880b085115400f28415514034420000c440001c000c05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 319022392 1250 319021142 319021163
    0x70c03020c010c0212010903260606030610050d0911130506010e130e0a150e0307031b0317070f1101061a031b210117030a030c022419090b04120c 64
    0x3d00d4060180e0003040e2910100384207010149c520818001d400d1441001c001d04803d007580c0b511024407070000503a518100078044148503e2200724000d07c140c0384820300480800790407002c03400611882420405550880e903003003400308800c4d80d1700156a1118038a0588150b00c0d0003081002e600d0060001686000690161880207000c0c404444107064000c0c81d6040100f00550542d08055a00d1107440ca00502190360b2580356500b9248081a1460032030081c141070456804044026141003012a0000040342114500041e0039512900710075514010000030000c3c0e0f4242107070203112400026540c4501c04000000541010100d0541454480c4040841d03460303035085550601c01103040c02503014010219000000c8081840300317400203610760440911300d85659802c0440280000401c603505500c28916480c85140042d84104420b0b10036000400d11406c1c49880740c0012448400d61660351030414100c540800d920082544d003142d40035614080e10002c0300301c00d54102606d100301600305c2141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 319023642 1250 319022392 319022411
    0x80f0102030901060e010302010c080702150d0906050603011509020304081e0c060a0207030e0d02121207030e06070b01061215030309031b08120d020c07150206070c03020c010c021201 80
    0x540107140103086100c02402126260b4000f05070034582480040d0025140ca8941d00c089200b0200902c40140040c2410303000e1809101100311560009015402483e03907100302c8800d120440c894070350071003002c070002e001c0c3d80c2a4405494007040c59004910780543d000011408000194045401400c40401c804422001440912541c3d4101c031501310041e024980000d0b0b20302a403442211140c941c540c540340d01410070301007840400302840070101d800a03548102c881810740b041144100d0074211107640ca5031000d041c54000c010303240050303d5030701800d01486484005046101214150783c1c491500780202c3c4940100100034040646040d400c1d12011b00000c001e16610607090000d903406006003440c5070040c60b5200340e01110920611002e50003011182c410500004001d05424040100142c00c01505074205418004940d0125007241685034200e00115018084070358800c002d42091004024192006900c480c1098402c604000e84c4855030310841d078070210420b0b00c820a5038003c0192881 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 319024892 1250 319023642 319023673
    0x1508030316020316080c1f1e090b0718120305071109150906010e090a06080c0102030c03070b180604060c0816091e030b0c12060406050f0909010608 65
    0x1038801e460040801200c500c1d01c64000000c0790b6000c2d8025040da035590103282c0b80d204141e006440354901e0f078003809414846c00c031004002450380e107004c03c0c0000b4130340e12040c0d06488407841c2c41140d40c4506040c040154080307400c1c90140c55010915041c40c40c0c10305035a010004581c0c0302c507045514040c003030407d44006c4c541d101307020f4040284101c102482100c11002001079003281107a90114412046240443d03d0030a040c0164100c4010b060008030151524001008140c003283c10041c00ba59880e07080007415002c21803502094001e00180d840c0c41076002850f0b071a8860380501402c2c103800100402d038100011f59072031106943c0d813800d07030380ba5050600e80b01015281820410300055802c5022400c501d2400254445071131550b00d810119500c0c060a21680200400300140b2607482080c4c0000894500364041d42b01d4074000340d26030361710850460742c01d1b07110402900c103d0195245ca0300a2003c2e4441c08180321007400304594086443d52040451405800d41d034004141178050b00034900340004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 319026142 1250 319024892 319024897
    0x51902010e090105100c230f07090902060301030605060d08070305031008030a021e1c080a0c051c0209041104080d09050409080f0703090312050909090f060712150803 73
    0x24401d036035014048190004001d507001c02030213040d07800702d200c1d41071a1909008400384100303244204c044000f02d0440c60724403000c480c80e144000c005c540240b42d01801510341441000c01921890104010800058000c00c3d902d0105000007000940d0b290040f410342d5444200c0c6000700740d03204070020703503482d5286001080d40d041540c004600c40313000d55010401e9280482a43e141c02c080b03a00030000b4003076103290b0380201031840038550240d0058280c01042e8640711600420542d0007504c0e6070b841402c115065004690402c040c1504008090242d02e00030075488042201c07050041401507250340d04900060002e01c117058000040b98000600014042d40208401c4c1c032645103a15141078403a9940140811303101840c10080886008202da0301c4050108005046014003d151800321303180c07139599003520071401030903080114901041c01400c1d450074441c0541d010712a600a8071b044801e03180090f6032a0701c0908240e05101c1c81c080002e90880c0c081d0301034244256181c1d84504480c2d03440003140d8036175 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 319027392 1250 319026142 319026193
    0x91e05100c12080420151306080f090a12021009060501080f0c0604090c1202040801141303090501260c0702040b240d14090d02160303050d0e070305 65
    0x140149100c070907450240c600f86104940058059648881c10007034000c8440c6107032201070f031008564a941c14107203207104c0075010510244d8500a061410010003620305040100b0804090084808200e104400800c2c45280301358400740302480880d840c40d06a017001e101801c90b207403c0c1c0ca00350f0741d0818000c2c2500100d04864030303401554000964226441d448540e0307509450f4009004001c100901340141e40450350805a5161012002104200602c203a03031095000504903074442c0350003015042030100d5150800c8c004007400720341e040b00b641e010b05168141d11656050002d0304007038688070460b040c3d4003040e803039510007606018682044244c40301d80281c9004e90040b8034001c00d010450400c40c0800c403113110132006da003a0784030700706d420100300740e00406903950016103d240946204480c031f0040b90044014401400c60350004400082c034220848018070301c21181c0c0c40b01080400d401104850300002c0c4044046107155007851a60714000403a40000d20512070510003d08461400ba201c01c1d50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 319028642 1250 319027392 319027403
    0x915150c01021c201804091a1b030708040312021b060916080a141002181914040e01112a0c060f03040212160501140a091e05100c 57
    0x111807802c0e03642e0003032a0300042d41450520b02088440c501704442e000c0344107011001840851346102640da4244400c403401a00d0321007442c40000d1041103c14a1000003001e050204201c1c02c41c649400d00811035880904080c0600000c400c2900024566804403140d2001885016010803158490690380d4602100d40d03010a0054412030140380b03411076907060444201c000107190110b0b194941d85d485101c03144103801148502403034010f030000f217400505540414030110b00307a000720380020b0041011542c40001c4915030350070f206009143c00c02c5d02052400009950000301c003054080101d005102d8441a005c0b400c001181c0c5a02000640d0b0007941c012180400714101c12081c00032507030366030a1403100260f01c003500b0b1000d10440c0c0c448501441e031040c001001031001e010f0307404000e810440784100030b4035490310ba990184180e50b040303944c2d010700c03901550249103080060140200140081c2c06101c43c143d00d83d904641704405124940400b4140041c0f55910005c04981e02418021000310b04452 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 319029892 1250 319028642 319028651
    0x318010b03070b0912030d0908040303200d03180203060c04051c0b1302060702180711070302090c1c050108100e0102030f0103080f0c07080307020f0915150c01021c 72
    0x150601182c0c0c00c0c12034044120090601060008205108031006905d40140c842403180c0103145049004020303c07140940c2c41c1c15a582e085081c0280842d5001801201041045024504506000400784005001c908d40007400d00c13501d625100000e9060381b0042d6040c41914284480c00181000500464404540f18142596038801c60074004212100103405086480001140307022045032905410344020102c4e0320b040010790000781401d030005e0f2100c090704084d0042104550b001035032004940380c1000104209461503000a170182c0008218154180300403800746402102d0f000d110300101d01c0054180001d68440e014281d07a200d450310b800c3c941740d05124008884203030610881e030052819801d612010380c250380f1015020b5004104ca070103036003402c00403010f00500c01e0009401520140c005940c2d0360419004000038410302c1941d030b1f481008250b081c0410742641c285140c0c130b654005c0e03450326041e090405441003580603030065124554000500780d05841e1445038a0216101c041c80c0420 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 319031142 1250 319029892 319029911
    0x120b0603210307030f022502040c031119030b030d0804290a05041401020c06100b091804111c0b0108030a0e12190c030b06010509010c1401060b031801 66
    0xc01103203244500c00c0901c1c0d02000407510161103a00802070301249448094503180d0300360940300e440e004058180d213000510742c0000e402c601c1c00340241c000c481141e150a000c000c442d81002e508501c02c180a445000140301a6407407418082e400609580500030191488124401070103002c0318803c860469648114400212208056140c00042006c5c880c01c07890706a680c46449200501010384155a568009440461503c500740000d01c0b18000c0b082c09884181440b8840001c0c14000d6080038420000602800b505070300c5032200e11040085076003d019440d251800d0540d54501d00901140e0400010b04203500181c01c0380c025054180c0c851801c4100c02c2e039850006030b4490054000580c001601e2034805461490a003400030b202003003030b03c1600c004511026010b0143c0116400c221400503180c00c0030810300265402c203a40c0118282091860a4220000282614a00035008000030041710044806000075403002001d001c0c41d118041d582d00301041000c2e521318032130a84c901158203007030051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 319032392 1250 319031142 319031173
    0x1205070b030f06040c0207050312181c020904030c0204050f0420031207050f07060f0f030501030b01090e031903020910020f0d0c031107030303060303030b2e020304120b0603 76
    0x1ea20034899455001c580b40c8889040102408400c1150802c600c81c000d400310386a034040c0140868840015a81c0c3c4e9950300310460842000450150380d071150400d02c9031000480940c00300c82d484d01e07034101c1c5c52507a165a10314041e114031103a404060741040c0382c4410424252030050245c0e00450040a01d440d84100c480040038035201002c8005405070000340d2843c1a06031850060600e06100b4010b654880150205184c6400150f40c80140041c0309a9001498260480b00c0140005001d21b42408030f0340c15921149220390040c401d19818950351825400100c1d014000e4554290001c030404c4100b200010000b00650840d0900c2ea105003801d043c042202c0e03000040e000c07024003122003d020b005120540540d84404084000c0d02400f044550b8405180d0090040c000a148692000109242503081c000e085620b602c106500500c1400c000650654101500083c8010300711080c074010500e05804038114052640a00c1d00500e0000a50040109285107248525801c0e0704a450815006c60030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 319033642 1250 319032392 319032397
    0x50c070b0333240c010c0f021b01050307030609020c01061707030b0f07091a040305240402100302040503010c03021e34080a0201091a1e040f020a1205070b 68
    0x2001a0000c6420303205107030342422080c3d09602841204181035502c08550103803c181c0c01925a07581d05e03590790b0300401d07020703821148080514115100030004007485201c8644606000c1c4402c1e410302102200040004d4442d402503405030145107010764845018010071400f0345081d00400401120301408401000400941441200d410190580d0262074010116190701c5014010f4400c02643c55000f144d07055140405112100d181c10300d007580c40b4a903050103414034203070140c81000c03102c00b804801c01000302c0940c45a00141c04a030084501a1610002c0c0c000388030b590301c92900743d403d0000049205415a000e0148526a00a015202c1c008c4010355612407040d007914080b080f0303003000780c03080140c0d01c1010007036940d03080310f0b49840c03070fa030303141c40d1080c054000f801d00740010303911105000e040244855048650b0058540400344509100c3c50b01000782206585603119801c4200010702804402c400481c100e40d0054085500c003602c41b0380000e2500201a403c0d01c2c00c1c403642200107000c0543d8801c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 319034892 1250 319033642 319033711
    0x91101090527180703050a060c030b0a0e0901090605010b0406030b0607080a050318060f090f0d23091507020a0f05062703100b010e060301180b01050c070b03 69
    0x100801102e00001455500c89409031001c00c0c141c189900c450302c40d550400803500514050b000030034808480d440e00c0d406664a45200074201030400c586551141c55403da0f44040d5466560740345038554034214441c0c01080c0380e040181c07540341041e00004201e4601e10080003036900e2a50244009481001807014a125000d40182001003c10150f405c542c89071000c2e40d00b01e00200c4e07480c40074210340100303289890002d41c0c28000348440f04e0280100203000308000c100030300f42d1038083c00040180180c060420110001c14071034900c1c00c0702c0c850318440717444400c4503000b10000340060303040c0d5030221307010110340c02c0b0034800c03030147e20310f01404580f1701489401c120440e140200b0492810311503080554050806007080b210748551410490a150750501c003995610b003102a00140342c0032801d0004001c40483e030005801a8003c2005000701008400e600b440891070010100d40c008a610048800348144489060940a00c003004902c0c011400c0c015070141d600c407291385200100031034200c002c1d81d1f030115 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 319036142 1250 319034892 319034929
    0xa0503060912090a080307050601140907020c090a090b011203080708010b0313030938090102100b030c03030f070c06030608100903050f0d0501050a1202090123040911010905 76
    0x30010003501418030083c652844044c28480c0121713a60340c0081d155800c105000c03201d43d0040c80060012034100030090140184c00c8460100c5424140c0b0040e445141456446004450b418001400400c40342c1104e807d0079031240007070401d0f40c2d5410015040d100030f42002c070000790300761012a450b10720841c8203d0603507580131a13091071512000000204000054400c8007484443c107000150b1b95036250300c10410a143c10080d01141404034170404c00070700c0c0d03003003c0c8107807500c28032030701140d03980c0055840b141c02c021103400a00c0101200010780780c036020802141d8144800030300500702500c1078000e031500c10f03c181d11002d681a103070281034060301c40034000d200380e99006403c20f262940c0b03580c01950496000e400c004e4982030305042040490f80c0329240134065036882d8001005942402c08080004110b03800341202190382c40d5000440c644818405d04944150035a1030100c409440004000c145200400400110324203180c0003111141403420980414008000019a03061505280d403a076203c60 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 319037392 1250 319036142 319036153
    0x215040e0f091f051602013806070f11030114190f0e0c030c0d1112010b030a060f14070f050f07021302120117030405060309101a0a05030609 62
    0x7400030740d900e51000340121020302c906541d580b00b11040f00280c0004141007000403c0030b2618121001d112040004204216803500710664030112400a07610b10452071000300c40350304640c0010b036000e1005442401d5902c40390002d9040200081013400d10083c511030103042c0b0f10a500181090300321903008004c0004010b0f403200154200007109003030410860760000c0007401e1980030301400203d88030b0342d0080840303078040c0315003210307174030b820400108281400c5481030402003c954070380b0360010b4072001c0103010318404501004000d07000e4000401c01080178003250714449050400d000036099000403213000b00e240c8241c403074928000c919494410001078641914240c84204c044a59921100d603050150009211040c0165190b01e090f081542a01c0f501503202c42c41e0600080b050001070340940c11800201034a142e03a42004400c0d80e0031184215150340d01d950f5070152503801d101107013020250076481e258000248010542c1154416901503078503048141d210028180c0e0f58005994400c1d030350b03006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 319038642 1250 319037392 319037401
    0x50108040204020d0e070611031e0702221406030604030804030f0315091406030303010303020714040f0f0606020609150a0e0c12060a20031b040b0a0305040215040e 72
    0x168182541241c80603100502d41222042800c0848031403580b030000301e0304010010400740d9071002041010388910b502035072405540001c1d0f0405c545040d552036008600200300c0700d0a42d518501c821080b24003032120030328200c644074402d000402220034070a8041c0310010214809044c0051030a02c6154152034201d05e83d140c5842c1500c44440c4050035804250f02c0d040c000701050300e0851640c00409104c0c9011400c014039404260440a00400107406a40140010804aa40020300004503140c2d6054400d17601507410105d0003410201c400300e20010b0a250152aa0407810350005044801607400c2c4c1d09640c58004085032110500700074405c0c8015050082210201e103584051800541c44084501c43d11700c400c0802d4080e6540e000e8040381d90442c2041040d026554061a012028004840318007581c00301c001c000e1900002d4035100365007070f40342004084604c3c0901110042c0058601858032600315090003005400c04550880c000c1d0b41614451402444050a46042d555036000c001066600d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 319039892 1250 319038642 319038647
    0x103020f1e21030a0225050609010c06060b040e0f09010504050a0602030c1603050d0b0f13020c01090614091902090408090f03030c03040618050307060c05010209041805060915071805030d0c0c0b03040b010501 91
    0x70202c1c15102e054dc2d07144005098808e0310002c000904104001580701d1820380c60200002000030085000e6905010410000440120303502d41104d5006000513225105c1d0000270601d80960070740903945c031b000801820185070308003010744484200040240140c50559061019880c003055010390040108900c105183c0703a2600540b002821100000030000010b450f80002e035501c0010b0b143c41c80c00c814041c090360603400d000031b00355a140d9042a80301500030780e000c6851000000d0010f411042c000ca03603422036680b5010140c100c0880201240d40310720862940c50707280e40c0139102c2d50780403c444850542c110049108698100c80c8020068001079240c0002901c41880044003242e20755401c000c0712502e942d41b48a480d2960440718003140034a00705e8030b040c616004d00903100088980c400b600c40b40302407008600c840e41c0008142b84c0031401150040300440344103c1a0001e561500424900307200c1980d010f00c85000207406888880e040a50706ca00003001c034802030710040c10445446005014a50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 319041142 1250 319039892 319039907
    0x12052a0a0e0402040605120c0403030c0b070c050a0506010801140c070b0c0409061203030b010c02030c1212310311041104030204140103020f1e21030a022505060901 72
    0x980c2400e0600507011101d00060890744550006800b20b036010500c521441c20b0644415031040040030094901801c54070040e024460504005040e030f6503e50004044502c120100b06c5100c0d401400c817040004249042a100d540900950b045907103461407613102d800030408414043c4d45080f021074a0080b65440342c1d2240030009115802d088401c000000d5802c038248507800c02001c0e42c9004080945051900070705607902d000d5601e04100006030008003681d40403d4a0070b000c2000c860050201d0307001081c40d130815900c9569540a07420210314071811040007a112418680044d400800c0e680170b92003e07881c485801c3c00041e1180c08282d0200c091420075901048519603500407650401d50389500060969200741e0038500c10b480940010011401d009040c480382c048110381003001080ca4400ca8101c1071031307440175580705100c80c2c2c420f80380c03e00c40110395541c9403031080d050781d0366404031802c040d654005070000c00c24080440301480001001c03200a20040e80c500400562600403010011180103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 319042392 1250 319041142 319041157
    0x302010507091409091e150a02090f100306050301110c12210903040314010c021506033003010e010f050604060e0103020706060b0301140a14090f0a09021012052a 71
    0x1445030100040a4103c000c070b100c0392480800f4000d10b035401c7c48104440304035801900a520007401480042d17490b5079012410b86801e030040e030720361255901c849803c0b8083d04143e4000c5805510306420b449110b41000028001548500d040703032540903101d6054102c0f0700c104080303c408841c4000c45107500d49100000345800505030400c40303003080e843ea01c50000501e08085401d085d41c0d0342d5600385603500c4e010b10a0380200540842d00701945e14040001ca0f455001101c540086020048540c103410740c40c020b5810141c011007403041e510ba60310341c0c1d4803902c0a01e0031b00072140f081825101c0007489191940445040e01e038242d5800c800100380100540194114110880d1440d48991001c1b4101d1310315006103000301104c2040861560b0000d080c0007210440b0342103126050b418484140b41798843c042102d4010340045115417440c1ea580280200402480c01c00950200745102c0c1160440d80c016842804007024420030005600d5110041d46206001c0320324201d0404888120030740d40c030340741c0041c2081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 319043642 1250 319042392 319042411
    0x120403030615080a0e071401050a020109170304150e101a030f03030709091406012f060406051806060f06040906080102070c0b03070e1c050303130302010507091409 72
    0x85988071070701002010b5031401e00c480011003078800c2000841941c0038201d0740c400c006014100140c10800030318050b80e51040d11a041c0500010300c800307914400d60102c5400f80d00808015242c1c0a080031270409a4429101520030b1007a5010a850000c4d50748500e50072031b80408024840803440c0721600001c4d2550900030398500981c0300340941161424007400c04003004140103542c0da0b00c0c1015000e4111740c0c45810507050030385002c88084914810b29000f50b0001e4090030103401780105200d2000520390410704500040000c40f89182d40c011001a01c030340158482c240038032541d5a00280c18000704a05414840503900c484081146410300344c0d81084010300241c00b061805449040c80b034141c0d50035504c40031190f0760004200c018040ea03c8140000361070b24100140c60b604113424002e1040740c001007401e106804071170b83c10352640b5a16a8003103800c3d5011095940368a0403107006062032034941d0050380076500748800079440501c9014040c0030f1301c81210100710015000700500429000c000c001880 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 319044892 1250 319043642 319043651
    0x370303110a03091e020d080309160807031a0c07030e010e040c02061815071412010305030a0909060b07060b030a0f0c061d0907050703020a0b1801060b030c12040303 72
    0x195140d1110080c440840240c8020481c11507624045000900480050103100e903014a9140142d85441404a80c642c000144a03141d0b00c50407000b0b401c0c01c15103003c011100000490000e1030034030100300641102e0140306540071088900b8942c6a84850440d0340f920006010030801c80000d0242070180c240d0141131500050501d180b0020030110380c80b00309142c026038040001c01802078081c10f102d202e07400c1c00b907010346480180c04800001c11000980140c041c00700303c95402d00301032010000c6d1104841e0180340070846580d82e00300305413aa0312002da03040000d40e0700180496005802c3c022a0116810321542602d40401a01e1b1400142144000c03242d05000d00490740e00818561040101540c0c0280c500403011494800040c000000313905038249111108455549150b865020716588080b443c18400d5441d05513180890500780500401031050441c41c00380154603c510320411525208280200b0449840f01c0752200070b03002c11900070f96081010040e81283d200382e90340b0590014405e083c08107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 319046142 1250 319044892 319044911
    0x106060f1206052812110d080c1b0301150506090d03050d09121106090d0f0203071b0f0e09070302041e0216020414041203050712050a0b03370303 64
    0x41304002d00310b000554481c102414141d01180c0406010f00500d4500c100c4500c0b1320180d69222644219806071921400401c0306071702c244841c490440e40070f020301c4d10a0320008800080c080300500010702400307000c1e6207084540c040c9200d504203e803040c1d42000304032504004007041049408854210104e003040802e001042084819020320301142c1d01c24400064011a4800001c000c7d0040e0310300e020184c1d0101c01803140741c19002c2032600d030206e42c0d443c02d242808071990381a450361003501c10044c59000100c01c1c82c0c0035500e00161340802d030f9500800c2c550005940d5114002c004030142c0d4448440c1e0407002c0100014074081d030200400c0a000c0150444c603c54441c440001c03a0402422018440541d10006045141510580240c106c900da05075805041c6a121900c0c3c4017010211a018155100b002c141071a009030710000321a060704100344018504203107540d002e80440400c0600a22880741d0002103a6881e05080c50026100c1081882051240340041c803074015100c4c041c2e0500d03a5a03280c82 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 319047392 1250 319046142 319046149
    0x60a0b0a0e13050103050d052d0c03070507061b0302060c07050f031c0f090519061d0715030c0503240a0b03060a0f0b0904020304050f1f060501020106060f120605 71
    0x1c2d06844100d20001103961544c201541090240b14122041000c10080508582d160020003400ea101015840c514410198500d0300c0c180320303d1200c450f40d4400401d101080150025020040d103410340d450000c41300100c03040e0514100c0d1036100030f0150b04024001202e01c01003202a000301d601500864401c0301d840711300300f800e542c0407000c55452000d12101800c940c400c0e0313018606c0c0c080b070102030400c80c96840f03494180e125004140001c03552a2505414002e01c00a0b811207802d000d03452007003a41d0081c10341078290303844c41c82d841100f40a480815010810078028410791902804c1511400c4c07440da40c8841c2800200b42000070070304034009080400311191244035203c00604030520a407641d80c1010b50070818036110691000d501062020400c0c401c40070080b00fa01c690b40c0c810381d03003d61251510314006007040f1101410b061288101c5104c40d0503009804501c001a1744070343c03010000c0a450307400480c00d84120740990000310740810840301c1c1c02841007011613031100c286600080c4007920789000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 319048642 1250 319047392 319047409
    0x1104090c11120a090312030e01050a0c031401050108010302060706093206070f05090a030f080a0807030506030307171e0d11070f060e030c010f1401050306060a0b0a0e 73
    0xc20300044501d581c040015100700054211504802d45071420f01d0285040140420400d0000901d45808400301c0e441d000c4c000c0d00f00f5290f055140009121510b492a040401450300c8001c00d40020b00304411400c03042441d9008a0503072700c060b0758582c0c0503821502070101c182d0090204850940e07581c6641d0f008181e2300001200080d0f4845441280420078012108102440d07031819011500440e040c00301058026090b803100c1c52035800d109031600c8012002905107501944050500407910340c1e00c03400c0041c0301d40209541d05460300c1d01c1d515510340e00c0381241216021200c494259108014400c0440c109280302029031107040c1040341352840c5c1001d0010003940c2600c031540c924001042403e0003050724002d0108001d103a003c59418607031075480702c031148003480f00c000e404c850307031070703036100e1246800b4070131110030942e090000e0010b031f1841c0030340400522002180310304598071a000403034146000310f0a180503180003003908415600704083e034a0150f01070300000c030500c02480c00c003000c0c5840d072801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 319049892 1250 319048642 319048661
    0x250602030907050a06030507021b010e0901090606110304060905010c061d0c0a090e0616021c0e04060f06020a030305060a05100314012108070503040b0f0910030b030a0204110409 78
    0x1500c000b524041c1840003041c5190443d038281401c000405c440958006880d0941070802c1602c0300000c11404016100b900c0b0420425801c0420000040751595035900a0320841d00c0650b0341c1e101c5150400d43e840d80324040d42c094000040d410710800c210a6102c0d03102c41c10480c0c0284000a010102d4004562425041d510080410740140100c440345250403454180208201002070154010750b40125465540041081c400f0070460b2144400d210720810100c2d50112001d9000c5ca0740c4031181601405080c0c121416038440d45c240b05000c41c40620440d0b540d0103c90321034000700403045840c0d80660290400918583d008002c403040015030f5952410302c0d1520007929140050f0404052034011800e0205800c9018003c0e0304070b4888400e102c400306140c00f800e4001e04110707103030f04031841e0035401d40c440c0303500c901501e120211f080c051042c041c1004003085001151850b03c030b0b1059a105809031200354190740d5040d000000e15401504250300103820007001d402d079180ca00780d22000c4400846e000b001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 319051142 1250 319049892 319049911
    0x60305040515091f06080717011107020d02010507020d080406050c070f0609030818031218040b1315080109030309050f120f2a0c0f0904050325060203 66
    0xe12080c41414846000300712002503007640940341c03420005a944100036103103071040140050038210a000381d8026400382c0100c07019614440e03603d00b410404010280100c14203546000301c15040c0000302821106820307806084050800620303001074525400c007103001ea81001e524044e40300081e6008000300044c05264591648400211a001e072408219812404050a2160701803060f290465040812280d20407501581c0f4142c0944400c944004507419540600c51070300200310030b00f8000041c0c0f107408485004020f00c800074204002c1901d055810041e045201505011403610700350f04401000c01d4400c0000c001596141c400d98215424060141c0000c0d50b610024400c00009101c3c4030300c82041d2400604c005094004e00c104944500c010030074615200003228509040145a5607140700c40400c019070344a0f0000e140c0d191a400000d1209204100e080100f030858644850140d00441c0c11400440c1003407507160420814081d140c5249103030415450700c0c000091054001076101d0f40515 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 319052392 1250 319051142 319051151
    0x30a021b030a06050a020d1a060909190908092d0402090f0613030b0f0c0a03090327060f0f0509040e0a020a03060209040506100206070c110a2603070206030a0221010603 74
    0x1c5024004482c0343c0882300c840310f0000519a80301e5910801586e05040c1c08899040b102d8441c050291900c092030f20600007428104610f02c410b01101304050182c0348826110b03d0007040c0101d60342c01c1e40042c152840307145110415070b0b10080d81000e03800391840c600060b24aa000660a1002440540060b070b40322150801c5c0070360500c100078000d800c49400081180e11400c180c10281310010b040d001e0615448105503640c1c01da28203161203408412a1a096080185082c5d8002c50031030806480b54021907001c11080800844554800c000c2500d00b5556507881a080540c4c01082001504050000d99058030a211103440987e40c4c801072400203621078280141c2c0d070307800c2c3d6007844140d4200074000380c0f04103078072010b003100301c3e802051059100d50ba0385041c40301e200c51807400c0200c440151301e801790020001340000c104510300300c2c1d1280c80d5455540d108503010601900150b80c034400c6d000000d401050600c0410b02000c61134014004102a4280000460786c100c004e41d440d0b03403401d03400400003a484 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 319053642 1250 319052392 319052407
    0xf05040303020627190c050103050603060708090703200a17031e0c0313060305061e22020a0f031104080a080a020705150d15051e01020f06130212030a021b030a06050a02 74
    0x2950741031b000300400e00b0144264a4500c00094070b03024000c0c02c0200740180f190014a04800a10103000555402000130500045600360b080440d03840d0707100a4020184c6030400f08214040403600340782080f0b040000e614080016002c5044694020809071150384280b10880e4424424000b030540075030f09500124800d8a4950000c080d47c00140c41c19000c7c1c4040740c0a03622100759060320080d12031081c1c40c00f002c0103c607580007084002d0b0705a480d1030b81c248085804142961320000e103410540541e60207109502d00281c1480d5248560f01c00c0c04072a5021408200018440c040584065880390055881440c2c6d10008500c14041c010b855511300240010701c102d11311020301c01c52480c1c50342100030000990400000c1190681c40544444041900c1d228040d001e80c403c101c040c5523801c441050ba03001c2c0c00c0008617001e41241c4035000301d202d00042c41c0b000001c0c1c080007040d51030f03d2510350300508000300103181c1403040d0548200043e1b0107018a90303000303000c100c05004050140500302401a510307202d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 319054892 1250 319053642 319053653
    0x303040b0106180515120a150f05090619030506040503040333050a090609050c010f1803030806010c061d28060f0608070b04060f0504030302062719 65
    0xc160007540c20300409000c2d001c2030001d03929546050b124203844201107501000300b8014580500848001c039081d0400400c4a0a0020f4000b0342d50380c898802c074a50095126080e071681103403a4024940c001c0c520700001011441c100d000152424500300070080641d4076510303a2408c5c668229000e4505500000f020000c0000607501036003044c0090b90200205016002d4007102d1511030700c40c580c2d6460311140865030074081a4090356405a2042c020403900d0700a15003192a0146007901601103160350261001c528010824240181c0550b10290580c5003950303002d441c0c2900242601c0d0400007580107040000b1203d1207012071a000304180f80d1042102d1414243c50103030000900ca11200501c80902d120800300300c03030044005d5120340b0101c0c010038040c2032080203004036403243c0344512918000003820350b0420014000e80707030240c2d07900620180010040c2d500384120f100c0100103078130140008100a078030b99a401c4c200c3d00144940f001c0e0030901c520640c60140980300000b50401480444000c021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 319056142 1250 319054892 319054913
    0x30a0b12011a181f050616060b01090501050f030a060b030411040605030f070b09150703180902030f01050108090a051023011d07090801060b0702010e0d08040501030e011d030304 78
    0x3004940304500c500f4008607212880f40301070001020310800791040c0b4503050001200601504018144540b01c880c40c800caa0a402c8101805a03a0b29241001da43d0703032944100d50070306c1a03035410f0b101c5a103040c102c00d25414069000070540f98420b40c0d10072010810a0362000194015070103031400b40c0203132182a00b008101c2c1e03119401030f440f990190141020050000c1141421111456145516034525001142c4551740c000d28400801600203615010150442030700b0b9800360210031401c03016500d03400c42c90224401590070742501c0015000410266204020480d4804010026a820b01080f42c0d2a203241007002c410102110703403039400323400c0c2215107101c9041c800325130119400025454140f201413428240303e4600345400c0341c0000101b18500916681c002400d0400081010701e55800034188079400a0700120300080c0c000010809a1500348040528150040e011500d0549018010740060611040304002d035503d6100b40000000c0b00008200f640781580003440e030f24501740c0ba0a20080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 319057392 1250 319056142 319056191
    0x70b04080d08160f110601060c1406040f120302132c04080307141b100509010209030d08060a050409230a0b010b0304020105071b2405070602030a0b1201 67
    0x111141c100f00c140100040f03840c2c070030031440c00d000d8800c1d007500e5400c503910b8800c0a042c1080b07129000000034811360005910005034014030302c44040440481c0d800d91960700903a0003404100d480340044002c0b0b0300c0440c143c981154182001458196564003990500503d9842000c40b050001211045c074421300d940c4001010114110030311900c0c09a82c7d0010380e01000e08103908110110a0b03900108400504071080000c80160601d10b005846001d190703607054488140030081c2c106000b14010b00f00500130f440d00b01c9401005800c2444842004940c0b0001c000c0031554417025415001400e6120340c45054003060280000c5032094001c0012123030000201004011150302c11503c00780820ba420301d0542c150b484c00405a07030340f070300c590004907018040c0800140a4070b40d050b130f00f10b01d400c448030f2400084070681e601401540030000744280c5d6220442c2460341c00b00d0f83c20000e080000e419070703004507401011540c00040e4270043c0c1c8042809001180c140020350b07959401402e8099185c03a43c0e01c0e018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 319058642 1250 319057392 319057397
    0xd0e01020d050702210705060d0903030b12060a0e0304121b050a0b0a0c11090a2f1206060d050c130905060a120f0618060e01020a05071211070b04080d 66
    0x40c076203e40d002ca5801c403a0710300038014841c810a0210118441489004002c140c0184090307160321000c84100c000b000d4003042100824900002c026241c107000c50a00441c1c10300300b02400003603895044a41c05002039059510703890104000201384503244607000c9a40c2401018010304856210030849051042504110f118100c1c0c41c80030000281c146040395601c07442460821041e4000745009402881032074a0b06a100c6503200c108112003146900060141e14240781c12340d00b21500b044034003402c030701600204004400070000704441c51504148a6006140035200e070340340a12004100f0b003210310030780345c03d6104100000d003500105020032001c800b801f03a41900308514182400010308a0940f446684c000c0a040240700c824000407030307140c03405540c100c1c0c2c06026a400c0400f10004488059400301c956628102034071090510500c2541c031460300c90740340c252800c041a194902d00000c600c81040c100800044141c0c10f907417082c820b440050400113151038481d4103020405041c00c0c4e809002004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 319059892 1250 319058642 319058647
    0x906010e2823030307030c1b030b07030b090c03061005040807032103020a0c060903030e01050c030117190b06030a14060106140304021e0406080a0b0403020717070302090c04080d0e01020d05 83
    0x42c1c994000c01202c030b019902d404c01c0e48000e556440c0c400e8082e0040781151f510034610701000003d10542210681c800c0030155410001f02c80c40b01c081108490042d04d58544004061001414904082c0c0144030307038080d0313400c1450a26a4546d0b038503181c0b5403160802c541404689100b141c100c1a80a0b64042c0c15900b0f06042d800c1c009421750041100e050f0345000303072410b500c658003007091501940c0072000d9401c10400070f00582c50495408441e944c0288a00006000e4401c0707071049a01d8041407074069081e41540a00e441001900c542c1d60201005c0e020030382c9805000211000540c01710744403000021500042c00b40e03985403d5020341080e00381020a40d12010030010040141d640710301094581420f241109118044803000c103000b00740ea03812200d050701c1228040000d00640080300e51080e486603013100e60b11601c459003202e905c2d1403000f40c1c80d45036112240a0005142040c41c00b41e02001c800e060f181850380d683c2c14503280c1200c460706240030500c40001c001c4c01e564103002c1c8110418445c01c0407407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 319061142 1250 319059892 319059959
    0x81c05060a0b07110604031407050307050a2913030c05030d030515040c0201110c0c130606051b0309040c0c050615030c130605040203040b1602010b0906010e28 70
    0x55240f0400600418a1100e01880c19140c1d9420f82580c0107150800e08028032815208401903844e400740c001d03544280315801d4001694640141c1c2e1009071802c102e1441d0a0703c071034100e800c04030000300456200e001c400340008440c0e0210405013900840c06080152842d925200c149030410b031315102044105030404c0b04100c481c4540b00d002005004050b100059807445820b4100e00400d400e490503500281c001031011048000050700031b003000c0044036520074031144080003500315030181c820b420208605119604194421313554001c0800c101405503440c20040d01c0009007180c074000303090004a20024140012f1007070400c582540032020607074042c01c4940c4240085e44d16140d40b802c04c1c1c4250760900031043c3c101c903c0d40015000303120242040d500d0b81020310309070103c040b0485114000b91a04044d40044900c14002c83c0030054001d4851961030f1500c000440d4545010700c0319581100d20420300b040514200001d0225072500f010503a02004d00f490001c01303c1e440b03003c9500c00d41c084c20700c2085 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 319062392 1250 319061142 319061159
    0x40e07031e080a080402120601080c01030b03030711061602040906061e060206010b0c030d02030106020f160f030327080327030c04021b060405010c1220031003081c05060a 75
    0x15080140c05003010406035171503200003a000d00030f00004203540e000ba5000091044800034101e64034038426241400781c546224180741e501c0c0507100c2d0140540c0702c16404180c041c20f28a00802140010070b20720380e0700c1d4200f6004581900c0304010f040741c04075a80d03903081151a507140c0d4400650011841420211072500c078009640d0801805500c03040500041c24990300013041044480c88801000d00307649960351079a000e510303111100030350221070141d0b840c1c003d041444205e8200c10b0360200d45000398500d041d924125480010b00140d01c0d080032161007a10385070b810020011004091480085590f0082280c2e25195100041d004074401e0100c51072140b02d50b9004030b149100008207031401602c0c0c58803200d4151950556441d0800c050103104280401e110064002c400380c0c5006032a1411a4a82001302d501194001050000b4003201e521810b4400c089090041d0b4010a03804605410f00740ca03600c0d15002f80d0b10201041a1469071500100d61180380c0f40642070b40000100d40c4203444030701e810400d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 319063642 1250 319062392 319062397
    0x1e0c210604080901020a0501060f1a0a0f0c08040302220621060e0a0218040c0f0b070201271d0c030603060c0304020418060c03050a060b040501050711040e07031e08 72
    0xc0c00d000c004a0f180c8410f901c200304000003070b5008002882100c0e03907a03081d0160300703403d80141d011130042c19030350303001c9000501e08031010031100d507541601040b01c200c02210070340040700048558440811001025a503800d001d001a071300d40c4c40940448e05aa5121340781207403000c0d07000180c0910f2000400d000c24080c100060302054000b540030544060700c107210f03800c02c440c500009510020084070190803030709810b6078600c1948614074030003d490f103070210651060b01903c1050301107501001103d0044d4070403030307080505524070601c03050202d107110300e11041203006410140460348400d405950323000b9008980b81e004101015010f10b135041c000086511000002c04207692100000040f408545903540304e00800540920508000c0b6403d144c0000500440d080c01c00c0000e0515000c21003483c114800c640c00c40c0c2d0b00072482032500340360400641d00e90304500802d0707460902d42800503209413214001c80c0080380c140000340a18506500d44034600d4090540c0c5840001d542c7c036910030000b5400c404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 319064748 1106 319063642 319063651
    0x1030305070611070f1101030912030e0c06030603031b10020703081e06010503160302040803041e080303060a1202130c031b0528021e0c2106 62
    0x607000400d004084018000d4041803070301e01c0001c6e0000b80306800340c090604007c0b8120b5602d843d1a41d1415030381000781b0100e0740b100c05003030381000d00340001e01d2041002c03910a81182810004a5624014060710b108a510030003446203080c5400c0001a2550903c0c040555035040c0d103140040202601f9501900d4603105850344140070040d140b015845007a06075038190955036042003840c8841c00c007020103000d059080001045000b8140000c2c00a4148201030315201c207100c00d25114961744a5001d03030415001402404000d546540010040701c1c40c51182e803100c07122600008070300f031000e4001224035600d4003904d140c40540503003080000000c0061074543c1350a0003403080c0c07124410540380d5004c00114040c4410300c103020040c1d10140203028030441fa044911750100b0001460340001c00d50a40c1d112440407411490b0503042d04442c158041041a1000000d060b40b503034030340000c0c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 318884892 319064748 := by
  have h0 := BRFrame.cov_init 318884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 318884892 ≤ n) (h2 : n < 319064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
