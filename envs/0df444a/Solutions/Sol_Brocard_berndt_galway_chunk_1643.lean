-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1643
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:01:30.776808+00:00
-- url     : https://prove2.me/submissions/acf810bc-7329-43fd-85ad-029f39d09693

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 295323741 ≤ n < 295503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 295324991 1250 295323741 295323773
    0x30e1509030c1c0f090b070213060e010801020d140103050a140307150501090f0e061f080102040605030402090702060103020619030e0f0f0c03031c020304030921140a0f 74
    0x11109010300d042c9414208107041099185254140041980040280010050925410510004040038041d00010805884001d501162480072444101084000410b110b401103084200c004001041c007000540080981c0c0c00c0005d07081081c03080b03108407440f18881c00c3c0801040d61700000e02e04004500f00e009080c81e8004800c05a070b150290a64480012096100304c1d040126100c50041021081d0351003403e814481e10402070002c40e0316841419143c5c01c00528144142d4121201004485c44404026000e0150207000319034642d240c3d85c0281c4035400448040f441681d9050009880c98404030700309040f0395001d0031590802c1d0008030800e00f0401ca00228000709070340c484404c00c0140d000c202d009842011000a0703c11615902030b0340381072002c1d4001c1c2d28001d600822802858a06415250a031015560b80c0141c0325221860111041582c550201b04c100b4912004a95074010354521541543c0c030560880b41c46d09100c40003140c40c0c42c0107550141c081d03901c0409040100d110300e21808294 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 295326241 1250 295324991 295324993
    0x150f190f061d0105030c0f070303091203090c05130213090603110d0b070c031e08040605090c0109050409031418030c090c09040515031e0607020a0c06120f0609020703080601030e1509 80
    0x4030710721020003621f940000c002070780042d0715104030205000e00f841c2003595411252030240b02c0780c03200340ca078080300a010b4450280502503180c903404c3c0910455064440034006108441e000c2c0b640c4e00603101c05403240f40016214410502c88180403840c0c145190100554440720044041d82e408c00140c03140e40304100c0940034000c480c1d203200d2000e90144505845921191215500c60802d42000e030100c0314000d0801116a000e0a0000c0745680c1014080707007195012140880c0400007490221610301c0b03a03200b5643ca44801143d9001c2c044081c1072441c0746000705504507802e0040d90020840c044805407807200100204100303004040c1029000203900c0702c2031083d034106c58810480881e1034042c01809245e0032540e40d4415090980b03003400059001909031000740b206555a0b1a100b607404154401c3c4424440e0307101e0313412a42200d41d000400c114552010421500340d0f0786d10410041d52208034124001459000010030b5980a8442d0551511001e0010200f0300b130044402e083e624005046c10300e003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 295327491 1250 295326241 295326247
    0xe07151b0f0308070215011406160b0910110a0c0213060b1c0b0307030201171b0304030504050111061b09030f0f010903080f01050306150f190f061d0105030c 69
    0x1c1030525100200c86440307079840e55002e142c1030380000c0c2000c40140e8159400e44403540104010442e143c176034a000c10080f07441302d540d1a10204000f4095408210003040607008008100412502113600015152400c505001c007a000b802c003113400b8821203040720042800141030401505291808812410080c440003404c5030319003504070006d401c501d16941642000324aa0500c1480a0150000c8414190000c0c8246070841d40040d01261018045150210881000611000c03440840c088100740c140e045580e0390400d0f0500038800d6001c6c2c090a4089070b21381400a44071400042e03c94803c1004410010828038981510f00303055010308082c941c10311440d00946200c9200303000d43c201c1210841c6c000954002d41e480c0c00b0b015048010701c484421103400d80100f100b500e0101d091603000029603410f2180004c0321000640020305c6212082c1c0000c80544480c007400700e4011210240d8501950b81280c103569410300712031904000c0b84d010240c5a0009880741654002c0003d10307003007152401c410382 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 295328741 1250 295327491 295327493
    0x11030f0a0f0f0f2f0a0c0b0106020c0a06230f0c01020409020706060e1519030b0703050109110705030708070302150a1b050c1b060906120a0e07151b 65
    0x41503818590b04051050b07503c10140d60003618a00c5250341e18140c0c9808464110100c10b0040010642400c142c0c2c0080e80c000380107495a4840c3e9040300c0500c0d8030a00740d141c00c0d40c595600940d00c0e0a18000c96001e00c031a20000f01d981c0e4004c4450441400e803e40c4c00340f0341c01040108a4206402284a11420910520942c040c0d14401c0c0081d02c05004105001a200c15580c201601501d446610203288403000400713001d1245000085d241200a050f140460080c4031500700e0240100b140c0e1025040702901818400301d50b43c107400407412075146607801d20203c0124208900c031480b550708000e0050303004100e00d50010b0518005004054001d0050b21060300f200c0c081c0d030038104000c039400c680c0590b88510202e510000c0d01e5070809803a0035850110b0030003482c29840d994640003003113410801d0700801c001211644c0c1300710848800040c06840540c41309000c1000000e00b0f181a11030313404184c02d081400001103000200c0f82e0841d8041051500b00c94070041c000d03640000e00e10140040c0126940e4600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 295329991 1250 295328741 295328771
    0x280f050f0f01052413151517060907090e0a06050301020a0f1701050d022e050423090f15100c03030c08040c061103070b04050c1311030f0a 61
    0x41140841c41c0041041d103001c500d10020008080080314915400c10540500754440d44030b9039840c100d92010028903c1c0d801121684045016804a401e00c100d03540c016450640c03104075521072954900e071150803900c4240c2000401a411100f141c0021007c0b50100f206940d800c2401d81c2082128400055150300d4001103403c5e0791180300e0f045c0118a02c40c81400107280e20414800c1400300110095055506000005142d81c3e50004064801d071452440f81c0c80c030f00c90b41c9201030300a031a40000c450b414400d40c4005080343e00240300f4100b52040c444031084101d1803050304044400c4000f00045115601d82c2901a826007001c0c0c18280916604452420151158071030f131b0010f00003580b80c40c014421b1900d1b0003030a403482340f11120100030b200e0040c000000c80d09035416050741c03414100152891241c80c007981c0f550140d070602500c007003454010700062000101e1042d00104040c1e842c815901c000c0c0c0314140c00d8412a407911110000c0410002d13005982d0542d4094002281000c04200303540d0500c041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 295331241 1250 295329991 295330003
    0x1b03091703070c06080f06040903021006240908060604020c2404120c0c060509030a020a0902042c07200318130908040306090201170405070305280f050f 67
    0x5400c6681c400100c250a0001e0107880c28014aa0b0741342003071003868070003a03003080108090182e41c065600d640015080500a006282c2502d0301c814040024035501c0b82041a030b5003141000800104141c5101c8060310311403041d010954803240e008201588a640074000258000c5000134100d005984540f090480e60711440009a07580301241162810301781000044940c1a482090a202156481c100011141301d994400c5460344e08000303440381100d0001c1307820030700611070023548801c200801080c00d031642c1d070240c000c0d0b0700703280b601e0b02c0080400d4604581c0d4070039845804e4290b01c00d400c0019503851281c0e00d40007840e00304a6124401401c14000f040c41d5800048101d8141c0010114103902d03824101c6a100b07081c607100c0024080303948991916041e0303100c2e83c040a00082c0d1102e0558056900404100c0c0343e00c1c0156040c1c0595103450f08180c1c2e15030445001c1114540544104010003440304000800b4400e00c0401c60b1024400c2507071454002a800381c0110352500880e40c40140f104005e0040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 295332491 1250 295331241 295331279
    0x408030606090909060601020c0a0e06130615030905060c070c03111c140f1c030b120d09080106050901140f010309200307080706050405060a0c150209011209031b0309 73
    0x300301700d080040c00039003064420003006014082c0c4403001c001440b01040c2403904928180c0f1a030840030841032000303014001682052480700904040c02083c958164130004516015105035181500c4007045c1c2040741c802c00e04c1c060201490301c0c0051000c13840c00320f408003840000400c650121451041482e0328003804101c196010803c460f01424001c0c000c3c01700b12240000c10020381245002d055103620f626807003d00713240400d5a50242e00c002900d07022010848001407000712015240c906000401d1007641e402010701950a0210008840c1000c0704154140d070070003064082e00210803410f0188082100c030300e0504050701c2d003582c000071401040c0801e410700d486280403c2d21075410f5051500e80a030300e07408480c042c0d01948041040c942d1140c01d0700d0030b8075070032944180c1e581c84810046407041d0130a44090952079440d0b028400541c1c90f94005c06030701c10207880303a109640c1144041d04c01c441d2843d5015011070700d24415160f0500b0f105810064061090070030310301140c3c68031611a007000c2401d003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 295333741 1250 295332491 295332493
    0x21006120203010c1e0302070201020c0306040605100e0412031a0910090e06150d02031f06050f100801050603070c0b0406061a070c030f02040912120c03090302060408030606090909 79
    0x11109508080c004c003500644182070400724000342d1040b01d2810036104018404166011641608580c0b080c8620322290700010100c45242c00c11307080000c014036058070703104001d0b030200703800164000c5c00c00e0a0714841c0d074100c0c20280c0c0458241000f500580503000d034201b000c180340a0450040e41d190103000c1d00503010300046617400e030300749459501224100b03490030240780c0c082020404030b0345020090114019058400036070600103840800d250007451421545120302d070102c40c6c4500d90075540404100c480c11641900c0641c400740910181c0e240000045000542c1c0b040140020304001d8025500300c51107291100e4008880c0d01c50400411056a040781c2003078503038004000340311696410f810f030b017861038245e03600c5e1404556910091103030501c00108840d80ca4031038007080d0f60781d6602086496400c41c2d0f6182e4280c01c0f40d41b005012010300040751202d14a400100941c1e18441c0c4a041a6140c1c1500240290713100c989138540c0702d4000904466001000300440c04103501e0f5046040c1c0604c10000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 295334991 1250 295333741 295333769
    0x1908030712020a1d03010204030c051c08070f020301060e010510230a050702130b0d030c05010216052b09060c020d020315011d0402011b060f1b121515021006 69
    0x454030040180313911115a100382c0c011311040c404100000b00150448108540520344500c0c3d540c924a042c1d481e901d0050714181000c04c0c040f0500ca88005407401680c4210002c000b01038030350900c044114020300a40d0b411041c803040c640e020b9802800d41c0211112a0f005202c0d400ca12100d036110554080e200800c00500302007101800c504003c2608000f00072103550074043c281d264801b01e49014140f01c4040d042006034034240e828480e0a604940900c1c113008008017048410b800d04540e928001030070340640a028006c8010120781c6154200c428000d80c1c1d441107103076442e00008840804c50003900741d80c00100c47c0d50010040c1c0c0c00300040c13000840fa41c910707414250316211a28641c102c401c0300c8000b10a80590030000140e81c014070314150a8412130046402d82c0840c11302000606980f0309800840c2c0c42c05244000c00d045000207000c40e04065502c030700c00810682114000d4405401202002c86443e1006000840341c1d6011b02d0141e0290b44101c402d50f075058440c010503505598082e08214601e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 295336241 1250 295334991 295335017
    0x20a0215130f060e060f1c050f09010504050c0d1a0106090806010f030302030406050a05120906010810060e152409100804020a0b0c010230091908030712020a 69
    0x1681d00c0010415203450510407443e1850280458001e00d4603c0d129040005240081000381d03001c0d510026200b501c2c1180452900c15aa4002c11003940e420700f0981c0410b0014140040501132280708580c000c000e04101300001c2c0034002203c03052502210004000784594118050030f80035280280510b565030000709240240b010b0801030f060f00400c0821a082c1c5003400400d40000c00c803012692245040e50340e43c200349004031101d016000e8501d0001c0304400a00644050004941741a030351030340700b50746100d44248401002c41318584070300b24a41015500007403000101584001800d03001600c1542c959544001070316581074042e080c0702c140c10020600d2001810480b10500200c0c030181081036460802d07070002a11000203105a00d01e10400166510120360290155000440300d485a038600c140a0303585c4080320300e85aa2428800c444003c00100c3d901800222880d20300c41d024101c40d8030444640702e003080c0d43d10043c000414050380d1082145070700d460b840100300088503a500e040c01942d01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 295337491 1250 295336241 295336267
    0x3010905210c03070b0a110d140601050405031b0f061201060905010c1113110412021203161719020c0306010807061d0f0913060b040207080306010f020a0215 69
    0x703a4042040404050240d0006841e0000460f550180c01840c4408143d650002860240c1024030b0000c22180d004182803c15400c640c2041d582c00d00b200d45900d80560b991001141d1038000e52159540c194003606c295400206001c14031828010050000100214550701084065002c0e1061300c2c11001000c00401c4003036030045010020700000d2821f000120324649500600320f0f500c0d01c06522440b11100ca0669802c440d5104400903904490801d40701c5556101300f180c001c5202009a020341000d07042d82c000343c5004821111030868221011008200750386403d140d0b0102000d80307900a01d820002d000c1402c0c1c228200e180089070742e500401c100f107618018142000c1042e4802c2d000d5500c5139401744402a040b00b08030301400c1603a9554144540c140e000180c500180d641c2194101e1504401d10030140300d101515031055004400c113228403080b070030a100880c411584003170100340d801d20109040750321403106208462050b2040744c4a00030300360005201d54491081c3d240000500182c41098140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 295338741 1250 295337491 295337533
    0x16060617060a0c0801140f1f08060d02030a150b0d060204030302010c030b01021c030f0606020c01021509100b030a05011109011209050316033608010b0a1a070203010905 74
    0xc000c0c50300748040488060044c1540c03106006242c2c52400048111000340c0358945d221301407400060800c4500000c03901000c2000c035030103000e08005000f5600048d01814603078440c2110070703030150052103105940e480d100f0740000c0788610110042d0b141c01038140940e03985031600f40c99600a101c0181d64a1441c0350203400c46403444581002e00d401c0122005690ba008503803103003000381c0c3c1c00002c10602d00e41a002c400a1086c1e1901260301854800d0200e8016400100302e81007600c00e03000c0f62481c0c1840340d101d42c1225403c5403007400035805141c0040101c2000c0d0442d0746800e901504483e05032100c1e42e40c0e942075843c202e144050030f94001c100400e06691120400007542c243d00713000c000e6103a003601d9060f102c0c4a0aa11001da000485c4c08000800d071207206103035400c003444681e01c1c1690140c0d14188000c202520030504180422100100b032204040c4a12410604c0040900504034a04914071800e03040100414180a80511903000582c80a000380804c552181c0003410780000c0c03611100c11002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 295339991 1250 295338741 295338751
    0xa1b060506090a200d0b0d120807020a05030405010507020a0e090615040b0307050913020d0506040c0f0e041506080102071b06080603100e010902061c0501091b051606061706 76
    0x1030b04080d000500d100c200c003440301c003078804e41620542d144c0c2c40d5603408020f44003541406d030708814a01d01203170600c90826403122810072160340b016115124681c08076034803600424054141d8004000800c000e6001c1c3d801085c14610280c1a202c01c159220301c080074800b0200d4408441d034000d802044000401d0040c501a00c1c141124100300713003070314a400700341d9442c0540202030044402c40c000c5040307c204c0c80740c1034481d581e0050400040310001d14285854280503034045517003014944010508030105841c40080d188003502805450355540c0354261441c109510030818140c2d0380001050303008080c0001c01001c1d006140043c40b000c0c58280c2e5428080311036001700100050716060040039500441c244801b09a400c1c0c000c0744103a48800400e005044600c4000d5100200040e940d05881c10340787d445041039038010301001160707078407403642080d122080810304610010340c91714003401c1d01801c0a040c0010b094410554502c0065841c0811501644c0110180d03008802540080e02d00c1003040503484 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 295341241 1250 295339991 295340011
    0x6020106060504120218090714060403020f01080a0e070b04030203070b04080604080c0102090306072a0201080a02070c0506030a0905100c1d0f0301140105040b0d0c03080a1b06050609 80
    0xc1440e010006000f40030324040d245040503c0102c2e40190350b80c1150399014804182162a20307818007110360345d0740706543d1055045c089602c0003205c40038507011003510304480e006401e07101180303d01c000440f00c0b660000c007241303034290750342e4140c440c0210104402d102130320280f400c41b0750f00ea003140101482c0850f141d0010038030300d204000600080c1c102141c00782d0050b6205161980381c200c8078a5090290060080b241e41610032103041100a9600c40081d100204c0c1114440100c0e198881c0d050300302d4007860b00040d020912100200e40e100c1c400f540100b50090081c44403044207a01c8400081040d4800d81d005840c094551813800d05011080c000400ca203003401c4020480441ea50902400b501d404103003411251a032100c15030308903150b00105c61803120f070041c002c005100c0d5070b00010180301c40030301501d0701507850140481c000d400e002005204854100d21940100c2d45141e46001c41e40e407060100e0390410000c12901651078890083d181e59071807203007001081c1e9103400810700092181c01403103c100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 295342491 1250 295341241 295341251
    0x6080720010e370302030d02030c2106090402060a09090504050a0302011b020715030b0d0609140c01020303130302010b0916020d2a0503090d050321160c020a05090718060201 76
    0x403605095071440d03c00100d90302a41c480555003000c0e4211300030112966901400007041105401c1c00740014540101c06450141182d00800c050010703070002140ca9a40000404002c2409450080d02804448580b40703001c0380703101c0d22601c95a05a9005607401c8510354800c00f400e41c01c158082c054004440100f403442081850b600e24025594040c40c80349280003070a02401e000c85034400c2c2c001d00c01c442030140400d20300880c1031410b00020310007404140c3e51034034022207500002c200401c0070222381c40168001e42c06d5807140c0002d103a200c2102c078400c406542d603401c1000207640b542910280702d090350340e80c04420120f2984000c2e0030a40c0d4040358104105001100b0410600100788400044032032001c442400055440c06500c0c500c00c0041250384207540300881001c0080010090282c054a501c5074280440c0104c1e000c44088426100c004020302c2d0782c400c069035a44900c064209150004041c5240142d44001040c82c240058070b01100203a608400707421541480800c2e040203040510003040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 295343741 1250 295342491 295342543
    0x3090f0a020a17012d060e0112080d0e0f030c2b0f09081b01030b0402040e0c0304050712030905040b01020703240e10090506010e01030c06080720010e 66
    0x4030601181c0224800c8941041203102c420394254040490981040c4a41c065451520801040c5c40f1030700703160481c464188000414080340d00c00d950360484042c18459481801c444c1d68101c6c40d0b0b000462094406075803609106840740003000501d0103000d02c48065665202d42203003035828124150701420321100c1c203d144142c0c101c1a44d002c81c50861151502e840321884094040311442c1141d4450041c0c0c0c032440f80c0e95007945880c0c10400b6198070090b242001040d550030309010070f034000c520640600120040c0000e605600b420300455009104500303545c1e0703003900c4500f490540e0043c3c20054002510301d12041c4640d062521420f00030040900080c00c04503d1541c48c2014091049080240341c41d07041810060383c0302c180c0001400208000c2035402040018121500811072018241c0701e034800c0c0310000940004001030035041eaa0084090350203181420001d40b02520042d203000d00b049039401503080040c3c0d50326050304c0c80194000000c1045040001c6040c50300940c6aa00001651180b00b241c1e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 295344991 1250 295343741 295343749
    0x1080a050601050d0903110d090f06081324050c0304020a0e060d03120b0603160201060614040b130e040c05090105121506030a02060304120807090b0901140c07090203090f0a02 77
    0x1e07400c0701080c0e40811744c142c0d645011201645e40100c861400d100d1401800c0b119070b0064007150a03503078400b030315160030390b40c500e002c40b070340c00040e54400340455108141002103550300345034079a40c001410040c0f51107400060244111441280c0f00c021141c4040244011854081d18200041c644009a0134036814480005000b48104400042c140145110218207048140e0060030400a00419554480c9049840f51125842d200e0102006519101020a181c1d001c1c0c02d2080c0015000c103003242c20f00d810050051044e5128010404e0500341c003201c00a0200754081c0018891845807800c524280d20304400e01041001c10f8009034850084900e481280070300000311520703622540080115591a094042824640d0011020b034200b0000410041172150380c00007036042203c81c0ea58500159203c0c80121000e01960150f010030b03003810402d0407125031048030300350f02d40041414498a44041c1c0594649003154640c007280706541c0100800c100c1c950140411b14091a4610241c450a9100c2e4001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 295346241 1250 295344991 295344997
    0x80103030912030e090402130609020c010c03050f0403050a0e12103c09021c110f090a020901030b1309020f04060e01060c080c0d0c050c03011a0d02040b06031501080a05060105 77
    0xa18000da17820750014007995a175420501d06c0c0980c1a030200082e40e2100441d0f400303940180080b210540c00c108503074406038441e101c2c1d507204d00e035441082c0300b45071101c1e5400c585980c800c0500300100005025410b41c40d07923541c4010820200321b68014a00419858456802d445003c41d06125402d103203d18004045040c0080c00c40010710418043c49412110703120780000c00ea6844041d400c000c1101c0502d0540206424a141e514015950200104840b034200000c240c6c403643d41c29040803070b21340401c40351501600500711240050601140150401c03001c41c1c0620083d1004c4440c203511040c011b003e600b0502b5030501c2085064405109050500c5042c0d0034408040c42440108a040130000041c001407109482c2ea606940080c2c1e401c540034003400030081c0c80b21070405e48107030260290600c05482d0520031600e44002c0704002c0803c041c460020800d05600c40b070300503600503448004001c1b85a54550046102e0f803030703001c0c88015445a11000419120000304084445458075043c451941c1c0c0000c1a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 295347491 1250 295346241 295346267
    0x207060f0c0203120703030b031b1503070201090b070f030b0405012405040306090506010e090d020c0108070905032a0a0305070306021623010e0a0209150114030708010303091203 78
    0x412181d8807031610200e440c005040100800004020520300d081682c55009070803a078100714100c6102806456040d14074a400604403648100707191601919008882d0146038400c4036400001201c0c42c0f603444400c4070f100100c0c4d802d8000358142c540700c0301e8a030701403080628030341c0151001c005542c10010480d4081e4a1881451031840003074101d803150a12550071280910b601c60024820030176140303840350391000c081c0214050402d804c800940680c40000702070401c80090750091040408010065070100b60291480003009400203011550b0303102001902d410300305061480c050004d40c02d0350401103c0301ca8034003d215859480e000c1006c16400a100c1c6c0030f40c0e03001480160784000324000d44c04100b1000400410400410f46407106041c4444602581000d110009005c00785201c0300703c944520301a60029441643c03080810702d11000c5225040d0f050b038040c105080e0200c690300b804050b580007141d58400165000f0f00620405a1201e4284003e1031141c0080080080560300036024000c5424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 295348741 1250 295347491 295347497
    0xb0604090503040f09020a080f070503060d060f020c0307170a020703240f051005010302040b0d0f09050109050f1002120c16080301260d0e061b150403030c0207060f 72
    0x4141814040140304440c0101341c48081852040d130303110400350203508940b0256002c41c010301d00050420309020340c440c0c40751f44550f4481b0b10b142d980d03030100b00000702c40605c19181703d0b80d00c540c1c5110913400703480148800c07403030b4100540c0c4a1465181003000215071080d6400350f80310a00c86520398903000195842a40d6024000c0b49142240e54070440d40000d026800c9101d1a040c54804659004580d004a000d4164641d842d20003589440040d42640320f039200c3c80b0284841040070080840c9207900c4032140c46800000420429507545809003540c0342440213440c20f41200c031070304070800810484018458144202541044121204203000c1c0300001d001300111380c800110040044491070131a440c0d00ea00100494a03075844d00c61442020850035030441131500d01c604074502c0f84e2000100004650825510031000b41803650900c0b055400980400c094983c40c0d030200c42c000340b418464501c207081c0c03e5881c0040d614080c00d006060700c0c41e06100c09c065403c002000e1010070f903c4007440c03e407070649007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 295349991 1250 295348741 295348751
    0x801060b191b08070506091f1104050a03050f1507080a0518060a0203070f0e06072a0306020706110705061611150a0605010203030114010810050d0b0a0c020a0b0604 72
    0x1d1001e5410314000c407218500d10101001080c20452018041c26006010304126045a03a4010900340c3d0740b40850710b40b03100e0685c0034400c0c01c07030001e45401945000403455074032420944d84101140e01c00849400440f0550017901c0b05031a1403504000c050202c50035a035400d0441e0615000180c43d181d400351040907400d44840004451101c4d80701051001045001100c82c58a040c00c040300c000d401c29940000040c0b041410780b01d400d88034043c10600310758000c2002c2d03d40301250742c0d256086030640d41d003400a2880c001a00c01c4426603596100d000354042c3c10050380ea5031552820704212806102030051189080c0280c3c000715800103540740e8401003551201800e0b07088000d040d5015901100e0421442c4124422428900d011004141c0902d07603406e010b10000381c0307171300041e038990009004030700038072040503240c0001c1d40c411454181c001c094440072403549030301c440104590709041c90302910074204c0c180a0202d107549138400c403454510188050401c0c4d091035034880400705406000c05100329152 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 295351241 1250 295349991 295350037
    0x5150c0d050c0f120403020607020c0109090f11041d070903050a060c020f03041e090c080a090809040e06100503120706320103050d1b02040915020318070801060b 71
    0x202c046a8035000e0780340c86684c80b196003c006142490381210114018015480441c11981c00000c0c41248603d05840342c049aa08004500b4003e1101c0990002400d448a0317800001d060078400030400703030004200f6403030390f50540380402c0c0d60528041c00c180d081004c80d42c020404584c000c68001c8480794000004141c8840c02c1a04a15008038490035405ca80030010340025013138907181c00c0442c03514003a800c00d10740c5036440350800129541030105a02041078600040c0199410340e2150703045c02d110303912107402d116854003c0b4045450541617580d0550020050141d0b910700362500b20010031089000300712503101840d10340418003400750300801c00c036156000340003000070300000c02d003900007000484668102c0c0c2425003c940e140a03c010343d602d000e208510103196100d803581260303e00740074003140030311003070b40c3d007031100504900303e0503200720000d10b44000c0c101d03100e400114002d00740e114031042d0403000f85810600380086540004516890310b02e0420480303042006a40b14103000000440514603a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 295352491 1250 295351241 295351261
    0xb220e01050609120a2a0803070b04020d030c0c090204093e1207021c03020403030207050d05100f0e0106050d020a120807050d1d0103050613150506031305150c0d05 72
    0x840700018200100400006d203081a11202c0000d42c039a00403404810aa40c0d20086490b445070010207031210f00d013800080c0c0941081240c5101c401e2180c50402030300301245d201e465221040b500940401500014101f00a28180c0510410181407143ca581016480c200c1030100211303010b400040205006d14050500c42000c099844069100780039181c94034005c81c00a4603000941102000851301c0d40110f0b207901e22078802d8400752541900140b0540b4240410400e0b8900c0d0342c1c1007129544295154483e002e0480d014814020012580124a0394441d044050a41c1c0190f0080c6003c3c0003102c8080c800342e51180a154121090481c2d9080c4103851414202e50502c1010300c00782c914403500c4130103051140d0180104420591040e5045908401000110b00341e5405581d4580d01c10000020390882d20400e500040002c203072403044500b56955603001c500b070340e042140c0421a900c0b458a4007070900c20144800095040304c80461031441c903101140e80805d0240602102c080c60741c4800180c0c0c400d034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 295353741 1250 295352491 295352503
    0xa0f0e030718020c0118080301051c0f0b0403080a0e0c060c07030b07090e010e01080303060103110d0c0504150201020c1906060b1602210a080d060b220e0105060912 72
    0xb12080c5a08a800c1c1c0c0154080040e5014598901982d1310f4402040c8101801c28001405640d100c01400c0c5907904e0003003001082712a603221454181508103840c8000b44400d0000e09030548074507960202e5280c86e080180c14000002c0c44070302c1a908042c060055400c0104880100c058211740c0b140c4c80d002c1400000e07142c418160001080200c906007485452900302c40b403030007200c00400400200741c1c0c94400030024100c0c06c0c4a00c0800b41d0051010035a658001d40000c094071000010450034000c1040818017a44d240103030002c00704034005024400b110800c660040c810950340003d41c580f1860460040c2d603440619458071201c81500c1440040001c07980040d0001d0103190340b400d4480740309441680c100c907030320300c03040780706008401c07104441100f00c0b80030032124089003018010981642c0c662444d07503440b1422401c0b4450f91400042180b0720ba810240c2100f0400203200c02c0c108c8912449400400042c0d080351120000c0100100001e80d52481203400441084d2008503103c041039210500d80742c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 295354991 1250 295353741 295353749
    0x40314031920030a0f0c14011a010806040204030f0f151109010e1813051903030b0111060c0703120e1b01170408030f0603150c040e0702030a0f0e0307 66
    0x218007010355408950701600c0e03000b010301d05450301c801c400c0c8038014081e660310600d041034000c0b41c503000d20081501d0148074820212401214142c60703034000c1d981d5050031690505c8004002d841180c0c5008074a5910443c0380340e0002059078110b2070182541ca445415181c243e03c002c20f40d11030145100304200b41ca014050500c15a0041400504c1d428068001c094000c521650300145044040141c6c9141c2409030b0907400d1441c85011030f85866290684246405400c01603e0078818004046484c1940f4100010b902c0c0c02aa4006a074407004d40004255003404914000c05500040c18840840b1a102c2103c81041c1e0504041e000d5114101800020b0809007140e18010300521820101700d011500103451585000d0b40c890703074a040c1701c40440307a11070420385d809000800280300241ca0807964000645d0002d03c0101222011502c4a245000810301103030307020307400b00b00442c0801000c034008a031a0f8000c1c0e450300195090542c1500002c0400d0010441c500403c090703501c1e802120344090003694003030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 295356241 1250 295354991 295355017
    0x8040b16050c070305071a070c0e07020f420a0902040e01050f040b07090b09040902040605090c07060c0305090d120e0a0b0108060711031918150e01020f0304031403 72
    0x1244d9905055807034048503c145030001c00924004083c80c1402c0c070454201c95481250301c0000c81c1441181c0c062010000d01e01015440f980d10116955401000b1495003400c201300c80c2420a12240c0c90584050180c01c040d409200b41810000111002810682e80c040714820700040d00100500010307010340094843c19669500c0c21090001d44000140740728865401031b02440c1468541c540200c4d03d4914501c12782c91042818402200145441e410a48404d0300040010030500c5c1c641000aa804c14190741c10400400700180503820400140a044450445800c08000070b2400c1561180c440990f441c01804000340d41089446244666002d00b05103120b0b002100d2000b001072402c1c0150307582c2030082544c2403181000003100d01c0d00c28056024116540f03406941005c401c101e004c503201202ca00050140080030401802e031a481a00040c01008513000c035016028902d14040c0c4900d0b0500d1016045400c0a20311a422040020440b01100e0303214110103504889801098118040c0d40880c8081d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 295357491 1250 295356241 295356253
    0x10050907020307031e17090a080a050d1a0603040201030e0a0503040909020901080a02281a070b06010e0a050607020604030210200a02030607111009150c08040b16050c 73
    0x400c640c00030141840600c25202c01000c12038600c0094100754010301c161001489004042603104440c032000740c1c01000d076000311600d0244581d50040960000045980040e40c0400d48107466100390046a9155013054110b10900005001250f03c91000900c0641410780b070301c2c0142d008070800c000064215401c801600c3e2a251265071881c041d00791800180d1240c45000300100358a000820b84444469000f8180c41d68070410960441c01803940002600d099400c60034006510500c0802905600504407019641c450340ba1820b15121000a03103418100080410085015115402150144d8030211542601c3d03004038030019000384142e420080d0042da46040e0441103a41050240103c100c5c1a02e03c80c0c070038031421b001503584002e1404040d601d0740c0190081608d0701c0c010f03a6242c0541582000340c400168071000c0314800e4400545c0c040f0703190554a11680c2030700b0258850200203140902c0c1c040000d04103500c50444000d40540300c1c85540d134005104c502d40d82e01600490711900c41c0e170015140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 295358741 1250 295357491 295357501
    0x120105040b1207091505030f03070b040f0c0e010303080901020306010903080f13030602071101020d0c030518030d08180304030c03060b0121020901080133051b0102031603060b0a0503100509 83
    0x1501a0302c043d03881000140c100880c4074600850522800c41c808c8008505101c1c80c0e49641d46003000291050720120600c21000021801c20490900038080b80383d0032449551551a00030807420340100104070070392041c428448142e901c0b62a103001c0b207400c020780d19241d0f295001c91180b5441002140d081440400f40d00208001c4030350080d0418a0280d0149a00c443c028001a0703242c44110080034001144503043c900002d0090005d01003251040800c889400346d2031010070300d003011500f28a000f06484004126100c2ea8924160f08080c440d140594103240c82c566030002c2411b580c1c000104401d0321103003207041c964803501c01c040f0038600007131041c0303580c0540301001d000070f40c86900a580001e540e0300011403241d004803900ca2102114500441a2021400d000c1062061a040c2081048400c00505d08422090318807082c80240780d800050792402e0025030200d004d0039000c44002403500b408010410868008250303800c1d0005410300c10f50725076900e12003204125154005540c03100c003240c203100b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 295359991 1250 295358741 295358759
    0x100c02011b0809060408030a0b040509010e2e0e101d010c030501210201030b1e010306291b01060608041a090730050c031002120105040b1207 62
    0x144480203003010141c40d21a040c0011030300341104680c018034590190b400324001804d108000d6038801c14444000070340508200c002810740d5030076145010260744400f02240f011500303100c2441c8900c200c03c3c030443c02e09001042102001411000001c82c0707070780d400b40b00e00341400078480944c006030b6040307080107111803411075201c4010119800d000740d9031800403079404580c002e00c105030503a4080e410009081d10001e0108142c0040200c1c00c9040548401017103156880390a0b1000d003600054101c0c0d49042e40c0c11000504491107548094041c0d40c0c4030502d019040701141c0c443e01c156001800c8076941e0011f5607020690340c0700d0040440003961901100051040d070001e003c80c0114401d031030450309019a0701c0c00303102c484070a80301410309405c0040b0420090b524a035507143c01d0b42844480c0c00d580481d0900c500304508495809540741e030012041c00c9078602d0300b0301050315850201ea4045040907904011400d071100d050240f40d02a5655882e114129035a644080801645a50881e0303640b40d2161100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 295361241 1250 295359991 295360001
    0x503070f061103040b0409090f0501050a05010524030408031b03011d0106020f120309010906020f091f05030a0c0504090c0e030d050a02150402220605210d11100c0201 73
    0x100008003500b040103a40380000c411141103c000540b02401c1c1420840740c9001011100320448000001421040003c3c10a010341841103143e8580003402e5803510007400120014910440c010721805580203102c0260b0109aa801540100156403260750300801d0841155100c071844a00600c04800051215002a15081d00106104054040780daa5607010382c1c0e10491242510565004580c3d40803180719034401039940b00070b40b0000481c14035660b4403600300701d034000085484100c400040d13812480c100321014094284041604050804004000814600001e00520841031303c0d0b0220308200b80c407030030945000e440240010810a046210041e005c0850400154002d00401075481030942c050403e55080c0a501d801401c51030a401b840c0602121004000700c2e4003000704071032101030003034051b0a16407409060200141803420082004801041c07a94840c0741e64451300110284542c001c5402c42100c1002e090840300006200581c034201103900d80c841a00c03500d00744054680302d03815002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 295362491 1250 295361241 295361249
    0xc03060f0f0f010f0306090c0c050c010e090f04020d0b07031b020309060d05090a061b02070f030c0605030402032a190f05010f02010905030703051b070e01060302130503070f 76
    0x200081440240244400800070070030242d0310a200046030074580d40a2101d070500daa4062030b00240321030b01c600040c0101c402d62100500040e003405081070802c40104881030054a00342002d440c800c0700600040d0908000500c010602103034000031400319114101c96084541c0c0c004074a0f07410b480c120600400910001281c0302540103020ba249001a002004840c40003401030321452401c205118032101418024000000724401c08402c032002c80c100f80704500403004014065200ca01400300c000f442c20145411120540c11420000c0000907010602c1a003200c4250500035180c2e41c0c0d030300010382040700185a0084c030b9044441c204982c00ea440d0702c04021180d088400c40d400d00301255140e0a400064056810704449034a0180721a60190901003042ca0b110710000c0342480b0150346850540d040700804801246003c60341d00c24440302d0884000041c61168010b00c00d007890300043d0300e01850188210400d02d03900195081c2000f00c003004501c050107014049400c2c95540e009100d040000c81c0c46 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 295363741 1250 295362491 295362499
    0x12f0f0c06042d030e0105161401150e070207050409150e03040503011404110103150b04080d120e150c070807050304051801030506041e230c33040305060c0306 70
    0x3c845801c00e9480c01032a021184c050f80d8034015030f1181c90056900354468241400b0020041140000290303007070700c0b26980300801c44000725003030203409803002e2909050b0708103110f030112590400152903400180350044a074202c0f004030348031441d0b0400b00303107c1b82202d0082c02c40d9402c0040c1580304510000c024011110141c000300481041c05415600020040d200203056040007a101d18807580300780c0151400c2d24104283c150603a680702c2c5104101d5103d070707100d8840d41d0840301c500c1410315003040c00c1d111000f44002c02800100c0d40c00a81503140c50402102d14541c0100c2004070341010504403e4074002d41d4040c0521f235a0b101c01e0305005540760040c0c480c00d0f12451400c0f031040d4000701001d81241c12285c1c0180102015159035070340003152058074035008003000c10300c03000402260300c1c0354003c1180440824415424401c090105052181c5a044180506005030b0390210740041d0240c4084440c610803c10b0b10304015448800e04588115840a00b05201d0141840b803584c01020003035006030301c112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 295364991 1250 295363741 295363793
    0x1e0409110a090c09090c110d0905040c05071a0c091005030f131e020414040303051503030f1b10020403050312060a0b0403150e01050117012f0f0c0604 66
    0x1101c100b940e03c01404480062008901044070521980000200c0c20072420211030b883c1d800100649484001ca161100141c80d01608011600b000d11542da880c503034618219141654549450f19180f565481c92840304100d1800201640342641c180c886268006007070300b104000e164001060364101380c59201e074602c9031201240e10080d0325411403400c0c9070311184c5450403080301100d0b80c0d103000e5902010780c0c00c1234542c3d40c6500085561109148614429240040c4c1c03800c102a070750b18800050300c0b011b0701030751042080c540009040c1c1d0617200c0c8621348500311400381100c03019907805d0046031405101181d002142c080100600403024180318051344003101c0c481d58130002000240600352140092140080100340b0104100710420300c04104072410104400500d2000d0600315213090b40011a0880060070a0081903c28011401c500030307010640814061003040e9281c81c0050002041c031182c5e40043d1801d9000c3c505420380303001c80a600d0540e005031030301382001011034054003480d40721000c5003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 295366241 1250 295364991 295364999
    0xf090905041e0303020403061d010e0105040c091d0610180c1209081b010e100b0906010806010207090f09020a06030911040e010b03030c0c0a060c0f021e0409110a 71
    0x5105941c425034002600401c2011507540c4403040703440352141a41056020040440814101c0c0200400803100c100081c1c1c803551406882400c44031001c4091200307034105414003012800c000c1005003603131150800003d2141404009035850001620110024040c0500700104c1c0608540c241c01200d40351125076400c41e8000300180100c03070005c0c8030b400120300301050750242000d041d07100c404214851620149000211802000360031115100841169164099801000790921054000000c0000e042c0030140034200080d41c080c0d00141400e0401c6598400160140c0c4200b00790002803251b0030003040b010a018031104045d20012005078054440804000340f140e2003842891072560704200c040801603440c3c02040003801c10023003041d0403592100c0810346550b40030301c01032187e40091001400d00d15104418407181100c65488a405e1001c98002500031130004007002d260b65904503140a0740118a071045072880c2c448120140d045440c00700b860b410031500182c8400c0b05101241c0b011003555407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 295367491 1250 295366241 295366259
    0xc0604060504030318090e0601080706140708070609080313020a0501090b1603031b0e04110319050703090609080c01050109050603030a0e0d02090c1e0406050a0e0103060503030a0f09 80
    0x2648219000207004000c10030100307124034929030842120015440794196100080810340c0c01c1581c0540481d00b2100c01085018030821038400101801e05206c3d422054104072080b49000d29080035000c10340000720201088443c2d0f0206c03c1a03540035010300d0700d0b4100403c0c240d0500891502c101d009000000020680d0760003030003088102c40b94140880d14014511064011000c1000c501720185520f990711b09010700800c01152009000565412072440c603030034200000d075004003011030083c280030014004101e41c124407681e40c070300a00f070011075961030780d06003203000700352004010303200720700c0c0441e08401c10184400074044058502c0080c401640c0799a41081210b1042d24425415442040b214444a000307409035a00680002e05401140800790049621560308070b070641c0d510320700060078840e0a504001c56540f08031044040d1420182012009015881000303212001c1c030161912800e0907038813079000000130b0107010302540d4892034005070280202104075017500100d02181008a50005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 295368741 1250 295367491 295367497
    0x70b0a050f1014030f0f0d0206061c02010503040807060216030e0901060f1107090c020c120604030c08180406090c030f0e07090e07080102040602071410080109021c1802030c06 77
    0x560041d6480900346003080040d60fa60300c082e82c46401d4041c1c3c10100380c40741d0062007a00c03150311414015007800c118000d070090928200500062240c1c40308030f880501c640028901825003030782820b22944d69141d604003c2d0042c092801c000f4907042c0000703072040c0c0284450540c0c0d00d01900c244c5400350301260300402c200703600e03000b4081c1c1c10005510795101c01090344549442c40d82042010181c0b80100c2e105e200d50340a81d00d2801d09003007d40d0003601c14070042e0600021341289240c404003c2d021505150f50002c0c801101403070701501032070303020030500d50881d030340140c1190881c40200204581c1e0382e1606528090b00040f040f4001003440c2c80d4006890107036600030101401351200c050714429080145002c010720072600342142611a00740e0200c5c4441d0b00344024400f50a09400401c0c00790700d8402e044107081040010280102c0c00f000400d071807660014403e07810740e04c1000300941c80d1030402e1041100300710340f003000c081c0382420403071230030340288100801c0d41d9094029000c2d550a02c2c01e070010b020180c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 295369991 1250 295368741 295368751
    0x309090b0904080901180815060109030321020d0e0c0a050301022d130b1c0b030d0c02030f0d0309060506061207030b030109020a06051201050a12020105030901060506070b0a050f 78
    0x400c184001000603440600401d1300480c14180311506400c1251000e0030b095440d0403141e5180d200039000342c3d40303502c0200200c4d40100c091034000315450560740c005241c080c50310a4004909400740d0b2450485c0d4140e01501c601001d8240c0400a1076110400c1590b40c42a92034a24000c02d1a100c004c245400c043c001c4400550169040510307000d5426541110741e002c0c01a0b0b9441c0800c10701000c0401c000701c00c07000b401004a040b6140d19040a00c00d4058003019100d03402c00359905d0808080d1a031744001c24080e210524a040c1041c148140e40086402c000100d41181040e018100104a0003505640101d008a0240c90100a565903903000c0c041d551049820301d11101446200081038688a60131404600c94003500100780c00001c2d40c0441c0c15480e5603009840412804580d022046010a00c1503004160841d1181d40c03940c076140c045550651481406070402400100003070180009402400061602401c410f039502d2080c286807503c00701c2500c3c2441200e040c0404106118500300c4128015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 295371241 1250 295369991 295369999
    0x9020a3b06070606090501060503040605060a0609050f01110d020f01060f03020a0e040f12030f0b0114220e09030a09080d050324040e03030601031d150712090c030309090b 75
    0x300510007040440c1d04640d10403188a5142c80010420301c00c2e0340a02e40c000c15032034445c161130303040c189401d40941d1001030903e40030b40c4444508029079030740510034004448059400c2d1060f0500c0f030004a0724078819400301c034814822147e40c113544650008580400503220340007044210344490115001e0200c40c0300182d0b200101010901481d4820070003140c0203131042280780001c2c8110703501c504a504000f1480c0b0042950350050f030701c102c1c816000d010b0f401c020929244c00501125544400325000304140b440b50303004007041e03008100c5085180311024040501c99020980360491000303031b6a07403109e5400c8000401091300000c00e803000141c4007503590304c1e0707841d01e40c25582d4020341d401d1108940c0c8001358120024101e003614549130f601c191804007034003001869583c54058009000c0ea44030721444045e0900803e82c0c900b404102040d41400e540401c45c3c1c590450711111011907000e1300c001c2c91480d0003851707c000107041101c0d000218003180e201e9118a641c00382d0300e240f98000c13a00070400450704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 295372491 1250 295371241 295371347
    0xa030b10181a0d270609060e0307050d1d0d15061e0b090607020d0b06042f0a0216060c03020d0c260d0f09170c07061809020a 55
    0x4003c2e02c0d0304001e071080e00c0744c11038044a510940c401159281e2200d42960059078552182e0180a000d00408401c500e01000440c0f8001555071010b60710030005403540300b040301450510128200e01212006c42003402000c2d24840c91550030032080428000c9210401c0034501328000030942d51846000040420b90380141d880d4030301d440080f48840c3d2000761600c1d440300c410000740c0011f0360354130074400d0702c80c2c084d0051600d00e01c0c0c682c0500040390350906000d415900750100302d00b8140000041d22490065003401e650302c8048000c0e00b03a1400c060041d402a80038078030300020038140d178030000c04014140640c0c00c4031101c500e086000c0da2214040003001d88480c141ca81c0c8003900183c0040b00d96401134403000054904550089102c040b101c11411461807551542511000e01800e151600510900c4a601031315050190610340c2e9100a02d20a0030103101d01e4100c050040c0d43c066540d40c0082c0481a815941d41c070045000400420140d940d00a480429050055104002e101a98000c607040e01d4a448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 295373741 1250 295372491 295372507
    0x1150303080c0c07031a060f22090614090d0f0806060301062105070512010f1202090403020309100507021f0f20070f0e0c0306090601050a030b10181a 66
    0x7a551000b4242e044031301c00e110300000080c4000980071801407200d4130302079090403c142084001034194031124400c1c480540c0003801c40c425210040c00d46882103500054212103458640058200c14100202c0362659030b00300810400f001c03518488481072956006440398a0701c1c0c090301c0c88034007603030754540158013400113101450041801180b41c2c10415140c000681881c40c03d94252802103030180c0c002180840c050841c10410104103001d44148140c42c1c4a00e42001541e060001031038001038810000352020030240360003401144c0740c550026010150015401d00c019000790302403041207004500341014800c1d0b104840c01c10801c030f000c1540c3c031040010b81c82403080b649204008646c90301c100807054984e1141d081040141e0042040301a001c9071a40b41c0701c0d0494903411b00600103401714004008201e0075a0791001c0703c5901800c00d0034282d44494203510201d00409900038801d4021103120303000491103421000c40700145181288138180d458440061640620501c0c1c0c691041242c207226841c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 295374991 1250 295373741 295373761
    0x1300c062303010b0a0309061104060f020609101e05010e0103021003020a0c060c14071208160504050121052403011e090f0507030c0911040e07030c0e0a080c030115030308 75
    0x10170360703c440c07901103110303506030300c80c5011240c0d15451292000030000d010841c43d900180301a242c0c0c0f070140060715031890305141c1e2940714850481805241980c680d01d00300c940c1c0c008016003506041424042041e50385031001141000c4080c0004d034481d4640030301c0c540c0c1c168481e00072185040c1c2c841e40c50725601d41899075050041c02240da00d420a003c003040e80c2210281244001d4403000d0702410b001c82c3d558600704805041d021001d0310700c2c98808151403a13070740c5807600102240c003154000c1c070701300c002290002402009aa103444c00d000d07069041c030307041c442d0007032461103100040000c0c140c1000c1e840082d102094202c88030715065410040e5449049030402826600c008103247c085c480c5904007040590f40c0604200540e04100c4444811303010911423540d4501c01c0074140c00b0707440d48071490682030103a84540c004000342441e04150b01e4805008241d4070074809141d10705005844d4a509940750746541c0c1e143c803440c80003103020b5071030035503c411140000c3c4103c404480d0191107200c440c0c3c0b82c982c00305c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 295376241 1250 295374991 295374997
    0x201110f09150904090b0604051312080703140124050a0903060b040209030d0206101203120203060103200d0b180735060f01030504050601300c062303010b 68
    0x3100400b0621150295807500d018060117a84204e50110035450000d080008942c809887d20f03075030516102140700000d060507102004007885080240055603640400c41c00341c6003002200245000250001441c0c0003c1d24000784040e454a080285900c0710340c100b120300303004200e40c0000254800708104042081079001d816041c40240c409858020024042071905204403040c9005034410410001e0080104800c05c1c0603060f0184075108000036a14002e00e4002000034003444668000b0204800780e00035802500002017402800206019104a0842e160030070304240b045241009000712461800c4448005080016400c420381516005000c03181c0e0200d04c02900f61f1080c1c00100040788003420491180301d12114162a00c1c0da1820301d00340250820090340041c140b6040505000c0050780201e182e03810b440300c07a40c01c00c0031000d00c500050410117180d12007000024090786010305005e000c0802e201540c8103525400414803c01140c964244451b818501c2a0785082c401405540605001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 295377491 1250 295376241 295376269
    0xc020c060a031104080d0c050d02210c150103050102220506041710020c030a110303060a05090903070b0a0c03060501091a1e2701030b09040b040305040f0801060302010201110f09 78
    0x4440c28142c8030010341b0f00d40301d418111a00400c0400c400c920422100b004204250840340c4054a4080d030720380e50510080f500d441c1c440341002004240c25000d800100241032110328490640032107941d40f42000f500079803102c0441c013140c41d80e091249102154070700d0010101c42c030140a4901d000d207027922441c084245e002900b0b80f103002d500d01100c03a184a070b0000e040c0100c01c4a0213150f840c1c490040141c440f1200c1e045503403540d002481000b800341d80d071030210710407220140c83e090782e036070303a1004051b046220f9030000405100070001881000541d135405403100003c0c2e600d04200b20364680d40103403003a0320180700d904e41041103010f070019104000f102502010101206940d1207110841c685821504084100c13030b011507048140d152480400c00c2401c464500030b080c1008007441c0354010645180004001a140d0900c400c0401c0405200f203080b10018002c0169025207240c5030000c1c00d010701202c0c44160300560820b40081600ba08800071145942e00d0b00c842e2902c7e00f080303d0f003801030502402c49 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 295378741 1250 295377491 295377521
    0xd21090609052e050c1902012325020f030a02130b0a091d01060b09030307030309020f0301051006090801050f010e040f0606080c090a06030203030f03040c090c0e040c020c060a03 78
    0x180760007a01c4948082011800300d541300d06880701c0301e2080c46403504a08150104010259022240140c0d8200c0c4500410001004010b0520f80060700101d1041c80364403c0c10b040c0d48003542102005d10444901150361a1080315500b94840404003010b41e41c40c01c0a20103980419110100100c2464940c080780501c040648110b403d170f940c41c01658211202203040201008103055400121007080c410f0301d002d440040800c6084c8564640426500d0054410041c1419614801c49041d9502e6884244404400400030700861401d414041c0a140c114070035040480d100031b002003840d0740117026007440743c068580600256031174031070300d6490100068400e43c1d0b801c0301c1201c410007103035281c01000003420f4610020b01e070400340c0030284107103a4402480d80340640d107130010500c0142c0d00070048540448601000079102d4a4600301044070840326405005041d181015200f05d89400c17000e04a81c01004441c00c111311528002d084c1d03107807a0281d091640c452402c2000c01401800f81d4800d24055a00c01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 295379991 1250 295378741 295378789
    0x70b0a050d0e0313060201050f190c090b070804030506010b0702181f0b0c0d05160f14030a02210a0906050c0708030f03040c060c0507140f0d2109060905 67
    0x2050030705513404000014040084464144046502401841c2d006065010185502d00c2c103507c3c5000500100c485040c0c01c43c1d1540ca03201800e40c03180303081d0409405a41c6405aa509a03880e28224540c8a88402c4070280030701e20001a43c1101881030307a0400e600580780140c424100c9006000c819401010030807400c03591800b44400420490601c0090600351032031642d50040304003040d25000005e0200d000304039007000314082d80381c800c4440c502050741c070a006003c04891464807000292040b10900d42074440443c010321002c1c0d000541c02544144003c01d14401c01c41c0b4074a108040c4500894507004c94080c20b0f00700304061041c0d00806d654992441a103000319210a07101b81158030001e00185080720200511083c0500e200310b502c0180018100010100d1165a82c1901e40310345e07120b500500c5014403074001054079501040010301c903008000c0300407004030340b4200100d40c001512503100c0f12202600c00e10302d180100018010384000f522070710251489d207020008005420090818a28025 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 295381241 1250 295379991 295380011
    0x3031c0506181501090f0501022a030f031206060304050a0b0c130f030b0618130609060f090b01050f281a0c060f1003020d060908040b0417070b0a050d 66
    0x3207854060100e035520f4903480c030000c000050003082103811901000d10111401c022aa80015141c841415004185400e040503203002c04600d5031030081071a014002d03503a208103070040100003810204050041c20005490f141e00744401808126401880c1d03510021620000c94000910b19071f03c00f090001942c64044c140300007104480c029404183c4c0400e983c3c00038001c01c0068030400c0c0c0d00000c01d6460342c40001200303544900828000d007891041c00c084240c01014091036800255550307812403001d000c20341960f00f58000070044c0700401d4031105050400802c051400403140401c0b0040100404d11100c90010031450b03c000320a4a034194082268000803020364080c500b01d2203c20413aa000c0d11080703c01451420800000c000f02c0c0b08032901ca04114a00d1005004001900c0d0141c0d4140f42c460001e1030007800401c1c10300c90240050b40301090011b2403c5c0e8150040003524488101c2403403c0c203030240502e68a61070f9000745580c02c0d0007801091903607441200500880b020030100442c400c125 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 295382491 1250 295381241 295381279
    0x120516090603051009020109120503090d080c0105060102011a010e01210204210c0303050c0102130b031605040506031b040e090105180c09011502010f0501120b010503031c0506 77
    0x2954004403086880314001c00900c403040c00450304074603000300c0903c8460042d41c002402c040c0c4900a00c001803041c00b0000c002e00400b017007524407803803000d001c002c0b0300102b80c28446541d4010a641c4000e40d0f003484009121540306010312008203401032048418501c00320010340ba1600c600c40c6d01410030903110580070b0030b060121080503100391560340040e41d4904181d40c400c0c035240c0c001c2d65050002d6905003020001030800ca42c2d0401c4a42602d02a40c0701c1401900441c00b900c1001403444010007181c002041000004d80114040e00c0d581c0040503200040820540e01ca000703a214050b8402420310000c2c20400054828030303080c04108216038a02070300d5070501070841c0c00c151007100707090390748608000456424400b440c40701c00100004041069404c4000340706144140100f454040040e5160042c450007500149451a0b4841082c0229030b103500e0754400e0800c40c2041918400082c000005050070301004803844045500c803200ca503d03040b1000034011b4240038200607001480d00c16031081c0901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 295383741 1250 295382491 295382533
    0x50c0d0e1c0c06020111030f01180905060a0605010f0f020705040209010e100c06051003050c1201060f1e0b0c06010b09010e0607060203090c09190509012004090c05030705041205 78
    0x210480e5070542c540d00b401d40c024210f44074280003512105c810000d101200b045000b0041c115000d0001810003400807040c200c0140c51a001c00400c90310402c02440854002c40e002082070758001e90350702c25100c294600480701401d10b402400050781110300e0900881c20303c2d8004008296040c185512100c9140e008640b401c04039151034800504640703448003c000f203500645401841d01c0c160306c50900d0441d00c48980396542c00c245a48260314410b4035542c50381003900400c0007059503150400e100f070ba40e049042c0c48900c1c80152080f8400100d040441d9401d042c3c0c00741c80c40c090b1018014015a070070a05401c4481c1c0c040c903142818040000400700003039582e80000c111083c49098096120700300001090b18010304110b40c180700e98600001c000c0248095591400401c002c04000f0510751030341000c50340102100031305c4982c24840c180408080c41210001442101c040b500100034041c88200100c440d80800d803080400500c1c10042003041040200c8044034140c003500030356102088555070301103011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 295384991 1250 295383741 295383743
    0xc0f04052808100b06040b090603100305100204090e030705340f05030f010c020d0e0406030b150a0e100339140409081e04090c0206011401050c0d0e1c 66
    0xe4031490307000e604906a40910b13540f00c3c005490450419051100d074401e14060041007501480001c0000790640040700c24020065402c24261060f24203450040300207944140505c0304220300781010003400c01c07000012245042d400c400a0030f0030200d840c040106041c403000d002904180c60b40e42641c006800e8052179001014075181c001c840e5454142410704000074145000180c0e4034203500030038016008200c0b00b050b003049152080801d40c440c1c0014004240903080074140c1c4c5608070400065400a000c009004034045810108032035507220ba000c0d20040803100da02c284110398400704006100144d061b92140403114881400801460b0401781d00d000c10b5211561105a41100300110b031880c107102510074101b40d0f8144840800c42d06c0d00d8449209200344644124800c05034283d21380d4852007910b014100101080c4191000800c0095a41d402030103020401088800307031000c0e56000f0b0f000c031491988400060040c8000302c210503030303485a2a0200640207080003205042c05001e0b58079040010b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 295386241 1250 295384991 295384993
    0x3020f0316080607110a0b06040b010909090501060e0f010602071e03020409050d093303060305060403080603070501091805060301110c0303090c0d0302070b030a090b0a0e060c0f04052808 82
    0x510301300000400a074001c209601064128505010200381c826010542c0641c042d1307030104041030200012505600651f00100c0c0040c900310b90142001419000081250081510625191101c4441211510080c031851000d41d121010810014407001400d0314084100c5407a0340d10b00d9502d402080540d1410700c01100e10384c0000d6210160f142e0007a04003c05410001004c550001c04000d90340c0c51561030b40d114212400340381d5260b100ca01e03c00c1d0041c0000d141d01c0815140716081c18980030f07007401c40c00d80b031003440785c02240804500c0d075105403203240c200c0c1d0f02d01488507424a0000300080c000d01c000b904042e01552074000d004c2e02080f00100810003642d10380001c65507490201f4003242000c0746180d10307030710840b10310700e084010950000b4404140c7e01000d110342d5480c0c0382c803124240282900310006098444080400030888070380c0c1d00c0a926801d03241c0c10f44101c0da83e5000c4000c0705224500344110100f8043c0024041c904100d2005030341420fa070300c10360403203400e06080203c0b03400c8564004001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 295387491 1250 295386241 295386253
    0x1a030d2a170307020d050408070311030703050111070606050612010909051204171b010504051504080109080d050a0603031b0812041b08070e04031d040c050c0c180103020f031608 78
    0x50907030400461055035444e141c09030409023448043d41e1510545e01c0080d04040c2c800b14000c0c020794050280900460744080200145495442c04100a81141d48207880062401c4000103050130200207d4200004030282c0703c081f80c1c24182113a00038a40c0107829100c5100e402e8440010354440300052000e440760515050300205d070000c085160000c4000851048945030aa00c000c6980003810b4405851044401103014100c003401c01c4142e0041da409829998280b050520a104011004209606901105001503500d0b00c6c141000d0700d40e117210040000303442111042940910340c42c1d49020520559070b544ca491a42d07501411580d40680341a112145200c250078030b001c090f441c0c40c50080c40000c001d0502d00346020342006008074010409804e000340031009400079100c01500c49000341004008210b51040780b00c0050141e000189012658411211110064508082900c050744801d0801c40500d0382903500744100204000200c1d07415102c0d55035899100842c514007080600016001030031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 295388741 1250 295387491 295387501
    0x30103170a0c0b010609180213210b16030507110a1209091d07080604080f030a1107050a170c0a060b04060b030a0f0b12060601030902030f010c031a030d2a1703 70
    0x10034812045901ca0402d10400c42c20080c0e27000e140104080f581c0d40104451410740c3c8846120030075080140040842038003200308072204000b14074518100d016a5410002a80c8001090310030b01804800c0070101d51000035944001203102000c001e88100c546040543c0c10740d1041610203861111014000700130850b100c01c02c20040c00c024220007000c1d1400240b81c0b60815480b03c5426104120950605d200000009000021607801990a603000004081d9903001142003031501c0380b2100004542d0805103e018107400c40b0050f00b621b00c041322000240c00da01c00541d580d800208012060950815103540b40000c10001900185224404000c400724040382060a650100c0c0c030700340e80403403050914610010710700c1000074015074031440070300f80050152091b00001e40350101e86c014040b5658244005090080e41c1504009098190340070324041d4862102d00b00b58075040304544c0c81c2c1c0000c164102c010403581041e03148111100340740320303440c0004d0901c1e200d04d102c80c10783d00300c04400040c0001c00c1c41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 295389991 1250 295388741 295388759
    0x1050f0d0905160b1b010603080c06042310150905040f03020d051303020906220e0c06040b0304081c02040303030e1902030303070309030212031e0c030103170a0c0b010609 75
    0x5902c10f2010b01c8040c80609060b696240c9002c0c1c488400707000590344054000d646025400000615007103000540c481000034200390799035038200e608071915030442c00440f41d030342c0d039082c8540c0700900c4030806003a000301900d18000080100b403c0c1c445241038600b0000a134141d141c400c00d0301a9003d10f0b02070019542c1400c0103450646080508002c00800f0800c60f421009030301c224909403541244c014039181c5810700002c000c2d400c00c01c07440c3c5200c20031040007107407501c456015189004001c0c0946d54690384620810005010b04c3c4128a0000020000600001c02c140020441c4d0780c1c4c201a06100c1d5044401d407181203030080e80048001c240d0341ca481c2d81c8828020400386c5820300b0048c000c48181c030f4a95011035202c2c04046e102100341912803102c00f00301402407001e01881d50b55031400300d460340f07401c2c482c0c5800d2403140400f00701c4103004e000201d0341d01070308075085034181c03a0000c0002844689820a0280303580c8020300920401c04d0504440000031042e404850003403500c0d1360740041c503500b40100c1c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 295391241 1250 295389991 295390003
    0x70e0106110706030c02030c120c01060504050402060d02160510150b03190203060a030209040c0e01080a031704020d02041508060c07031209080f0d020703031b0206041101050f0d0905 80
    0x1400a221440724445410140000d05409a81051401081d174a9115a060703103940035041011310240185403090051308601d03005032055141d840005c2c000141d42d003040c40100c80c400d45020750002d07810032244058040513001041808600b480e0303480e06881b10f0b1141803c05000950607030f001340d112103e1104a24154040e1406030402c1c240b00740c40c40c1003940e181c90b045400e04a100b01e20356008400100e01d0340daa10881d20003140c024103503200714030305031903c681d91039828003c0c041c50f80c0010002140f11000020035803401907060300d503503241c1c4042490418000000070022680300d040303e10b8540050720780340940f040b040600c2428690717150401c1034a6080c000c0050038028560700c24080b84000c01da201412468001c40b0b0040026210a41d00744502148112160007030301305000100c8440300ac100c0d9005182283c041e65040003020b01c60a50001030700d254140110042e40908003050100d001e50340c0c011051201410498544080d99503400000e402803883c1803820b40c0d5840c41d1505003d0203000d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 295392491 1250 295391241 295391249
    0x60a1a030420010c030f18080c1516110406051804021e06040b090f06040303081906260a020a060c03080c07030807050703020102040509010b031503160b07021f02070e01 74
    0x40640840080c0000b403050340b2244c0084e04014942e83c0c80d060302809090703010003100006020000054684807840d0f82c2e05035100080d0701450002140c10885010682641c800400d150060364100e840707500c0e02c0c102e2880c042005075100b60794090010355640d0b0b68008840001a42c0990f0780e461415004000100c20040105048001000701290743c950315202101d0981d454040d03160b80f24030050002c52541048003038420f4011000280c048281500b10004a100701807034030348403240c007185909080699150748200210758506500142440340044a040304107907099046425008071a000180040d0499004001003a5015244803d041c2d0103054035602140c06040a8078021283e034005012075070080c5090704108010a414080504c01c0d01220003c1c840204070304407558483d4404105036000f6681f400302d06004c041070b02514200400c0201c031102800509002003840c100301802a540104d40407a4030807004610074401c54641003c1c0c1c880c81ca620707802041101e003003410540301d0b144c1c1030300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 295393741 1250 295392491 295392533
    0x50705011e1b0c0b1611060a1e0b0a03020402180a140315040b06010e0a0305010e010615020109030f03050a020f0301090b0f0319021903150c0e121005060a1a0304 71
    0x4940e0089000c6880c20342d007100c5190000c500040100c0411203448841e021652446d00408050002c544a2500700c11a402c0c1810002c07089c007145a030030841103942c22201c4a8200050302e40800c05458250701070400c409902c46061002c90340140002c4c1c0010030380d08091900d991451001da52800c0c01c02c0360382954200c1030740c181094180382d100c4000b00c08004000d02d04019100c0c2c581d1546403a10008240210390140007072140f19a03200c1c04038043c001500500c007042d0b03184106942c41a2050049101c12a00f40e15000348030900882c0840140000804011100b9020000608250307600c00c002d500801006070005004003885003081500b030643d400541c0f00b0390026214140001b0708410340e0f0b9400390f04070750b854050820045c100041540c140d00160801c26801c415680c41c540540100c00c100805582d1030b0a240751540820000c0300300c9000b40076440d4001c0c0c400820214240d8040f0350400706c018085050b0b00e070b40e144000801ca0030791003005241003000c400e00081101c5a80c00001c40c0d18809 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 295394991 1250 295393741 295393757
    0x50c010221061005071b150207090b0619030509010e03070c0e07140a0305091204090c111c1419170109020906030406050a140c120f0603030901050705011e1b 69
    0x2042c0208540113040014060b5105460400e60315030103145404001c0107d41c60100300004c2004019407203c3d001d2003541c1189090a40c0682c0ca8a0722408444000c13940e4040b00b41c01880703640040b00140402080610350399a243c200304a9444c082000e0b0000c9841100100d16003814800c490000d6400606410140401d400c0000b020101d26001c4c0c1d41d840342c40d890000741d16654544800d250800e1452440358800340007a01052100041d0070603101a1600d03119540200401030100303a44060181e8880e204407641c0801902103440303003120744980b510f2904054105102e02c1da0030000302c102445c034040402c1e440c464420840c0c42894045004000b0920114204401c440200e202031000030b01c0145805d41e103100045004807940d2111b9650040000ca0500910341800100f1980c7c1c0304000c44201041080000b69413005103174120751189602034080e60900358004010340e4160460076040b0380d55500c410015a0390700000c81c08040c145c03109200840c1ca0050040a184401000c44c0c140341003000c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 295396241 1250 295394991 295395019
    0x4032303090108090304050402030a061d06012012040611100b030a032715030e0a020a03080a051c090201031a090621030f0315090f060d03050c01022106 67
    0x11054031404070003030801e0480c66503410340302800c5100341d8204903401403021003440282d0ba40c03580f00070261031002058012405c0c0316250006080b10071220140041c00340d40d10603d00210854005001c210410b045854080c7c0189130110150070a400c0000083c03e00c2180030500c0c0810041c45001e051341c48002c0104c040d084020035201c80c0a442d000e030070710206070a560a0344600d8881e0344048000b42c10fa0760f46040c1c403a8842c20806030a18502d0000070708107200c40385e00880c0481c1414070300c0e41c01840d4240242ca50703a01c440482d0400740380802032000038400010481c00c2400640d2410b00151000140c515240c070014049a413038a1146010762101e030310b00a1291120f07140c1030341009003111a0a04804d09416441505400c14107000c02400041100307160f8400f280055802030075020140845d40b282401070104030501190800c0d00a000d62000c18120709200070600410350184c82e00a00d070450000c00f1500360b034002010340d1044120070401f0243c4440c058006038104500325110840c0d1204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 295397491 1250 295396241 295396243
    0x909060a030c060302130825050f033304030e131a1509100c021c030c30020a0b0906010503100f090210050310060207030f1103010603080f040323 64
    0x294042d02c8189a170016a40c2401da081d1000d650080106804840880900405460310348284940401d01004004000314041c90590b00048401101600400a0040507000f85040c014601400c001d0034500d4140080d081805200c1c651245000b0340f50701c0c50202202c414000050f84248c4a4140c0718940b540c000da20048081c02581c006908a42141c038614400400d04141d02c10f88840d540d01420051480d20316a80184007610124001c4460801c0c2d041050f44109130011045401000039503a0780d4024005640d01040f11b0700341c2c480603802c03101c402500c290760315541d21441040c00540c1c8400e62241c10811924007a0360700c60484400f41096514202c0801ea9070189500741d2a0466100e40d40324610620361342c0f146480356001403a206090b088250050541e9009170340c204200048940f010485500010303148040302e0340a06559118042901d4061611414060719503142d501c8003000408119004003400d50745640108644d941ca2039850401c40045040c0000d98030046092118410f242d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 295398741 1250 295397491 295397513
    0xa110a030806040b0307050310060f05030c0d081b0102042d030b0114030111030a051b250f0203010603061508060112030810080f16050613090f0e010f020909060a03 72
    0x7100f82c402041403042400080d007068041d0704455018403541006c0720910b02c1c507811400440b4903111001c2d560a48510525484d1740e02081f105400c040b001c142c0c407000a9039040108200c54403002003240e0203c04146190a80e4040d07071000c9511031010384101e08100c1031403079088180500010303454003075142d0340c0c1e02e10a580d01481107200c00304820900301c1260f1420341190b11100c0c4030700406641c07468100e03600b0000380003d59200c40704581031011982d40e405610101d5000007903d01492450b214500016412069035010840b20204818104001600c003400b030b044c083c6100d10008661440f0b50071a1000c1c3c010180c0c0030322215844500100600d00b00c040310311000c2a0945820f00a075941e200407100b00f107589501c20400ea1240042c1c4907411000450352152212a500107542da10ba5038004008090091042d103100030010f07454100000011039204155620000c2000304107032000e201020308440080090054117600081e16001600d030028041d50300c06803ca500702c274020706503150721007052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 295399991 1250 295398741 295398751
    0x30319150603200705010903021e030d0903210501031704031707050109020a030305130b03071b02040b18100f03080706200a0f1101020f0f0304060b060f0a110a0308 72
    0x243da1001220284001c1800c211020120b000e005a41c4041d1854964000c2c40c1b102d40c190018044d40e07003400a5603c40c0c4103506042e100d440000d504006411b10810010011600c2c205c00780182144000d070b89c07030315007943e2000c040c051903400036041d071440c20714400180e41144c03225080d281c02c22080c40012a03171410418200100c0c6003c0b5101c1c032181c03800d18014001c14a003c1d50101121070000101276010004215080282c0f051f11500307941c0e210580a203020036260000440c0001d0100d13400111040c04200307042d03000503c0030404050072800b041034400d02c0e4400d07100703800e0040c040204a00010820a00500021001d401154615100ea0006000d140001042903880d6251550380001c1c0078030101c1c0d43c0c0186403400303644183c0080003900a566800d40358003c9052410703c0c680c1581c040c801c0d100d0f101c103a040007a14101c000d002800c41130344018001c4072415900d002a0086071100d40c040d1850300135030741c04030b42c4d6469822005004a4034411000c50954403520020000981c04541207400c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 295401241 1250 295399991 295399997
    0x60301020a02120f070c240c020a03020906010311031911250602070203060f072304060f03020409020f09031006120b040206190906030b031501270c020303191506 71
    0x10744010b002d0313a540d48070358140600310107050807010800d0041006140e01000003042e046203c030302120740541d1407070007802000e90701140448041000d400e202140c0b6500220514000a20b4891100c0c41c003400d07002500c4165030700d1129184900e1040d01c607c03a45142d060f550059a0402c00c0d14800175294440ca90f250f4402c00b003403002034000f00929601a00e01065008042d030b15985051303c4004800300003101c018001503901a8090f561007107403001c2244080050a03010304d40f0341040415070b88103040340480020103900304400202c4007028400381410180d03181c40709690b40e82540401d864200d214917902106032030400200885001100800c100b26406030024115540358000101e0034060000b13516690100c2c90301c4844444d500903036000640707810392000c20400c0b0400085c1503407545c1002400704010600401401102d5850410b200c21001400c19101c40ca4800881c081c19115100340c0600568000300601c060030003044455020404c0306001000202000c06042c2e01110107403003aa024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 295402491 1250 295401241 295401247
    0xf02010e030f130914041505091209030304080a050c010933050d02030f010305011503080739030308010522050702030d0e0c0301050108010b060304201e09060301020a0212 75
    0x5400f40380e07031480081c44003020130421440341c20a10000b11604035400c44101c40d00c8036044006458134400c1500a03010342c8010a602031280c502c6280e0755001d0700c1400d51522003070000040c8036070104600c541d040e21401c0940f98025581e000900400c00380e401c0000f00b000c0d00b014812094002900c0028800c000100501d00c40541c1c41c8182c46522810b09901c071038500000401401e1400051000d0427640309200801c280d001e100074441d081c1c04180030050101c20100441004244112401601c21184071544416031200e255003410046d552600080c0f41c4505980c1042803503042000b0600400080e940000e5164480066006090401c28403c0000359201c1c0400c031818420004ea508007c504036007004407084080c0340d00ea5032410b01803014440e40c01c0400206803420180204140780c03034090700840c21525541d4900c4e15081e115a82801100d1075400f0450480e070781c241690140c03076810600d00b4014070f0148140120550007c14042c02a13004000c2e1040e041c1d400100c0500c00d0b200340c0d10040e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 295403741 1250 295402491 295402507
    0x506040321020301080f0c03031812120a020d02160501090312030b03030d02070501110702010503011503090f030f08070e0105030115120606020105070810031e020d020d0b070f02010e030f 82
    0x210314801c0d03074541d42125101200100f040b0382c0000320303141c03402e240740110340341003007030004050b40c038801e840300e010442c50a406042102c0c00c10301c4440b41d440560350145c580365078582260300210b42054642c840181c6c003400b5108103003a0140000540001d80050004885040c200040e00301c03646484018002d8050000341c981492280e40328450a035801400d5a03134445841104070040e4106c90000d4070154038010305d0b41c00745002602124491b990685416007143e01e800c3e203826110f4645820242815154420f070701c0069080000d05654900c26160300110a048040040072690004d184409210154020810030380e0440296070468008200d0300c0511202c0d0601200c8100c41d4441e6050100e041100120740340350190880b600c244516540d46489a8900d0104861000b107031201034442c004030381d0219110680c06425014250000d0860007411185602190125043c190203890308002c0c081400383c4287c0c09503e244000352584000c3c001040658a07182c0c0320300c00e6103003d00000000080f040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 295404991 1250 295403741 295403777
    0x40f0902040b0a08150919060e1302010309170f120105010c110f03120c0703060524040b041409010603380907030f14070501110d0305060a0f030f060b060705060403 72
    0xb03140c001d0003800b00c01b92810b01e400c2c820a01d60a04191000c2e807400c0082c08500c80085102d501c0c4103d07414440c40c1076100e4150010340003042c07800c0d0150750b00c030020950100d003e10301300c00400000d096004810707610000d04c0c6001054181c1078016604011400c0c00c88004143e500400d1200d03881c4c2190700b0b600000010b00000c5c5007084a00d865074200e1340c045502010b0000208221044900801c0140044d541d8800f2084229440f124000d4100d646408100c1d0542082d501c060f1175290054000038803510301c0b8190144031501111841141d0b034503480c060007080311460f14041d111811510a00001028400207503444151450700d00e8170a5201c4000341c158801040305034003c54101108010349a59820180000c501141c1200518031074050005002d5114614a840c48202640580b00c0180a01011000b410700030b00940d80c0a0369640000c074100b401001c8000c01144a140d003000724403d1031403c03500f90707a107103c1c5032485200e0031303c0140081034001c0b0300b1f158019030620384041440f900001e14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 295406241 1250 295404991 295405021
    0x607060b060d111b01140c0a030b0901030f05070902090607020607061427030702130b0307090615020c1f0f03090b10061803080d110d020f040f0902040b0a08 69
    0x180c041d1800c1000141c42c0081c3c0c20020804401d01400d081d04240c0068000e5090701c1209152000d045c440d103001030340301010719001e020052094640410070004450002c0e004000c213030010f460650f158922207007040810450740c0020201c5400641c1014017001c00221580248800070f4021500007903c1c0080103010f47c4a0641d51000314003003c954200500b441c40c1c010030404103c42e614885034255030f9070310000802c1d240c95070750040c050ba0007480380c500e070341000c0c0119039101ea8052003041c80109840782c02e405544094050910812203803450510001e14006807000740c01e015085540c4011444046400c1400000c0c04505101001c0d041c2c00c41e08800034450410040c000c0d00c5007106001c2c2c1081c51401da14102d84507541c03194100c007590682054100054400101013200c00c00c00d02c00b1010300f0b50404510f0711507080c2c01608202c0740008460a9a01001590071140000241407250705104454580a409024130440c01c06e803c00300c0c017072481d01c1050100005c0c80148000141d0840d024050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 295407491 1250 295406241 295406257
    0x70f1d011815050405100516140c090c032406070206160605010e190506090103020f010c05120306091f030308150301090b16030c09150c1403030402130501050607060b06 74
    0x10560101c0c44500300034104d8006000e03a40c032030140613856045940c070540039503804441e4000812409100c69403032026542802c0743c0d0450038000c81a9020070390b6100c030700e003601c0303a101004015520b1074030101a403005000708011a02c060a00c10203010103403201016501d100e0f07030580d41155502040c60301b0142da011136810051107142024004580c821045191314050502c8080e03030721060041500003001d4910455a20340c1000c50100100007502e4441c82d02e800382d0030117050000b105101904d802d810040151406611a00c000003805a64100242e115501c5030840f00000709101d042350030b000c5000750500c400350400c41018085504807424501d0410400e000600802103d4034034a0504850f400032210610984004201d601c030355400b0340520b41c801c40c6140d442d84881c9080901220745840f5240d041c008004902e024100000c0d0707031011910300303120740c540150303140d01c1c02d03104206040810091640d4014200001005642c403444203542e0416403081010440f00407446c0030480c10700903021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 295408741 1250 295407491 295407509
    0x301060e040b090c0d030201060905010b161209051206100509040803150402040b040303080708071d010c1104020c070314031e0307031506030c030e0705061b01061d070f1d0118 77
    0x205008151f01540030104403074010b01d00740803980e41c40207a50a40e00400800d10001000031011000041c0340c00c0c540c00c14a0900d0600120b000d481c1c5000c984240d003a188585040c0d40701405005001d1020500c0300000c200494480c01d0500d020394446516002c0980300002014500d00030040d01e55941d01540d000d4480c0c500350503100c6650b420300034150310081d40c0a00201d0703a50408500081d01c141c0f10007910f008156000481084020011602244514800d80b4140403048070f10315260f03201d000411442e24044000c0580905604080c1684040180140700f140d00411444041e51203024001c0c0303d110700e011150f0744941c4c520714113a000d407030416000c0036210130b036100201c2c8080d01030f0f00c0811a1446582c041140f59221000c0075520200390041e1548120180f040c00310b4104034a01e144000050080040380040da00c41d0388502008150000c41d0443c00c1d188104128075906c05d03480c0c071200c0024684a804818018052400c0e03151424420341003210384004c02008a120544d03140c01050807007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 295409991 1250 295408741 295408759
    0x209041103101410060219020112060e0108120c07170a0209012409050d02090c0706050405030a08060402031614040e10030302070503030403030e04090f060c03050a0b0301060e040b090c 81
    0x2905400a19a19200700c00003840e400110302c410f0602c0c0c0c0c0ea002500c640303130024600c0030347e1200c01c01000358800034228100141c20501100f400001e0040748000c00208580380d40d1541001552403c00d1481d112a10784c0b9901880b4000801c040041d111040740c1560035600b5a00311a1a4a02d0800c404d000d0040d4010544d1000011001e404210b1146100c03206181c4408030700c032454040343c2c104150f1050030390100103010000d01615020f07012a03000b4004241e4507240c90388541c0c074036080d1101100d01f40c60700e400110b10001e1840c0c01010280c3d008608031021461882d110400c03010790310840415030200710700c56441140c514000c00c125805030000c0c0002d12518600707081c11810304100ba002c118014001c0080c00201400d001050310700b66030b450340f5000208220300c01400024406030301c0c1a20080401716428010410743e20407504081c0c8160707804034052500707a0b0400d0580c3d00303020400740a41c1c03404904108080f10742d500c0f2034000d40d0090010856481d400a02c52070b04000e41085a8407110a0f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 295411241 1250 295409991 295410013
    0x31219180f050c06040e040b09030c0f0a02010e0402091311090d050c030c01170c030601020111030a0903090f06051e120108150129310f08190209041103 67
    0x4841002120303101e407085443c1000d081d014042540034921844241c440004081400038180b500306941c409811030440b4184242144c11a1034003d100c1c420700b001fa080750744010259603014640300b4200c1c40a441c25842c09068002251100500c41c1d084105943c1e81c000f2464010750850454441d1000205038540031443c40c1007803034031342c0510b0024520900c02c0d00b41c1060345501601c0c1c10242c1c0c6114980240d62940c0d500d0024003103600003030145045541e14401c051004200401440c00380000100000d10586180340280c842e40d5581c200c038001e040c4c03d43c010001030350312204845170038580032440016007241040200c06070203a07041b03103401441c07600008500c60320000750035903881800c41d1890100b640c0e1414201003400300d0b00b5102a2002d88004500c05c8601c00c40c0c02081c00200d101c541c00092048602c4d040a1a00318216511403012060810088502d00b0306000c0e020b0500c0002900c8107008145144005029070003000f8040c04940c000541840042200d0044000b0041c040c0d548610034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 295412491 1250 295411241 295411253
    0xd030c15060e09010b0306040201110307060501060f02160b0f090a030b01060206061c0f0206090111151501051c0905190b070801150c061109040f02041703121918 71
    0x110702440702c0011050001901c8800c0c14043c40c0c02955020300035088907200d0f42c004581c1020408202c1c0c210b440204a14000600c062080d18000d00c080c0e40c03180c072103c100d140002c0c1006280342d00380300702d44485001403246440032000c030f540d011100c6500d01e955400c0c0c0300110f103050000d680050510211203000207a50b50b0086009446100106c0b2032900c00c00803070241c8900c100e84203001030080c4100059132801030404070010301500c40141041c1a4069200385203030700d000020004c18113004403203810700550000118a407410645c00742440740c1007a2551043c0060103400d26180441c080d11008100c0a000d0b061000c01860f60490142400010032070070420400802911140000b441420000604541d10684074015031569512000b203503410303481d0480030b80f01c00e030085201c945d02006041c00f96995841240c00005617105c0240e1264036180e010540c0f441105c03240f030155001000303004210040e41c080d160740110341079012482001042c0c4000000c18910703924413030162501c1243c1060004c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 295413741 1250 295412491 295412501
    0x1403030609072307020103090609060e1006030b0a051f0b03060a050402030106051b0f0d09050301060806071b030e0d0818030c0609061e0a0503090c0913020d030c15 72
    0x10041d21424101c1e169120202e821111000b180f0240c480c200c40c004101d5800b001c000d000e194014900031550b4089500d501c011521181070444419542e918528152801032125030340b040142601001100e265440b10800b81c54001c00d0300441c0c540d20b10028110600e85414003100e58820030303503410f00d1600c1d401102c2e61507100b40c1d9400e110b0050400006072518050003140c0c16280380341d9400e42015410b499041004000107241c2c0598041c0c08007050201604000000711200d940c1d503015036041c03802d41450308545141e0070030010f9401c00300c10050b60580018406043c0101324100c015030313010302d080442c0d0750a40090140d501101004112042c000410080c0031852081d0510400d1050f17040d040603903034400480306540012081c00145c0c00b07464003001528044e2404901400015040d41500070641e002e4059000404c0e40070080c000542010452050750803010b89a000e01800c100346683c131a440b00c100000c0c814504404500105403054910b001e2150780640e40224907882102c0010283c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 295414991 1250 295413741 295413751
    0x1e09070e13060207260412060209010c080f090f0301020c070e09070915152c06041d0919050717100507090611160b0a09030f06060302090c0a12050a09140303 69
    0x10304005042e4194101d0003045508845071f03804110807908182c0e5031400a904113014440c10f10011407560404107941c4001005100c0c041d803145a030310b20044c420480054840d580c058040d82c8180210a01100700185004c2030b07401e10a5002c05a503100c02080b031403d400c503004003207014144151461414200310802c0103450048009100083c942c0c0700440d0251408010119001409000440d448045449510108801400180c50243c0f40e007200750b10381c080c9269604e1041134070740c01c2049001050040030402805503101454640144e1912555840240102c040000075200312101200b0204050204109202c03010b10030b614100c2009090707080e4034800d21007c00e881d904502c0c030002001c0f9680403500c01816042d50258248424411940c1014819109001e01c948010003c10608040c1010030b13407190201203420b90441c4103100100ca006000c0301c00d00d404c280441041c0035003040e8142e03002110080000f810b40e030740d800c108015080424024059100d504007006a055021000310700c18 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 295416241 1250 295414991 295415033
    0xd1505041e1208061804111801030f060b010302192001150b1b07090e010612030215070201110703030911060c0a060b03150a051e09070e13060207 64
    0x40e00c81580c000052200c03401d00510b408030104840d41c0d080d010706851a044200605144030380c1021280e12103540700b0a85040c0c4041f030a4112144152410301c6d0b1540709094009481444c83d45940c2e99500c0d103040d0b10600511881d00e03800e50316600c1c0d1196069440000c840c13052480502a842409003030b50090700d07044002031130388108085980e80d0500802c11909889602401c101307180c04228045904003d005404401c414545031480c200d0800600300604507040700001c64803c04101e040c21607000e903015020440d8001c0d2200040381d004101c408502d02090381025044d0f44602e0100e0041811140c844043d84d40814042d0906606500c1111424030030b41c824146d0030352600c10842c0307600881040008684c48600c1e03c10008005800100c8001710140032146500705514120b049000210f40ca4070400b541c8004000403e20610030a0034000c460342492200340c140294041c0e01e03100d03d80168040300b5072400101c2c0c2c03002d007020819020580c00c01011510381c5900c0c600004c11031603104030700e004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 295417491 1250 295416241 295416263
    0x8040e010f0f230907080a0c09140105090301020403080a0207080f0a0809090414030c0d020709050603031e0c01061410030c12090c0b1908090f1e0f1015090614010c020d150504 77
    0x6000c0c001c01c0c580382a45d142442401d07048002b0030044400f60301c03000040d41c165400f07000000000301ca01c0050003881d030241e0090302c40c1038205134026240200314007501070340e540540070403004607405c84203d408200b4181c0d012030541e500c90426850b030455849003006584000140244c1052005c50b9000c000001c0d6403d807044250b0720114003080d5401919000d516400030842550105061185a040d816041a1315410021218525400c40311142d02890b070706030a221110615140c0010314000300100303400c0c104081103030b1540003481e0f200d82d00144004180e030760080d4020302c01a020346ca80140041c45110b66151000c1840413480e0382e5040c07444002c1142d1801242800402033145504580010020104c541981c020391342da158444401040c039002e42801c1e0000404207202c0202038114420010070300c0809034100450201d01603110001051030050244103154511514445a8209103002e2540501c0c600025404c00d4140750018155800c2000c0c400c20b003282c42c1c1210340316a0207600e44000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 295418741 1250 295417491 295417511
    0x21603050d030b0f09010902032520010216081b100e0105010f0806070302130e07110f03090307120204060b0705010603020918060619090908040e010f0f230907080a 72
    0x100c844803c0c5890b480145c2d84018003400e210381d4013543d41b00c0020404464480040d00b142c5280003111805000028000f0b06c10503c0e0001c00b4030340e403600055160085141c8087c843e41d080701e407034009400030407102c0e0005c3d40d403070241c2c2410702c60070b802c801c40d000742c07a444103e02004600400c01107039111015402c1500008801481d1150340b01180e500c54094403c030703615144128025884100080a10b491141c400314040802c5403401e4820130703c64442c0c0c141c1c00040d587c1545010400031070790941d94820855008140c40104030722040741c16802046030010b1030b03480000c000c7d08542c0c0000c80312240100e074410034420150400e50031280241c900c1092034540441000f54418022030003a07459005101190240c01c1c106520160107030f010f03d440420035100c20145040e2980c0381420b4604840100d024000c0c20044440140100503440440042626011601040d11070901ca42464141c036110700a01e08485000d07081c2c07900d030009100070030300e2404d07440c0508900829500001404e2030001425 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 295419991 1250 295418741 295418749
    0x90f0e0c0a09020c01090b010e180f0a030c2316140f0f0114160218060a03140f0a0c060e0f0913020d0b041a1b040e07021603050d030b 59
    0xa59000340074145070380040c144480030000e580122610140da43d030340c01c041d002040307007080094064400002900030508003d02183c504445a40018545801403042001c0d0804c000a01c50829036160a0122030492581002003000703100c0c0c00c1c3c1160225501303400b211140000314807900715400041d84001c1098a54081c401c030301d105200f50366000000180c65107641d04d02080e02c1d92140e441450410020110340303142110079001200c03101c0c0088881d07002202140303040c8003e40070001841c02544260316044002a82c449550f1002404031604001500d20504050101880b14036032801205c04a5000e441c04403555080d03846498001205074445129506d00002c1450100078010044907440d220b00c240b00118000d40d41c403c990040d2481641070000d18541d84052046016810703203000c41646020380484244000c10080d0031648151000d00002c3c2000281e50a85550709021081c075030310b2131300581c03500f41e40701a12000180054000010480d0020300111802155542440954858000d01c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 295421241 1250 295419991 295420003
    0x1201060c02030610080a0314091005091c02100c050a0b0702060f131208070c1406040302120f0313030c0204050f1f0302030c09130f0b0603060c0301080c090a02040807090f0e 76
    0x828000d800c0201b41c000400e20404600b0003204e075032031180345441000c0f0700150800da54014a440821400b01310000a07251070700c06074035412100c500494208a0541c00100b541110400210038001c800c0f81d5001032010800c0192003030350707020951024600b04030310b0295407503404551002c0305030b07014070015009120a090b2075514951004c00c0200c0015041c005550102c00200142c04201c810001600407907081d000d045490f40901e4090540341c141400d0080c00e25065034002100d002c0d0800c02a03503050442c0e4100d0307a01140004a0703c9002040b0710b81110000d4000001940c0a07050400f4001c490b42501c40182c01462802180f00c0c00049601c80c04911b10800e2101075030603006010415090700b40300e5112540001900d1295440c40780311340e54084030300c0340400191018090300d1300b0000035050800813250802c03980801c941c29585403e540d10b590b140c01750a1b082c002c4800101040105405070181c801170085001074946050329008080018841303800405212030400380c482500140108038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 295422491 1250 295421241 295421249
    0x30b190b0d09170f0702180403120f0b04020304051e061006051303020a08060a0f0203010b19170a0c121b050c03090406120201081f090c051201060c02030610 69
    0x26203041c4107403401500010803106405440700c450528500c40c0c000e10701c4009041c01d000c2200c0a9407030700c0d00d42c014071420b407400c2160280307001e04200603c404a900040e403400c1c1c41105a001080c0302c0e4200c00c0340c401030110304004542080c00482848104600441e0260a00c0d411000c80140c082c0c42600c115900c80091b10514000500c101003801160301c00c40c01001036400301254889c00300d80da903010074155009030380091a2904100c00f80061902c3c240281108862940419401d43d41401090161803156420090102c012040890b403902e01a2143d02002481050400d05510b04482524060540c6000400008a44075011a8502c0385882281c611005004a0f9203c003410154152515888400e980c0e143d44000e11500403656114041c00c000b030090f48000441d942854030000d403052001806a010209650350812214010726161031f0441d1000007005c89c43e0500a90305a070f1504c504041e004c0c000101d58008940c2c160801c00d450f58151007030f0304950403030b40c0701800044d0071411405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 295423741 1250 295422491 295422509
    0x6020a171302010807030e0c12071a04080c06090310050f0a0b04021819030803040309060806011e0f051b0703440c1501050109060302090f15040e0403030b19 69
    0x40444c5c4030302d120307a00950421301d81d401241d9881c0110000110001c0c0c044400030801d52001c8020b02640840315080400000140c603054185810044d21030b403900c20f200110742c014000810382000540d400c01960b14100d00c0c1d40070400003803c0c00101d0b070070380140895168001da414a46503245c0d13803c16200321140d98001c8012103035100d03000c8040080902c411240200b03a0044000e011001c5500c1d90000c6000c0c6100b0b469402e001403604401030030025008000300e0601025031150f10400c504035800032100030f510310700050329a01c68407080c0c0705401f4000f12015100c5a030140d21641104c00a07641e001e480c0512903401151050420941c10900107005100000b005c031115036401140c0030280d9414100f06400e101d040100040040e4541078030300f0034141076080380b4801000296008102500941628075066107440e086501107032801d0640d000f00c0340151200c060581242075114156409044400c115210340e044c03600f0000c4c09441c0090440f44203000001d0914146c014090314201212841d40e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 295424991 1250 295423741 295423757
    0x1003030c060e010908030c030708060901060c0320150a110405060a0309060209041a09092103040f02060705061009050f040f020a0e090304180204061e0c06020a17130201 74
    0x254500d0094031524540b8030740307992103045800009001c03201441c858000c240388035490346441c40008021300c20142c120f90041d01400014803030310b54080341014660303030541440b00c041d81500000414007080c4a0342c0e0b460a0007812000c80c8661705840d240c5000c1d01e840082480341c084014295205440369101d00795015801b008400c061030f0094200e82c581600495005080407107481c00f14050740c0405899076482002026220110700d0551032840d001007445009141b41d0511080861500114100e01d072001c610200c0080c00300004c4940004d4010760107400c1c91384070f12183c540241e694500343c42d100c0f94502d8a101c0424010158400d451155124aa4018083c0c64545801500901010b41a6040080010003203085400903004a018068102c01907a460349040b2200505002c2c0321500700d01c140c0104001c0200d69030042d01803419a00030100c0d070700003503034107041954090080c903030040c0110300101e0f804100340d03001384001c41c0b07504050000d49190f42c3e0b1412006d28004043d50300a011840c51 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 295426241 1250 295424991 295424993
    0xa030801092a12050a020c25091a1203090109080a0203280204050f0108010e0304030b06060f070c0902090103060602060f011a16050309031c020a03050f04210302061003030c 76
    0x11030b52449a82d915040c0340169180c3c81d03882c0f20070707a02c0480d107000d400c503000110703035100c400200610281810368900c289205100301d050144586d41d540310302d0146540303c07034000e2080d5070794010b840c0d0240d60050140c5c0c0c941c01c1c8448526104d411001c0000d01040003a0380010b20300c2000b0440c0404554001c0103001140d58041c81803080584032180a0480c0940000707500c0161100c0c42003500a507103081e0000f4281d8036041e011800c0d50b010b52440d460541050100700009848002c40a400120456100c0e480324035045100c0820b0091603406480d142e03c0a800040a11281e80108160702d020398040c40265180c910581c0d41ea0401c1e03070a0000c3d100c0781c0d0010400300c00080b07880c2c00d0807140c0081540c41d00102465220500e903c5000c1078a031504002480c00d90341c07504201c9195403030032407210010850520310001e03407100c00c81072015040c0800040d507080b0604440d0101c6002d08210455030903d0154085a50b822110111046015106410208842c0038107202c1007400c0700e606644002e018910703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 295427491 1250 295426241 295426301
    0x6090b030c09120a020f0105041802030601170406060f0b0705100b040e070618050910032d082106240d020301060c050105010e0105150313140a03080109 67
    0x80205901c011600602c8040d00d40e82da45070303070702c04511001c4004103001c5001d8010000c01c01c4840c21060705000080008010f103c142c0d000705440e1058601c40141c50303a80741e100503180d0300500241c001400d9101010030082040d5075101c0c0c0c0654800d04007407840e85440b500c12606520030490050640c2e8404994100030350705c560044402c04c00003420202d030b2200c05102c05403603e055600018003143c40d120102c035945240c0c411020042c1011122500b103810101080c0c18510000d0002803e40182c400c0d801d240c100005402000105400400b00500d03040750a081d45c0a41084203890740388000110f00f903031070b000a0490140541402040c0221240403c8002c40b02500d80445100c41d8001c1845410045000ba2001e94024911600d1341040c2112034680b03a421540160800018a200c0388010311094903210180c0800c24222411140c5c0c985820414180c20b282d0040d004010f60110322030f6100a48001c0341c05103450b8480d859910351030743c0300e03100342050320302d01e405030308910301103042900c41d07405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 295428741 1250 295427491 295427497
    0x40803012306130504150302060403020105131d070807030c0e13090b09011b09122004050103050f010c0305011a0310080624060a080105060a050d1b021606090b 70
    0x40e46421648100441c0008254540c0001448440c0f80c0c24a0340d007000075043c103002d14001050314202c1240600e00b5030380042d1250040303000180c108040442c64600c2c02c0200b555500280c06140c000c81002c4d8000031580c02d8807103003268500005a0b001000c42c1c0d0207802400740302c0d1140c0d0302d0384a1401a000c40000e10170500040700700c40b480141c4509018010070321740007165004410103400401c2d10f0042c0048040710f2051010344104000311400c0c1080712450030726080e1056548864a008200782510500c071424140400300d0340d0040c907243c000402c000c00003602c105408010303402480b490690300025130407164240f00d401d41401c0822a00502e903c030392002554400340d013400d00b1018940301c85ea82440c290044031a00701c1018a05000c501446103104468840704044400c00e25256412030010051041031041600841c1c3c00707c1d442100c24003410a44080700300064080001c409001003a8084004240141004d030140c044280e1600040d40b6040c0b0940d240ca40750704c00a40e10380b020307030071440e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 295429991 1250 295428741 295428779
    0x615010302070f0c0815090c011803051f060504020a021507110d050306010305100510032d0b0f03030403020121060f080a1716111c1208070804080301 66
    0x59003001880b00007118150240c2840d4000c14425081d40c0c1044007451030503183c076186040101c3e042d410007115540029031100040e03428a8080148070107400c02030006080da8200411a0007110060400c090134121404900c0000c8401400110394480602040344542c001660068200c545c4080d03c10641c00030454003c02d181c90701040c800074140e010fa0404203085444400204000248003903981e26000d0359402500c00103a0315000e510708000100704254030310141c414107032200072000302c00c880e44080710902d4508264007900c400d801c0034400e00400d81754008500c80d860b440c001c0b0031700342800070541d02901c4c1d0684810f0b1684ca08240383e100161100c01103440d0458566801180c2400400e03a1080241074203002851b0307200483c40e0800391001c0c1d0003445500381c01c05128086041500743d8540c802a82c02120521a800a40c0c3c081551040b003000700d41d445004a82c880703030421014618204514126690f001c078552180c0400312020f040540b406030004c00203200600c81c24000940c07800303003e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 295431241 1250 295429991 295429997
    0x807140f0303070b010618050f010804060e0d022d030304080c070302060d1407030b010e060d0209040507090e070309021f020a020d03030c020f0a080d0c1206030c091d061501 76
    0x80128080082d00d10b40c081d000803240007681e00d00400c199500150707001804c2000001d03a00c199810031001c56034000300603003914100106040450140b261540c1300500b0b884255083d02c0c00c7c3d01494502941d680f00000100c041d55410f141a005011400030040400d815a507010b58910b464640302d40b142c6420004a064031409030345400070060b55940020180c00c0000403011801d140c800c0250b90491030028144c034103240c18140e944840e40c1e8840407401389403501300c44480c0ca038414980c03480000d01905002c146c01c14074080601400319006800581220034400c601e0b0740301d03502d07071804809445807008000c3d00300c6555070740b0043d130211801e1000c0b07040c80d503841154100c41c0982c0005010112280c02980800e986011400805a041c071a0780710040b01e000c02427808800c1603407800c00b1071107010381c0402c000741d072602508101c502c01e03c06c1e14038003d240c103020b0041a4880c00c10356407000b00e074401c0c0901c840c54542007101c260126030041a40d000510054110369032528611007140c3d035403030401410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 295432491 1250 295431241 295431259
    0x405060a09090e0703060b0301180303050c040e0c070c0f0605030429040b0f07030606210e070e0108100501050105090d0822080607020303040c1e030c0303030c0216080714 75
    0xe2200c910604402c00e010f000140032003480c5080020880e00c480f0300850099040036950303512040c0201c1165001030b414600090b0079900e40511898901541e0032504804030906c1c180680c0c241c445025003443c601450316406215680c0c040c13003080400c6441482c005c00e40a20020b408901c803804524071b814540761081d5106404c0340419010302404075000c461000540c0d05101000009041c400d0303000c0841d081c01c101d0b036420308002402c000c400110403d003a02c59003a607070750204100e40050380006604400c9508558494045e01568103090140250a1140d082d071401141c00341c2c00342e24102d07403041c0c4520340784c2352101040c8800c26104e00400d0301d581d2020080d405025804d0050701c00080020821450750500b400c4500e42000800b40c10034085600c14001e0001040824058000f101c003e455031030150150300c0c048866903000d541c00900071a1260b40c0000c2410b4141d000008464010f074291460800b0148000188081901517008141e1004005102840d8000507072241c4403001051101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 295433741 1250 295432491 295432499
    0x3120c171b070803091c050a050d0f110d0507061505031c080f060120120304140105071e110102070212012004031509031e090614040b0405060a09 64
    0xc065030000400060580101058041044090003100302410019018518210014002485030240c521507404800c0468045030104002084607250107a800700540344151001c6002501c0e401568900001151110f2182c815500b40425115003d00c0c650300c51a040200c03030380341d910042a005000306c40c20000c1920100d03090b6402c01003400c06801d0544043e601200151005007400ca02418030580c004401051181c142e8008108036000c01c100c0c20002400014203080f1441c1107040c603040821184008240700621102203181c01000110030001e200c00c1d111400200d5006007803038850500c004c110380c2076039401c2e8454156100c400070040c2c005400c11750941c000900d294644500b0081981d5544401d01452500081c20003002a90203041030500d440c40c0c0718440c201e40f090314a290010342c1e40313281100b0103000b0041d03130320380c00c0c00c03902524504014140301a00781580c5005070b202260048546446400c2c0da1400c030f0701558083c00c030b481e0a1502e0301d801d03c2059048801d0310070078092410300c041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 295434991 1250 295433741 295433783
    0x103090c0b0901260604090314130510020a11011d03070e01031103060c070305092206090e0a02010e040902060f12010e0115020a03081005030f0a0501110403120c 71
    0x6001e045030710001903907814107800261090031144c588440c41c0c1003070300000b540c01d4501040540e10000954001c19501440d14040302c050400d545030000081010135074544403599008400140d4009480e064002540c0b444144d03920a0f4480e0000c0221150000f100041d510600e000440041c9021090000c6500580003c0c102941d0381c0000c0a58000c403001001030104613080010044011790103458a400d0240056646210703018001c3c0070f1010000c2c01c552a44c039212071072240d041010010b003840d48a0103203c503016080611881450508007a800010b001000c078005102550503143c10210401040911014002e01c002c00e0341d2140341030101d45015950358004084191030303204040150340c142001d0084038607044e0082c15500200c0c2d02d4036092a500014401c204641504003051580e50320180040c0581640d00b20316010300070096003404418001038034400c1d02d03100302c000f8807000a50a405d40441d01840c4005442202d800160421a6000e06201c1e10218000e545070b8040862900e464 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 295436241 1250 295434991 295435013
    0x6050409050a0c050109030b011505090a06020a120302161e060203040f0501050907050603040602090406080f01090528121e26010b030703150503010905071a040b0a050306010309 78
    0x1d6440c0d42150100c6401c200c5142282e001400007420507416444c25621910302228050041da001106000f100da000745005000f82c540359003008007000d0b400b03901c4000003500c1c0d13017080f0001c4524040e0185105c581c0c038003038000e807905000a01d4080c1148040c0b81c1b500f05030301207601e000700d1f0b981c8010407001c0c0c08203045000452041e4010b1801031180101c91034480d0031207100900340d00498000a6003031102d0b0b5191030480e07030001d801800c0543c03507500b41c10010700108095804401140300d500070040c980f08040d000385410130b01031010f0300c0302d452036848888034407410800c00c0800102200301900004e01071141c1d400d4a04013a28052882c00c900c2c01200000280081c0c1071404200c841e00035140d44501004e508a500c07000f0100c4030b1041d40b40c90110134032800050111424192500c90720006072601d040e0900c001c040c002d009110707101c01c07400c00d15140c01d100d0240300c0035407400c1c1c041e9500d894501c50444045800b0095100d240c0703202810119aa904050281410076440c0c040050100380e600ba00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 295437491 1250 295436241 295436243
    0x1090602070b0106051908041b081b01093f05100c0f0c020906010e06041508010803130905042f10020a0203070e060612010b04050a1a0a0c0606050409 66
    0x50303442020b801c0015002c0c0c8140d0142c001c105040020b40351a6559040b00395106266040610094aa80c03800c611561000b90f034070311256804c800b0001d82541c001412948a0001171440707141810710030011215080b1a0041305d10790350700b82801c03aa00c0010b0a001100c5e030007000b00380301a0b110310700c58503491340042110107580c02e0384080c40510319110280304444514401c0c1c148102c581d541d00d00080c2070704940e4003020b41304030b2550002402517409071114180c4000000c0400390b695403140308a400e00d02d400481d0320000780030380300045100d01001044075500340c10b03c048014a10b02d090f0a200c058140204111907009201041f00400010070750001207000840b448954a640740c40c0601c000210b4100191045520071018080541c40114100080d034410700c01d1107889071307580340215202e031040c0d54843d01344520341c100008070b852000002d0010740c1c0c0110340002a0558851000c1c010103180e00211041000400c100c0c0c00690040c510303012014800c502c007203010761392400020100c910440e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 295438741 1250 295437491 295437503
    0x12240a0803270618040c0e212d0c010801081c0e0d08031e0606090111120c3009060304060b0306010807030c081b3a051e031801110109 59
    0x1441004e68030b45806080710800742e900d440101003400c00300050f100189983c113048544443c0740c10106402d010b1005d0340480e0300c2c3c140c281c1a210012076203102484040b0309103203281d000c1c01000c40055031140007503504a4200b07200402920484140d031060884110400d9800c1c0401070302d0152880e00c64403d0134081f00d0085403001d8413171801c0c4440100716605404403110400c0b0b207000700569075442c07d0503102140f401f840d101d00d812600400c460b03d44421510000804540800c050000c16030008450303e105000b40108000c40340600b080b040711041031600003400e46c4052210200c1e604043c0701a5a22500401021420f911283c0c04030b803e10b4000c0e001480340c0c2d00300d48003d005002d032048003070005161500041c0550080d0400101c52000c00103075051140081078a10f0300000c44c1304900b003040c00501c5034030840d1090907200a03004265a90011a400d00070540050450381d0700599581c01c00c011600035610340080754410321200787c1e209221906001d58114540000082441480d81440c4650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 295439991 1250 295438741 295438777
    0x606061b070b07050f0601030c0b0c0a1b051c0c030b04020d061b2304030308100306020307020c040e0d080f0a06170102030702150408040b090612240a08032706 70
    0x400e0117403c2c48455510010750380d0040b070041000520440040303085614400380380d610741c1d291400e418100803c019010380020401c040c450102c644500119084820480380c0d504400c50910240c41c040301c040c0300142024130311a00420120f40c188000c81c1c0c0c03252006000401c1c01d8800e0340d0318012682d540d41481400d0701e0b076108000c0c501e5040107202c18411001e00340104104c0c80345148c0d003c0d40c82240030090400c2040e41c0410042240c6500d10406140d00c05401c0d0b4036840d2a500081d0b03a2401a1841840f030341c140400705441c081c020829020300300840d5203115a95076180301c0602e00150142c44840041d030740e034900080c0f5261158030f040c4004080d0380096a01e04040d080286401e00783c403800010b0318040010300000031107410481c2c00720f403844205503031210042000070382e59019141481c0380ba42d0668003003080700c40c0001480c480310319002083e1284019201c05000100105003c0c40303000ba84200209000041a416481400d8030700c05402c20394040b00c01c2c08100347ea0071460800d9401c000e29 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 295441241 1250 295439991 295439993
    0x90901060609060c0c0918050f030c060705090d030305090c030f0705090601030615120209060c0604020405090118030503040203010609110403050d020606060f07020103060e131a090606061b070b07 86
    0x1280c40b00401e42407814504e413102680301c01c2c0e0481d081d4401c0c241402c0d0755120b5001c40800d00e0b1807903c800d41d0054280d410300d0f248110220740320382c0404403540590081800103900680a2026200da1480241c44d03a24000107e41d4181c0c02004003030045160b40c8500c4007400165a010001d022455518901502c0420700d04028010301a201420560516040520902845001000c051840d1401d40741013000100b0013406140284141044541c1011000900c07060b03c1c5800142240547e00c252000c20445d83c1d0b0b490032600700e070900e074801d100030789941c0308207000300e4802c0e0061900a4001400020b555560309040d50440f50340310070210503081c000c61f003001400070621544580204a0014201e107140200c0041c0c09842080303180c0030140d002156500559110380d06c4000681100301c4d0f85400cd0805480075180464000e800f19001c0b403114210440415001200031300504141c0010700341070300d84100300241c940088500555041c403400d0444100141004010020084801155503507941c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 295442491 1250 295441241 295441247
    0x5040501091b1b0b01060f120c0212090f0306090609060703050403082712041701091101080c12040f0201030c030c080f07020118060c0807020a2f0909010606 69
    0x10507809031241ca072810039803015000901450030302e100c50529008218480c6440080c0c1400e2000c0000741100780d207100003007681034000a9130209481c1e0754a81840740c000c0701000a069582c1000c401c40143c0041080180c9090080050003075100018044181c200003100407a1030700c48115082400c47e0721100a0041c00d0310280807a0307803c2103407460140000c1ca441d45000e45480350150002001d06c1c0b048440b901c0030b04521181101f0109030a00b80d4400c010012000b6029820500540c1c40d40080c41011140c41a414482c0e94045a40008020381a1084072300641c4d43e01e4005101407048441080001d5000300c0c00c441180c1318070700c079220343c0c502c04140307000040c03c8800c600c0e00007003490f00d050340500660b5000120b4a80c0400c0d02d1f03402d41e00d2541d6561080340500100007101941140010070340f4100f01c019000410010650340d60000d0a43d03032080300301c9e40d0b0150258080e03d900008030540c0d116080ca01d40c03075418403910303103114100b007150200818980c1070101c5000341c2595441c0742c1442110340c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 295443741 1250 295442491 295442501
    0x105220213210204050f012106020c01090c3f0305070c080a060f0c0c06051510020a021008070801030f020d08070b060406060e1813052a0306070e010309060f11040504 73
    0x21403906d40d90007907040545031a5002084100c400410410000440401c555501251006001c1c0c100900000c03405160881764184903004203030348900d1040340d200c4002c0001c00041140020620001232000c8000080c25511042910a4040043c20003410020406841c00e440040241d903004010782540e6003040030440d1880e1032040a0b0314203101119681940c802d141c444100c0d084400081c0c140c9a0504440d6809038044200d50880e0542c0d40580001c0e8004c51001c00090090b510001545800c00307084514a5040313514074081520b4500610201c3c01e2050341d40101440900018401c034540d85411099401401c022601442c034541002164100380c0120b400800c82130400c01d440c220300074001180d90120740544000b10318454001003a00507104011007940781c2180070303141c500900c2c210b003422554171510306410508540e00c0b8220141000101580b00e08030641c6c0e250043e25070040110041c2c013250a080e10358680364207801c41038004038403951102c04400741003103540f03615020500003a22 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 295444991 1250 295443741 295443751
    0x9020325061e3006060f110c0a061b0816050d020c060a030f09020406080a020901150f0311190e040c02031204080f0d0c09030209010522021321020405 66
    0x203040015801c800540000c00385007204034401d12011070a654410250440c0910407060840f00d0401000240d0700380c011701c3d4420401e2041e0741c1c00d080e00f2100b0f5503403a5200c462948091b0402004101082842d219514020b0200500040c0080d080c549403501411038000c40c40b80355810001d00d20307220400000300074404003a030b00e41c0050401001c40a0003d42540038a4043c0001d040d00d8021514415034564410040d003035000f0000c04c1190703121580240c1d10070101c5c03c128055030181002181c01400c1030032049160310956602030420704510030440180138a1000b0b20901201880442451000d13040c52010404c0c981c3e45595121a410042000307540140720180705541081007404800c1400b6034040e540640c0000c030266803072603902c2c4894882c0c400c04901b1880c0030316000594402650103a85c0b003089074001c5484407866620381c010808480510814440c4114911240c0c0d2031280d210b401a100035542c00c0c0404161540d41c02d401200011900145080b02038681c02400442c902441025004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 295446241 1250 295444991 295445027
    0x30f0601081e010c020c10050c10090209010b0304050d0507060e06090c1005091f090513020706050c09060315011b0303150f15030f0b180610020303190902032506 71
    0x44404d4200c0a0b40318a44a50990302842c064031805086d28000c000710303102d4106180840b0000040381d01078400074004c41c1c4040744201460400029a588a07070140c81c042d40d081009071602c010324130313800d640690150200322101a143c01407841c4103981031040d14070803040c62001e813016482c807801300012a82081c1d058010320900380124008c81d15600c41c10040603600060081071511000c4094038011080d910141d44a80c00aa04a0385041d080d00a0554103104200c140a113444200c40c0035114042c4884142c0c012070f09100091000c078a41d86e2103880000181405c814000c81c070a4041101c0307242084c19000300362a07001018060b0f03403000320300e80241189110181414100f001941403501082404030405895200f40c003142000d0398070003c4c1001e4010a401c40e02040b04c1c480c2030507484111040c5110324903518018840a0000c0116403080c0a8240100035804032786603800c0c0106040841039070540b0404102c3d4010480c1c2c000c1e040400d091640e104e000300351400000500030000d4085107201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 295447491 1250 295446241 295446251
    0x1e0b0306100302090c04210507050a060c0201080a090b1612090305120a0f02130801051b1e070203010e010e0f0708152d1b090604090209030f0601081e01 67
    0x490246007003000d050720350485824070f050311040c603144050b010300d07042002400d20059038200403100b030300d0082c601144600e05031801d19550300100580755074244151801309074145c4819005600c03804075030fa80203100c8036000036034010340e44899206490031246000080d403180000c4500340d800000e1510f02c3c00d10024144580d1100741e41c024403a0040303807007803103248400c90003003090700540d07400c03444954805440440d01d50100542200d80c1203070358460000c0a500c0c100101d541d001c100c214403202c1d0780b507845806280c0038400c4c5843d03804406029880500320028055440141d4013802001f0145480a0002c40c40b098004003441c01d04000008850095009084c00c1000c0790021681050006200d2400c0c071107562460401070403d2390540e0311813400c90303000c2140500e0003111141766004120700004c440e0354114440400e42700b131091800c1564480c40a000030071107024150000d20380050007030180e45141c4040307504c4514240c401c4e00090900c0d0000684000548030007003030060140400002440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 295448741 1250 295447491 295447501
    0x4020712050a02070e1e07031401031103030c100f060f060804031805090702060f070507050a150207020d0f051506010f2703050c030c011e1206091e0b0306 68
    0x841114061180c030a000d80460320003800e50080c000f81000b801c0740d100d14801482d1607104010f1668103044074155421081021499051080c8515a00e0804660713451039240d003188ca49012003065600d11961500c010024240d81e640244800102000800d03404107203240110581d0301542c1107500700300840f124201c01001710380c0d404440c00d60440d4160415000c480300d0b0190f08842c12049405c00c68020f00c550003071041c020f03400160103124408916412446445440c4111414400c81001803c1e0780c0c0705c0a5140c0105092400d801d81c08044417000510b0f010055003c50410b5421840585c0e10300c01d0b6003641418448144101c0c0140301c0704803003811031490f11400203091000e5504965042203441790800c0400240700404150810303a43c031003126515500d241684c1e6a24440960501030b00890202002e65405402c540c0c8a54007659424203803910b540004a45954203c6440d15006844140006013100107200e200084040003840689502011038050166a81c001c0e03a20b010340d1207002001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 295449991 1250 295448741 295448753
    0x10807050f030601140604230109060201050c3c07061b080f040302070314030c15041a07120903080609060a210219080a210e010c06090b090304090605040207 69
    0x40c1560404030701050500c0b2030201040e01e83c043d41c1c001c07c96000c040381c843c00c608d804810010b0403030242603942d1300486032510b6040b0f082e070b082903e48010299003071104031110701001081d0b200a25001e03100030041e12220f01e4940c441c0b002c5018000d0f082400051490900c1624000c8a41c40c8071000ba40302c50740d1000460007018040020100340d036030303824400801c08062007440740d040195084101c607402000c940e00b160303890390702c1001102072512420519205140d160a042c074071564104003510342c1c141850010710054040100003c041003448d5018407149401423054100d410f00035a20031015160040500c550b104002e805644a001003443c20402355000281e9502091040440301603070310703054408160740d40c041c001c1c0b108814811440c0410f01c0d00d40000d21000c550700540c1a91b40c00c640104910790500d0889000100103004d90920190550150900e0441584180000600700306243c41c0e88200381000c1d0380780c06c825080010108540d400034025000542004c03141140b9100541c0c1e200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 295451241 1250 295449991 295450003
    0x50726030f03010b071a040602040807090603080a03051819030305090a050703121b08030601091d1f150e03010b060a020709110405030a0302010e120c0a1401020d06060206010807050f03 81
    0x10000e5460002076105c100464214100c051401c82c1c0d41d891400d0510b0300d00080a5045801240440c0c440e100c00010750311400d02540040326044009949000000201100988001081344a400403400c162800d600c0c41006145681c0040c480d140302e0441c2c0900e401000e9500180025000b980582c0c200000700e440802d801007101c0d407103099941d51482c0e080b030960704031007004428110002541c2c10b100600c040031008511828003684d51100582d11500707004000a451a9050758084050b0002107103c1c851104840c03c594030f010116144030b0341c82e0103104500140c8840300340082d0f02440040f00505013402282d01444013203601c40d040c01e4603500c00940e1a007081c481c900f45940c0740e100060a511160080b18081c080160564a00c681c441c140039020b403000b400d01d003002c0d00c616010820ba075034460085e120601940e001030321500c4035a0321084901c800307411350b084080d5400c21401030f504e03005108407c010911a00546400d44c90102e105003801c049030b100602840410303021440360340d404101c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 295452491 1250 295451241 295451249
    0x215041e03030b030102161b0614090102010207060203160906020601230f10020703050601050a0f05101709070501020f0f03030c182d0f0105040b07020607050726030f0301 75
    0x1031429900000d0404402414030614501c0d01544001814140e084500040d240031a0081c0740882180300e0910240340e0050300c1c0e01c91100020004684061250b1100000304541c042c14400542460f0391500d07464200d81c02621000301140f01206004070850300400c078400200b40c80c1c000381031150b1606d919052010407800e40d9803582100048550590382d14400d04a602c120081d09031903046451600184d603c00301030200b51080d1066500018443c41c140c030a060688001001001c0c100c0c1c035103814880800581141c803011301c1a050340036414a50100b058620a05510700200b00c3c1502d00310019041c013440343c00720802c5402c040d21004400703038000304994001c180340ca2181d55820702c640000240c2d03114040303140d9100003c59414910222502031014841300765481d400c0e00400001c0c1044003140c80b02c84907078003164050008118040019014291160015100f607180c03007465a80c4c00d0620400741c0103411040d40ba103606124030754207031030390b040c0d00380881d0015454002d40c507509c14518001446 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 295453741 1250 295452491 295452533
    0x50d030e150901020c1606020c0f040f2c01090c12021801080303010e0106110a06021305031204060216061e0c151a01090501050f0d0b09010306020a021504 68
    0x4110900208000910000c00c070075002450780e0030420a014081c0d0300444105885100e17010b144500e207108a0500303403c85103c0e40061504090b0b22040c8120a02c0343c005a9a00c41c0d903030405042840c14078000c2d0344001c00c070050502e5070b00c920078504040443d1091400c0c803c980c9003000c3c0e0b030001140d05000b03200b074030080c1d0440080012288006a03210340d260300e00b0f550510f030b050000900090004050f506946a10406000c41ea0705c45004840c200c0301000c80118940c03041d076644011130341550046c0003051800040100c0903455401180c603100901c0741c9400e81c40d9000508100c0c0c182c0c14043d071130b100d10307508003152501032a240d40203012141c0c004520189841002d1152031942c01210b103204607592145006429621160000009208910341c00d06064199006d80010750310400c12001602c20503158981040066889510745401250041e00125924201929581c2d034038180c1500031442008096510742040b034009042c041c00020810041e5002014040020108410382c02c0743c0385c40302 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 295454991 1250 295453741 295453751
    0x90203040f08071a060d020102031b0304120311060f090d14160f0212060910091a28061203050a09050415080708160308131503020409140103050d03 65
    0x4100069907164070340e0020002140010042c0070040d03844400c001e00c9804207450741c0720340d9070309041c04805203581c034000340142c1080103041003030100a82c40c003071b1408110040343d040c69110105800c504030401c90580c0403c1e503203190114100d80400020381d0001084400c050b00d82021845a5514031007160040140005c080030000d000407004155a026040340400740c58041c010300b456010300b201c114003a40a0840b95101040d5900000b640703074001c446d484001c2c0844641408000b0041c134101c54110394403606141c2002d1300e400500242c0d8040c1c906001980792984581c1811101d081410100707440e80c509100741003011900c8000c0e814855505801c000d0760310044004111402c05c200d030006980140781c500b0100c40310301e001c0807410503034603030a00702c4000300d03182c015140c0d40304540c1040440e004c203501d8040c400242c250018003030b0710070341100e4400c040382c07503617800344c0c5820195403c28002940401c0400007880300c0d000301ca1f0109000a4404907550442e2206611128650041e001b410303158 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 295456241 1250 295454991 295454993
    0x2010e0603220b06031c0203031b040e071106070f05190c0501050411130501081e030f0d0504061107020a0501110a02040218030717030703030c14030907150e06030109020304 76
    0x88000803030298001e00b00d0544075030f00e8003005035501611000e02a12a0003c8504016010b9002e42d42160480e0010341c01d40c3e840c500300900c0c00f44c86883e24030048500b800001100c140300362030036020b00e1040e102d0808221000f10458030b4814000c00d88010403c4170902e408440760484100c0b01040c0c0160340d51140944d08030403d449035250a00028440c1d0720b404100820300c40e8850729002404d0781116102000300c40304840400380c51082c002c08180c1e4210400c04242c83d213302410184d803d501c201035908000d6000c0e8407507041d810514141a805031a1010041007007800e204034101c0d28544650a030900a49801081051409010340ca050010800071081e14082c00c011440b000340c2d000703109540c0c03040b020f04084070030342001240b94000c0c8038511001c00c401004144400c8040c801c40015410a0829107044010701801d10098050081c50800c00c41c82114510013503120b041000d000300303006407600d2110b46068030340a00f407404002407c08020718583d22481128115032051b100581c0740c2d212 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 295457491 1250 295456241 295456261
    0x6030a1709120d020c010e04090816050a1e0c05010504080606130f0e150a0905150408090409050307230a0224120f090c22060b0d020d05090a02010e0603 67
    0xa214003002d003600c240c040e510701c0d040c0e0010302400c410400380d8403200d65090050900055075000c0900400402c001d0020300e00a804000c1e00c19900d40c002e8084540c0d502d80d03030310380c6074a00c03030041c480d128507141d4010064280196503d42c18000c0c00207180035813800d46003102d05d945840024000f00c0c4908802141e5150700c095a40021980343d0340c00f00104003c00079a1511742d510304060705040d003201f40c0200060207104192180060054000005d05182d51100072170b6002d214004104a605a030144042c96003034a440c4129040103210b20000c681d60042c0f400c050358020a01d0306204421842640e040409810214100ca101641502d80300c0004603400c00f0301424a01d01100d042a40f80d02003000010101d43c820801e00415900c3d0001d5040c0c0c5684140645605110a601d50080c000300084112076400c0d401c900038243c4600400660035480e0242c11101e6845a052100119004181890f14003800d11a031030300b03c5c01c07103001070011076480d034000707004001d070051000e02c03811002c400101c2070380c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 295458741 1250 295457491 295457509
    0x605040c05030d02010e06010503070608010308160b0a0605090609040c0b07020a030501020f0a23090609030c0a090f06140a03030807051b0d08010902070c05150403080c030301030b06030a1709 84
    0x780003400d4800124100c48000e00a00501d5059016403003080000105400c01040e40c0c400c5d59055a10800280c2c21500c40c40040d03803007031000d480300f98265109000071404c100c01c17840c000c00c041c4101003646442c0c481080400c1c10b010304030310700c10312102c81408000b0780c000c03000c54201c82da4046d20586454041c0001001c03901550310203031040d4000244038203462590b500418041c10745403a0f80180c10801c01c4d8010058010b140766402c1040304100003102e0303140260141902c0384009080b280e21130401e801052180000da0701a614554071003401124144560185102500b0f00c1600741041e44613240c0020300c0540d540c8409410f00600c580070590052080c021280381045541c11004076415641c1c0175580c1e40c02e528007a03000100c81d0400402d00c41ea4074000c450f0510740002501501f6424141041200301d0040b4800c00c4104040000100052030b202c0944005030b03440c0090743d165031560408a11102000300702510036002848000e001030012014110308880890400d910352003000e000c80e982e42 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 295459991 1250 295458741 295458749
    0xc092408060d020402070f05070e09031c020d020a020a060f0905031b01180c030b070509010f140c01060909150c08130204140a020309010b01050c0c09042d05010b0105090d0605040c 79
    0x940002480c01c181f01d80250311074000f522440c100d030907503039070744580810028055a5810701500100480d02020360500744500341d00503490030051070714200c3e015080807a0310081c00302c4050303000040024140b01c524880d900c24011071071414000b002065030340325142d07c66081c0700004030303039126903180d60000250f0118100080f0340b42c805a080405080c070351716080103444101c0f844808880003480491160040c4c4d20103144c1a1542180c0307503044607068813116401d0458a22582c030901840040c100300f40180c20003000b12000014a5115a040100f40b64444d0551500701a0a18400d412225845080d03903500104501c4042c2d103e04940c8001009069a80700303201104000c1001e004401e50750780c1c021402441801d0081198071401c000540d45030140070b4035040e1070b401501c2082c0090604c84440340e4000d100b019110942c40001171500c610706200c3c40006c0c1545c0b0001889002c01c0002d101c0d14036401400d003005400c0c845080001856040d5084008000c6912000480c0400109a070030340090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 295461241 1250 295459991 295459999
    0x908070f1a070c0303090e090a0c030201050c0a0c260f03030601110a02041e1b050904020a110a0f020102060708041106070218150a060c15050910020c010c092408060d02 74
    0x11552800c00a00003c1b40e400b03501d140c01d40b500046003461100140e00c62034a0350180d42d0a0185180d500159016000b188822002c3d01410241000048004140030042c00c5440c01c140c0d00d0394036103589014180388651b1751211541c000b0958980e28200042078950000003441c000c2130a00303588440906000f146480213400a0400818200704206013660060028000304100b054100c403004c2040c4441501000c1000f040d0100020002810300b5001031111f03e6041c1009140c8240c0d40300c0561900349841803d403209124a8150004c560381032081c075800125a00d440d4156040c5504c43c082d8181041440c20301c0b80e10002441070445d03c0341e1051b21017141c20201100803500e0310080039110704194525240c481c114800340441d80a000b0b10340507440c207800c500c88040c020910046c84008000150400d82d991080d3711604100001900013424514152000412505080740c0003520700c0f4079a421030a1005140c030241d0202e5804d01074610ad600030380e49000ca0303a036280c91011034400c3c00760340806500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 295462491 1250 295461241 295461263
    0x702120f250c060e120f070305010509030406020d030c11061503060702030c0a08030402120601030f06050f06060d0c030612060506120c130507170403030c0908070f1a07 74
    0x40c6850355005031800da07070300d100782608112800d002452004014075008181c020a0707102403020b035104200e9182c1026018025180c0420744420242c508140800c1041e40303540001d00510030800280122900604c00324002c1d401c0034200b102c040d46400406240004142d40c60000c0407025116044024070184010162141c0c0e040c000c01f184080c8605525440c013a214000c0800c020307910010444070501c0100c009004001c560b655118019400540207a03070242c00901d034a940b5a00600074580250b01c0783d0b0000c1c0c840101d519250007070b1500180700caa0000481d004010072900c0700c20403194500e0301e02030b0006449c00c1d6200142c000f4011a0000304410003d00e91241c00c0113595030100380507807005c07940c5041d00420b4522240e503483ca801034072500074601c2c85080c032240440b40c025a81020881c24011840da6101707040344807072442100c05400007a00ca1032000700301600305040c038019080d0700c0041c180c01c90501411600519007441013240c101440417000c2207032240e074015100100d601800443c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 295463741 1250 295462491 295462507
    0x4050f0f011e03020d0c0f1e051804060e09061e04080904050a1d0f0c060a091203030603050102070b1e0906070f1202040b040e0a150909050a02131a010503091005070212 74
    0x421010f4075140c4005c1084040741182442c0d001010b020703076101541c2c40c1c5140075003101680042d0003a402b90035402c035450f80b1011400c01070b01c078140d51081c40d1510041460b490002c00302445007126000500f4014000fa0602002c03503400d02c21120700340c50a4401040c142c4038801c0800044c40325801e04001590b4202c81a610f119001c0f440004200314081100c0c80c161110701000041d100780016180412060941080f00702e000300c2c01000ca450090500044141d602d0711001d09981c809541200c05541e0101040b06865450480c0300c032584101c80c4489481c9000213180741d42d00b9000d0203200a020351420000c00b8148035062000020341805030a5465030303603800ba0480d1641150103035500510003000050746403100da1207040b061018082c400540940b42c66102c0c4005c21400c1700c01d40c0e450082c07400c030801503190012038440c00404041e0001e014007036240312003041d0004a8105040120810034040d50650000c0c1d0040030100a150015030358580c070009034504101c3c10041c4040d0407001c0f070402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 295464991 1250 295463741 295463747
    0x402060c010603150f0b0d03031e060306020d0e0a0f0201030e07080a080c010b01050322060f020c0c0a05120c040c17010f05030709110a0806011b0804050f0f011e03020d0c 75
    0x18200803501c030005d00910340788000010a849400c203286800c00044201030021911a80204010340d1548041e0b0500380781c044100c46c1038958640058601640008182c080ca00c418480d1110741164007003d081400c0c104c1d5a4403e2003100c581e806810551100e109140c12101808844010030240c0211400c4420f40c0c945500c4940001000d20a10b507e46529030b84554007950031603100d809080303600120502c1c80382511109500c2213400380c3e086031b07031a50040100f105902c010b00441502d0402401491039607000c122480866400080c050407100c81007040c01180055001c0c0340042c100c1d404100081c9007031048581403110070381e0b4642145104000501c91000c10701000c180c0340c003681079860311074803415400203071a09047e00011004041080c83d02251090340001d030481014035182e4001d1045031640c4070740c0070312040e090341c9603400054200002d01d412400340d44001c4040c1c508580982c00c0c00000380120b81c0e1100c006104a0aa60315a00a20f01c40d604079030664402d201c04101814483d84c0c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 295466241 1250 295464991 295465013
    0x20105090609071203230d0f0507051e03190908121e011701090804090c08241005070209161b080a0e040204090c0225030308040b0402060c010603 64
    0x15480d8011600440d9150b0300120764038042e00d00c112401d00b0180b04a5408851031002d420003a41c00100c01803505000d00c00d25030003001c0c3c140d0044804244c1d0321300302c941c0314100c0741e014124409000c02008041800302020500010210080b800d050b01c035541c00d030110340d04a00804002076a035240c0300c8550104103620300500001e68403c0d518080307564510305105001091501155222000d00d801040400d030100480c41b49031903168008905502c0c076580e44022508541c00400c1056101d09245210544c004602640031800740b1281c541b036094500c812591f111460550381c01800045001c3c2c1d0898000d41c201c802c0207501620380170321440c0c084840d01e180e00d4801680000100850900300381e41c0c0c0c80f00908070820750000c0440d868146450811754002d140303610352582042d000d1200003503180181c8034221031540e0903000b41100d01441e140c1c0c501a03100306116032061761039210040c804070703500056442d8480d0b8400164640d940b29400000c100c1e0148410b00400c640c20050081300f040419a04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 295467491 1250 295466241 295466251
    0x130f0b060f030916081506030c0306040305190503060f09040f080f0304020f0d02010215060a080f061602030703091503062303120702012f0613213c020105 68
    0x103444c110301110120400594242c803034028907500044694032402e80b44d41400c1c1e0052001001c0b10010502003000c06d0078810100e60690210f180850b100c001039003ca2800740034286a860940e2075803a01000103454070401c140041d000303440c010700040030403103442d800300e00c40c03a0040079158603222001c0c00755038943d008880480c01011032b050744880c0360030000088107103103030b05030080c2080002242c5a4001d0080c01040c15902c1001554001a01c10003030003540d00c403559040151559250015442d80990f41c00b0588604642c4104202e001080d40a41e4600940d01d0302c6003d40007100da41d10b422800340c00c19420480e45d442c603404007549030210141080c032009500350203890000100c1101180940075140c1d0280c0402c10032000b1007007034201c00402c0c0311709401c90300c1040c00c26100c01490710b1504c00206c51294060f4554211801032010030080301ea070900900d00020840072500000400010b10425030b14403c018031030105d806400c10403e024851202481d205200407814100240a8402911 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 295468741 1250 295467491 295467493
    0x231209040b0d02130f110c0c04061a04170a02040f02090310061202060c2d10090c05061303061a1e010c1401060905040b190b130f0b060f0309 62
    0x5401482410400740e01c4580d640c001307004c88a00d40e031981e009805000381e450020509a9544080c6081c1c1411030701401582c6112002441d401490500f40800c4410300c0d040b482d0b13032020150000d4400d082a10440d010f54a0070303984007102c1411100307002d151290140d0002d501a04003500039088140c00d81c01391003400303000c81c1281c0003c030078000901b040b00c00074003c022042c01c1c40b680302005414800c0041c0f418207110411199660300b00d0f4501c01903455980d005030040002140394850121040045600c20622020304000080c0c00d661459120710080c03188502400d408030714000000000d400301e0004542010040c0110000e5001125003114054503203449034a41200b000e07036821442560003600f542c1a150144500d4550321070300110b90300381030070720810b40d00d4680100712520302d0300800740218800c015409040c100042e81c1c0c1d1044403030f001044151407800c0f503280d01d15030f82c52290800c051160000050096400000b40c0040e0503680d501c40e070003800024010b803000214400a44c0714280340c078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 295469991 1250 295468741 295468751
    0x5090c1c0e030f0f12090706090902090604030b071101090c050a0b040f05010305041e03021b040203071e03060816080c03121e2a0613020a0323120904 66
    0x90360540440c1c180d201c03407540c41d41c02408103841c0d04a50781e0040c0048851008000c1c213008240c00d00503155141283c840c0407035000b41e602000001c0e000340d103c0c0044e141d180000d42c1800d80c9440851010b01461102401d240f01500101f40d295004e20f040802c00040580280a40d20017424501842c081d58400c1500565081c000000c0b0a107404040e0360a0310740381288903403201c2c174001c0114042c040c05082566a940840134842025440400c4003200364400d0300a032855a44101d100d24041c2e140400240c040e500400401c1011030f400448161407010300f03c100301a4900ca0720b0704500905246e0000c2e0501c0c8070740c500001010a00ca03070103008540522040700d8019401c002850b4480181d40c030b0800c04e83c0703030501a101086e8046505940d030307401c65100d0503042c05007427808645644211f0002c02d00035040c1c480c2d1380c032401e5410b10901b80d101401c00e00b08051401c030f6a000c1064450148000b520000603a1654001d100341651070b40c0c4c403105848100da242c051100740e022459440800c0c5503101c0d074034007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 295471241 1250 295469991 295470037
    0x105010e0312030406050a110d05090d05040503100e010e07141504030309180b040c0e0f04020c070e0411090c0a030e0105070503011215020a1106010803030402030a03051305090c 78
    0x2907020030020807000910b0860b110f990f200d0003d4403001d84950712154688c20000c40726150f001c0a000f18000e01c1d031000c642410215200c904108808400000b0050100400c0c0501d4900045d0840300850182000a611500e00d104c1801404d01d0b40982c181401402000228282540300c00140c1d41c100f00c50546040e81200d82e002c1c0144260b100003004a00824000c000c000c1103c101204041c0141001281810001d000a000c48401e180ba42d0085504518210301908242c24485401072095808515248500c5c120a6443d2514426441e040d0504000502003000c5100600703108036001d0400c00c2035081141010b10250040e4804400003443c00f40b4008080d02d05010361802a00c3c01c1e02c03180d00c1c41c0d08100344545030f40c088074020b668101204c00d101d000f1482c18401007400c0080e907034503a0604810a1074071414810182d100c0c520035032082c8140700c0980e8012071010b9480b0740c103007885540d9844c0c40d00c40e201d40085603441251701090351810001c0d00c1015900a015038541e24240090f10110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 295472491 1250 295471241 295471243
    0x1608030a201201170a17040503100606031b021b01050d06080102031e01060e090c19050301081207081210181a0108040b180c060c0102040303030c1b171b060105010e03 73
    0x182180b4404d242e4840303a840340100302000441d0710031100c8600e11610302a150310210346807400034a114681036a8580040059581c14400c081592004a16060869015490003559114123000703900d072403030080030340a00c2a8000c4044031064400c00c40c003488404e585480040c001c0d0000c55901c1382800c8a058030010002c2c0403141a41a902c1549903940218040c10900269840061405902c11810840e1040e05550000b86004108840d520300355030f0b46c107058030700b810414000c083c100c40e58824007048000842030f00642b01d603c0c4501c0d020030041e56803000071015030301256001007200080c01d003020f030148284ea00202d02c0c0c1e07008046180c44ca00348080c01110101000c0710003900c200d0940c40440d5851369204810000004001c0482d0404080b20300001c400354071048400c0380c1c60707500003801c104040e018046c1703541000d42ca090444544485d6840c500901291034002001c010141985000d141081000c1e02e1620f100528440140304c19844d4050b0f450200380106400300351140c3c4808a1450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 295473741 1250 295472491 295472519
    0x20717030121050d032d061721070c0e010803070b010b0a0c0605041412030609072c0303070803010b0706050a050c0a0c020d0206070b0109111608030a201201 69
    0xf0780031000b03100710a99848120010700407507051806006c4428403401c01c12071910002640d0398030703040c00000c04030301c0c24000701004440c14003007149641210701c48800480744c00d00d0309003820340c0c0c82e03516580d580705600d0321440541e2583c0190134600c8040001180640300000035098482c450014542940d884480c540c125018510381400040c00790744002c0c00041d40358000300d411038802d803041c0c88100b44101c14207041003842c60441d051040088100401c518103074074490f402c402182000c0380790016000c0da04080d03100c086d414542a035000031030a24207803010003c40d03801c02d0300503812689958462480100d07079400035100741c440310308040200e240d84042d4480c00e4005e44514058501d080310014064400c1420074005030f920105402103a8056200c45009102039803145903895019030400a8a0084404810a10341203800a000444024040c4001c8001c01e5030031020140d1259030307007414503002d800c8611051941444080128421282140240560b103a00d031130441c4882e0380740c811181c03c2d12 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 295474991 1250 295473741 295473743
    0xd0602030c030a29041d0714010e10090b1c020d0b030d110c040b0d0606030803060901060903020d0f1e24090f0206072a091119050d020717030121 64
    0x1d409581800200e01c1c5c2030b44003541044000701c1d00c6c0c0c3d008418484450500081d42e01c90f05c401c02e41c014210500d513a0042910308000360448902d040c1c00042c040c01006c0c0001c501403640000300014451545150700340c8034041d017440c10304095607200310407031184000d0000c05d0038180c001d20a00d6140142640105503004803541074200604030000040104000703001444090340d0000007000102d8042071842c01081d0103540140c1803aa941d0034040240858400141d01c108104649003030b0500050343d415285e602c5454002d0102d0021f01c96900f03110001060202820301001c0000c2d144408001045006070b000a911001043c0440d6041d103180d4103070b881c1d00c2c40080180000c1444540145490342c050548180035802c48511106101015030040c4402000407100d0b651200c804c000501440c09046c80b000708a2010500300304810642c81005c00704425182e0900901007014850006603a0503100003a4008003c1520580302e103995901c554000c1c0a4410000c0d02c8002c02142d070b40018503c8540b00b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 295476241 1250 295474991 295475051
    0xa0b0a0c0e01031a0f0112060f050f030601120f08190207090e0c0a15020114010e0a1a0105030703091e03031b08010b22051f0e010e030703020f0d0602030c030a 70
    0xd148480c4c10000c50132501d610490501c400104a03090941507403003580050102e03905a0300c50141440c0400c2b0812100c8050a44654003080040c401d645541c1409007140740e01141c00c0003031f0503043c13070718071140e020b000200e01500811212203108581e000480c00215400d46904102e8030500030441522185025962070304622400350411141c941405004602c0109200015414140000d0004060802c0e80700440c0d02501506002010b98507104043d01d1035050003950040390001b03030000e03002d07010040c80d540a05070384440c548240a1804407103041c0082c00a00b0000380c1ea05494054000d200b2080e0b001c0e070a491440d0fa09500c03501514071039050750708100342603043c0b4210001d01d51650700a405041e488403040040050b55880c2d01e6100c00b015502640c4900046400c881c0c014950014000303520304000a01d50310101c07a0b00d0100308101900d4055072042e246492034004111116000a001001c80784000200301c51040301c400030758014107481005100d040c07644a000c107a0250140036161030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 295477491 1250 295476241 295476281
    0x3140a02070b2d0a0905030a120e031002040b0a0801090902060702130608070b07050f070e060d080c06040602090901080f0327031608070e13140a0b0a0c0e0103 70
    0x2c02e4507490142500c11094600390304a80d4005454020954103050303900603410000c00d4085085170402261005003006074010700d1411802e4440c005040706000c04e003007e01c08815101c0020391403d0103030b10701100740750905540e81c954501645200d6071200c030341200001e900070b0000c43c8000040c02a0025650000c1050f420981d894003000003a40501d01029551603540c80d000038140c1c0e0a028500c0104203009001d51100b000382800d500384410f5400c01101e0341c01c400014810390402c1e0341c03615001441038990030145421441d10901e640315040084200e403082c0e204000400070700360000c0503401e038160744640c1b4590361455030955480b51264445c0880d001170040840d81c406107040c103040041c200f800e41d4510401c41e00801d04044015403d000c0780c458040050080c40004c00904d80186070064444809142c1417261100e9400c440708002c0c0100d00c5a95541043c0200b00203009019400c18085021401e1010340e0100a2401300c01400100b045040344d0440307503000e0300c11000e502d1441e11070021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 295478741 1250 295477491 295477499
    0x1090b0a0e0c0c2a041d0a060c020a150221090a06151e08010b0607030e040b2403010801050f0c030601080402191e090207020112020306060403061803140a0207 70
    0x14064100070084a5240304110820000c4061003028070581c008284c0c00e600b003c0301e601c0500c400e8450200310b41c580e017407100c070f0300300c5020b00c00241d0b135645503400440c00111038400341012410b110031890060f00381806042a5448600c20380d0080500c2120b10341c0d480d0b0b8100d40c028064100c501c04841c18080c0307030080101031020071459000311401c00c640003164a0415200c0c059003116a4107010358040d451490381c000d21820b0802d21420282400032100c441c01d148150f83c005000d4203850b15164026034440028042d152500e03080b414040304544901000c0c81d141c101018004c2e00240309440b150f40c200008506100320810f140b5005a68220200e49156184801580c031200e01501c203d07000f4124442d5103000c1001c1d024203501601c5c600d03100244086c419004914214000d0700310911032071040100000603a04029524107036081041d01685a643d00000a90a070040d61700107401d940c248851301e91034180740559100c030544240c64240c460107001282c070000c0d0254400321005030b401008140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 295479991 1250 295478741 295478761
    0x140901060212090315040b06030d0816050d020f1b190804050603041103030d020406110c031f020904020d09300c050a050318030d140415050d060e01090b0a0e 69
    0xc07200620141c1110b50425440500075982c0b05c00b2070701038076541d103414117008032842c051050b03500350b546d02e02c0c1151003420700b0503028001030307124a41c581c203104000038940001c80d01c03501a00d01000e0026091a16103001c944041d8400c070020518111602800b41c41141924042440054450b0000b03119420035042100b40a502c1d0300142040d40ca018620421a2481c0d0341003009010f41d80c0100340140e10b40c0c0c944200500525900c15411416800100e00100c0d80c0e1000100b400504070007083e02b00700c020000e00e030311009200f210707c5203070001c1c0001804154040346402090a8a1184c0072000607285802c0c20b040e8025081c1c001c00b44201c81000038200d01c0351080c04800300c0c8a0081080d283d031801656104ea24550101e0018a54841c40e40107160103890280300700d0f560b07010f07241172160480e100c501e4801b0280c400d90242c910004e40c041c59180000d0b1141c400d46d80c007208c0e1b50304100f0040343c0b90040201070900034401d00b80c0302801c0015160907418410034041c02c85100c09a016941e440d502802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 295481241 1250 295479991 295479997
    0x12010311010302120a06080f030c060f10030803070f140c10110d06081501050303160201141908090c12030304020904030507080a03020910030924060915140901060212 73
    0x801d041580a0240a4480b1a00d080d600d0007030380b00090000d4580e140404160400040b60020080c0c0d410034400c030013807500080350147c1d0000401c1b50f1941d1580e00d041c5142242030310340e003000d044820048100505290441c0038046910403503110446410010300480034980f10710000d007240b40e0010300070080c1002c01900280d01c0c0c0000481000d00f80002c0514200840d0220b41c4541941d13840117103c1a0301c140e009003801d024203000e40c09145411104104c4500001d69010028100015112044843c51000007648e0252061600c144045041c5040c010100c0313009a529200038000e050003026030745400902403880b1744181c805942180d8841c0c08105c5900c1009101354207220041091381c1c00903909400814520496440c0140ca51444805020822150301140000d0600c0c08141902040d5000304682206403001844c0705c403070480a5044000e00010380c1b01001c00c5003000c01310402010303602c25480a962075006100d6031805a80b04120a0407020700c245405a0011140510416489401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 295482491 1250 295481241 295481273
    0x2100c110d120b01030b15030421030203090601080c03070911041d090c090402091303030b0909071e1409040f0b040b01182a0e100c0201080a02120103 66
    0x145000001550282000d00c000c941c000010024000300c8514a100d11650410940c00c3ca030400c2408030308404220803500f80791a0344200701c0040001420803021503040000b8003000e01c43c44c49103400402000d400f03034200340d03501d42290003003100104204200013580140b6080017001007803200d00e080007a00003000d0340c940908040000708004960021102c5540c2a1410004000300c5145030214805050001c1000c4040c4110b6410092202680d1044411504450320b503550603401c0c000d034501940144000545140c10206400070004008008940c880c1144d401c0444680020b00920656801d40858001d4a041101103424540c0c5410a80801c0e036103d0b10410181c0c2c890b0034261039203003140b6801c880c102c82c030300c0d088001030043c5000030801d80000c0344140011703c01c44d90594511400c05c00850b9170102d81e05903c3c800718811a11070300209006c40340141c136240c0090030340076006108410094060740490320403000326010b85613a108690000513086d0807900c40749d0031503a45a0001c3d108900c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 295483741 1250 295482491 295482497
    0xd1e030e1c02130f09020901030f0506150a0902030a0b0a1509051c0f1707080301060f02010b031506040b060c010b014107050303070e0a0f0e0f0604020f04060201151502100c 76
    0x22445e001600c0d201444e6000e1030151509103880c0c1d94600d40207180c030342d00400e00407074030442000300741980e2105112001075828031200561650f441d001000c004003051115144c3c00b04e864040041c840710a00d9440078840c5a1b507907403a41d42604c450500003c20407072000cbd42050484401018041140d005901440a00c542c0d20802e407000c180c61140103540100c0740540e0f43c00c40c000b00401c040c580011000a103801c960000b0302c000000030000035110003420b600d110200c810300c1c0010b5840d07075840c0e03c03203901035000401c001d489030002031006000345020038000f404101001c25500701c409908544082c40f00d000e20011610f280d80046400801600c101441c80d00303842030001100050007131010b184500d1159541c200311003003070410407586440603848510410078102c410701041c01c40484c42a808a0024070641c1c035515410040f030003d00c1212012542c152000c41c01182c01a41034102101099001e01102000c940740c903c2d105c050b440b4444404013581c05078840410001c20340d0444014289542 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 295484991 1250 295483741 295483751
    0x20a1206060b3402010c0b06060d0603050c040c032007081902241e0606090a0b070c05030c060306040c0c02090907030309080303070207050d1e030e1c02130f 69
    0x140b481541080304040020314035018020044640c03101490001007100340a0303030380850643c0000c1c100c0e00c4070f9a0090320242c10100010025200c8000701c680c01c8613201c1040110380c0c0c5d41d05003640c035801d107026040d100e04c1c1440c1111100c540300b40100f458006082d104250001e4070340b0008506903000300c50441d01c1c0c1105004841e00302c060943c1d6905140c0c021380140c2100750142c1c0a05c9a031900500c001440b1082607404e0103040d0780070042c4e0b07106850003280d034500720f41c03a50b0b4005461400348210b11544030a950b2001700740a1035110140801d1440307940d030344035513540321400c141d1a24006004660807030390134400200c25160907003000034201d04030300707220407081841d40104031024400c032640e01d00b903440340404204250b4413a024000a002c1e003006503007181480786000f912400580314051248501d07003003a0040c41101440d10460805071014041d586407907140151086001c0b02e21140b00d084200b006543e01503d005903044000c1c0d0040c00d110090941c40101d600401802c0b460312046da0382e41e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 295486241 1250 295484991 295484999
    0x21040f06090606050f040e030a0e130f0608120a0509040b1c03020d1107031703090f060a09020a081b1302040509010815011a0a0c080904020a0f020706020307020a120606 74
    0xd40701c0c0144850041c00080b4500d030500c401d0181096442812038000ca00d442030b042c00e01c000c00b00940300300305402c1c0340038803940121000040c40c0b1780a08020420f00c03403416160080e043e409601c540e00322030101d02a10260751200407241051700072242610003260701040700110380c1c50140d001103400d550040090502c0380c10b100c2c0c200050905110103c0140e1b014030300c2601030303a0b00800079610703030490038006211441c10750360b03111001c001401180c065020003002041c0c0e500b406100303c107840000b4800b2039850780b8209180601810070501c05038080d01d9040d4011504040100e4003034045264401304a214200c0c010610442466141000f40324590030b0002107810744d12843c08900a01c40840201004100c8001c00700b8400010f0744082c1c40f40660014540d5500782c00360680b5000380700d03401c0c0403608080c2c60070306041c0b1f403140c0710205611610010b070b0700710a10f8103c00c21111070600ba40c21680e04540b200c00c1669039205091010313501a90088041010030f003092091034201c1d1040d82c0c0800c0103595 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 295487491 1250 295486241 295486253
    0xc0d090507030303050c070f020607061b090510091d070e060a0e090609160e010203070605010b031006050c071a0d06030b0a150e0403030209030a150204060e03010221040f 75
    0x4000044405800c10307007080082c0b59040c010f2580059800c2c16162074001140d6034000c0c4039556010003801060081581401d01615503c144401c0b00382d04800c0349a0190301758020070f001054010103100c0e844400c820001944a204c0300001d882500d48030b08042d042e0320400c00c4c98a14000c190408000d60000400120b0b141d0030040c02e8a40318036158400071003031403010007480c008020000750003510750104100311107005801e0003c081c6ea441c00c02c00ca20110550040f800d41c03040400103028281020000103016003000011071003000400450f200301510380382c08031102c0c0710b03103900300840744d02512060113420130b54140d14100f454050700140c60484181c0001054442c103a0041c1d510010b16010001001e20501451850000944052559034100a42c000000701c000d0b00c06400c040c1c2c0891100c000361002c1000d049140e8014100c040c032101c03c0d51b0244041d5101d4002d50000510401147c0081e044c14002d607240c020030a034100e0b1040316043d1103010b003d1401442900c449802c85059004200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 295488741 1250 295487491 295487501
    0x90d02030a0c06090e0108030f040506071a01060e03010b010c05071404060f06080105130501052b020904050d020c04061a031e01030515090604150c0c05030c010504031403010f030b0c0d 81
    0x8195212420101d26041703d880c3c40c0c1c10160300c03e01c181d8200304184003414180700300700c40a94500701d0f04503413151341c94200741c3d202140ca1003040c8a0b6036500000801c0e00740c3c2010041c03124500403002880a14890801100c6565010400906641c440d207018000420004000703044040080d000080841c0d803035400745400b200640c4204081801500140410300b844280343d1080070718201c09101c1945010081b81e540c40b0b490b0b100783c2400741e41c1c2502c0c107618180840420071554009145204a04080c144151030b17006d10401e0f800036104004a40a03181002c0c015078080706d040d00e0000383c0f00365001b44e6405080c1d000424070b8988800040480c4520684c041c01b0034040c50160300244216096400e0580007520050b04d846069800841080006003c002614000c1c42802c4000b184c95044250309917000d0b40c80f042c0040c00e0b4000480c008956000542c01a4420350096481c0c880813040c8540810740c910003030055840c0080c2d0f410050004c600340d030a19a4000c844918000d103040204060f0074200c80d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 295489991 1250 295488741 295488749
    0xb0403120f06090504050601080a08030c0703050c10050a061719030e090903070201031d0628090303151202011e09031202030a0206090c0d02090a0b06040f0305011b05090d02030a0c 79
    0xc0d0355113041c081403100800240b405402540000e158100d00c81e02c80c0001c40c00018641d40d8045400504001050b03c55810b0720f5055545400f11200007092480400c050441240c0c0030070a20710307000c000034201581e40d80910601d00c0300303006800b15401d046001602440c50160507810f02440c90103050554845000c031a105401b40383c003542e01c0308182d2000405561411b840c0000000b459003100d654800041010340d0849154140095141486030020b503038450441104104c45243c4078425041c036425402508403104100d040603104c0d5118045510100a0034801a0000d5100c40c007191f400c0f101c610701d0219404990030324082103603895460700341031807120a0b42030050b04040383c40076450341c04001d45a001550480500728031500b44020400140ea8400041e200d00c130000302080581c01c0030350180c0085600600800d070307216120700143c1070090701488111030542c6070001840500742000d002da041010240d4a251800740420100003042c0304482d41645d0502610361114002460340c92644024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 295491241 1250 295489991 295490009
    0x30b01021f0921120b030102090a15091a09011b1a0415020f0a020d0905061c02040b0a0906091d0c030711100f06080a02150a091802040f120b0403120f06 67
    0x200c54403541c0d10585e149030184a000303a0051002518070360303610002a05039000014641800c8240030b00840b8a80f83c1c0b41d210080c18804035204c0441d1000d074030000c01c0d65100a807a1404440061011224a014882c801802003204150000c84240c2024070064000c1d00800c920744141c244407500c05d00320303403001d0f10740c002a000001d10700104503010302060000449a06065411900e04408030300244a6080301c107100720100c128650a0300700560541d0043d00380c0394051500c033b010420300a80f5024540c001c000102c3c5400c500002d0030400701c20441840280d40901507400d4031205854071158001400385414811200300d40749001108201c401034840d43c4800109004821042030703c115100d5812040d09a04091038000151f00c5012000500c00c00c00b407040340d035038012030108451034241d40d04103207400f60010040003000501f070b80182041d2031011060b000039503594440400285c1d08480001c242598110010340400d001c0c594aa03000c0d816070001040940e04589500200d500641000302c038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 295492491 1250 295491241 295491257
    0x12030f030c0418090209010e1305070806270d12060902070b04060c020d0203090618130912110c0907020c1215070507081611060d0c030b01021f0921 65
    0xaa20320304003c6110220a0000410461000b50080307003e10405000700340d0998894804600718011400d600c04901d6000019a500b55880d02e0515840305019200d5100c80d4000b07110b03402c0000c903280c6004040c0c025101c02801020414042a611400c0d00c40380507283d00e5a9400010b007101441c0002c0110718400c00c842c2e1014905482d000c01107608240b65002154048281083c015400100311000f442c03007242e0640e00c94805c0d00082030003407035003a075290300600425040c10b8a404540c210428681c401c03010900d61200450003164209601040c601c03445e4082d40da017130b0080c1410305205401164900c140c81000381d0b078502007840e05500800c00702007a804210060010300c030225007117420500500d0058501034041e2503000882c05041c08040050030129081020402d4600c00540e10700e50161003c5d03224280c03a45244000c0035107c2c140d0010900b0030310080c1003988040b03002458042c40342d008451446003a0240c1e0300400d2044402c07528211105041405403904200b20f91030b0400c0c554031486 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 295493741 1250 295492491 295492499
    0xa020a05011a0a180f02070f030809010902010e130605043201140603070908060f160f050f09030102090a09020c12040f050f03153c0612030f030c04 65
    0x421107250151842c070111442d070031810183d5440c4050801c88140b001c0c001040128980c648008010785086078201600c00a1030b42d040003000e035074011026010b51508401503a802c20810f081e250210030003400291304107000649890101880040c83c0081c001c0060010f03103e4020504845400702800d084c035080d046903024210320518031286802500f0000c10041d45402c81c0f10b402d550107200e54600c554804400522254403810a00703005184031000c035001400c00c0460003117680c2e019110380356082071400100201d1800344030340c0096001d00f9668140b03029015042d00055400459220354555003c00800356181c0d41d01d1400000386c9010400165a0b19084a100f172418a0000251804075030078001040140900030302581140c0d0140d6004c190841c000c00040e0038000fa05d0301d44542040700409000081100004614500b19001400b001710950ba1410901c8002c0708801400503000c181d0004a0354209019100911a4444100c0e0b007494095000800581c0003168400300c0340c800030030100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 295494991 1250 295493741 295493743
    0xb040c0504200a031d0d050415030c080a0c02010902060c010204140a0f0e220c050102010b031f0b0f0d060b0307090b06190e030a0303050f07020309010c1101030609020a020a05 77
    0x1a0700c40d403a003201c614240c0c081031000d12040c000c00303083c1014940d907104442145404010700206141e0301d801540e01060b006680901185c1090168145c06841c81d441d1481443c040d2007900203c00c0f882c1c407501190341e2082390000103807034040701c0d03c2c0840d502d179901000103880d01005409040e510b80000340e102d60070b040303401031243c09014096100d020860410880d141c0105003c009072091040205a00d56075040c01d20610203040114590700160145a070080c0446800040240d5209038002d02c4405103803010580d03102a040381040d140780074001460a485c510394045200c401001e4100c0f90800d0140c40007c466130031124065520b03540300e040345641417805010000250011181c02c01c018800140403808a008054440c51416010310701d0b6070131103000700c02001d80c2010080484007007451620f07004000e441c054130321441000e440d4000c600082d00100a0716614113040e0340e01503041c101d6440d200d0541d0003242e1001c3c12f16550705004124420703540002d00c2c5160307a41d002801c0b041c0003842d10ba = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 295496241 1250 295494991 295495001
    0x20306060307050d0f0618050102130501090605090d02030a050f030408010c09120822180f020c150c090d030309030e1009090c0207080303040302070303091a07020105070f0b040c0504 80
    0x491007500454070611550713580d41d560714501608040c01d0f030a041e00c40d203404030084c24000a240c2c0c2242c41d194903401000015001440c0a1130f0b040c01e00c044240c0c0d10340054907060601c0c0203d801103139081c80301c480b403400d002c1c0d61004607a000400304e940c0e80c0d5494030b0700c504024107255103e602d6080001c090200200900401d03000f04100c1c60305a523a0352074405038003031102e24cd2030020011031000910110100410852840d0881e01000b90340001d40ea0b5100e005105400c40d0190860905000d202c4458a00a1003550f2110341c0c07001c00740002d1440380d0880260350304000c1070300c08100d50500c0843e00f1901d8500951181074480d44000030009800c0c1400340003c02d982244500c202020508298a41d42c80440c0714119244040d000ca408107540000380d0030402c0343e400681c102d03c004002c010a041d400100070040368000e450b0310040c80e850303031200c014140901c068110829002c010110042d4480c00c02070800d03d005110900039692030b961a141c0c0030314181e400b6240601d02400c01d1216207428819 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 295497491 1250 295496241 295496251
    0x50105120d021b0f1201020316020325020105070803010e010501140901230d020705031e070f02221503030e0d05061801060e0f04030e010c05060a1e1404020306 70
    0x41c2085036181c0030096903200c29003031003565800300310700c00780190311800c07801d5900351030040c4408880160404914000d40044600380e4050101185103240203001104498501c4168801e080b0281d000051158026507403140c100d0402004002150115054102560183ca060740c0003112651515000400c0600c01038a07401d1020802c1201e9680d5a800c00503180019860141d80080d6486420302c0c04040d008500641d1592400020441d00b0040003000414808001c2a80c500383c3c0f080c0e05460123010b0056480007040328442e040c50340c01500c0d1510a10300081e03c0100301c091094901513260f01918141440069039216502d0705200305030300140000d00c01442a0340704509820340e40c648039a6002d002d8a01002e00c0300075038100030354120a4001304060b0280e424812542c1c1043c020100300f0700c804440640010b10f00710f400103c6580701e85411080c40360041d0091581e5240e108541e40141403102e40c00400c08100c03d00031071204c1841c082d80351440150030031109076240900500d4100000181 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 295498741 1250 295497491 295497493
    0x5040203010b030f070e060f03010e01060206060306010b09130c0807030605040203060303070f1104180512130504020a031e021309141609030c0e0402040e060f0a0e0c04060905010512 80
    0x188a42c0b2002c1066035400511580f01581c59100d5042c1540d00c500300b99081600710000180d0800d030105030400440c100da10340741c01c2d40c00507030b40d41c842280c440700156466680764001400402c4070507600b41c040d24030184001c1140051100714030074841182c42503001400414042401c01c030846805100b41ca000b01000d40381940307036203000d400090301c038403036100c008109100c54210b00c028402d654541d0006501d014000308815402c440007640ea0f07d880e800c088849105c0e02070310420380e81c186c00941c0d02101460360120b013005d04200400c006134014910070800c040e038404200c2c04104c0c08050024450705035100044c0c0c0c8809800d18211111110741080c40502d080032003001040284504441e40044019600480c4540e080b008a580d000c065001801c80c0000c1c140204001c1039a0240c00c0c042d030b108841c100b002d0100d041e000d0b81c40301c404454400d05115080002880c01a00da04146440314001d01038503465a14800041c0c1100d0050b0012070b58140d43d400184114205101f8507541c4143e80c01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 295499991 1250 295498741 295498747
    0x9010905030406051e0706050115030902060909151305090118050a0f02010516050601231f0314010b0a0311040b0904090f080307110709060501141b070b040f050402 72
    0x145a10341c0e00e02c00e074070a01082100001e4514030030300d80741d101e06840821244200d40c0c1d0f00018203050016000030b01810180040e5040341c0c0719900c1c024403900c0c82041c2e003d0642420810304904100241c6d00040500c121481000e94400b41c640d43c009110411400e8030000240504001c3d24103421240e0102300270a844880c103184c400403138400141d040a03140d10100e0140d0f1442c0d0761004071796078080d480c400845c0740d0390089020200b03c400304401d4180c07010003190071401100807002d10000d038090803946400c014503079419807a01c4c404000e0808550281c1c10045035900e002c004003c480c000903441507100e85000318136154540c1d40760094112101075040e01314101400c001000c2160b100b02103040d40300310ba40300c401c1c0c5c08224080040002c1550001886602c0c0c5c940705801502c03c0f2105240e003506801a000c0c0410b0003881485500c0954406075111807a02410000310309142d48840f13402030750200d01c10148046020308001c02d40c09080b00460403600e076868040611b00700c001c2600b103c1e21450040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 295501241 1250 295499991 295499993
    0x506090606150301030605060604120f02090a02030103081206030f0709090c060f120b010e040504030c030801090c0507020618031609050106020111070303090c030b010f031104061226130608090109 86
    0x70b0082c1e90540343c00070000221b90312000d0010780d0364840d90744882c0a080000580c40180900024040401030081c1c803000202d98074001d550b1304034070090000404084060202024441c0300d10180c9074810405412038802444000804c0d10305070541e405881c42e551500884000c00400c0301d280c800800b40c500381059100200c407405825030400c1d1780c20f001c0250f9509404c04c040d82c800e246450f203482000d00708224a040906004041582c040400e5010403445c80c0000b5404455208540c208a150360b202410001c06a08204d9598450350b095900005140d103404e80903078043c4855282020588821444546042904015100168001429645012205c0740d0080400c022140b01da5414600040e44820306d1804407640321182c2c20103054000b60500200707034010f4000a40085e00d018030401c4659025081c00c100544a840c0104070035030504284040000b90712038841380d000f800341e0b0321044202d220102c1d141d521b034002244d200c0412245c2c0400300192900001c10503000218079000b440364400b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 295502491 1250 295501241 295501279
    0x801021206010c15060e06011b02010828051303120507090510020f0708030c010608011505010c080c010203090c010f0e090f0709090e07050906010923010e030a0506090606 75
    0x4000c00759818408107608050800400c0c00b0304081d0300800d424104179440c0c40d0742e004000c2a204440c07803404200c0c11040b0b400912801c0040c0300c0d0b41c41c2d05075038042c0d43e951030019460740c200c1d002101d40c8222040700e5180385000f6460284034807614581ca0030001e80c078031504008102e5420031807640d026a16007010300900c0c6910aa01d01c0035500d0984800d0710b440c60a6108a203010001c0d00c5180f810f0062840c081960300010004090b0030710750034001e028080c2c40e41c503035600325107043d1915840b40b24611002c00043d40074903901d4010343e024064060414001140707007426640100c0d1200304580000d5000340c0d5640e000a400980406185800010028984046548140d018000ca540070a5410004002d00e105882c1c00c0050310940200780100c886014496a640c1c040d4004c1d68420b092490008101c4e510440c81142203a00307451200c204c941100410b14501d20000301c800f07041201c0002c1400c82d60310200180c01d149445813008021624001214500700758000e00b009201e0708059131080c2e15003803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 295503597 1106 295502491 295502527
    0x818010527131a150c0618030408030301030f0b0f150f04150303050405130e0d05070c090c080a0c0302030105010e0f0d0b070c05061303171b0f0c07080102 68
    0x141d03000404c0c6050141c4a483d0f81182d0200d00040d03000000c001c503500302154000c00380c901c7c02e0307194000141180d00076002036405003c20f8190303030204a82e080c016a072042040b1195051424010394003e129040034080c14851034450200c84015502c03a40800340d042540c02104003419a40c2c603010b01280c1080c400c50b440f4001e58014030452402c1ca0003480001d58050000c0c2100c200411000d66050304101c40c10b41e0002621035001c51504154442c0040c40f0b00d45449120407841d02060500680e03021100c80d80406006100401c0640d8000800c11043c40084800a607203075280320108880c4503d03014083c141000e500b003408102138015560000b104e0080d026120f643c1d6440103100314815420000400165645034454441e04c400052990810070703105100d500700d4202c00c0100501c4c2c10181e0360b10103294001680382d480020400a0341c0040c02c952000354100f901c0000880d01c1d5803 = true := by decide +kernel

theorem cover : BRFrame.Cov 295323741 295503597 := by
  have h0 := BRFrame.cov_init 295323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 295323741 ≤ n) (h2 : n < 295503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
