-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5526
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:05.426589+00:00
-- url     : https://prove2.me/submissions/63884eda-a323-418d-afbd-c00e49720488

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 993705035 ≤ n < 993884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 993706285 1250 993705035 993705047
    0x30b0f06220909050a0201111516020106030206070f060b1c022b0b0f0a110747010b0a02060a0c0e120f1605090a050a231e010501 57
    0x1030690303540410850030401c0ca07a94000180e0040c0b800341420483c0d00404d0070500d4a4000440003a408130300b6082911803801d200080310301c400000003050807059159080780034005010517004d042159200ca1010000da0b0703441c0000c003000d41c8075900f05152660b00d480c01e1030a48174801489482420f9030304640d10716034110074540304481c2d4112000c00c0081e407011000429000c4442e840001800084103c00801c01324486880c0580300b5100c0358883d075524130b81d039035051b11201c1d0810603404405011031400580d00c1d03101c2c0e003100d011020790b81c04007242c40c03042410041144c21510541e01001c3c2c083c0c040d402d84a41300c1c1b80c003400c0040c00951802041c00303000b81d070f80e110180c085038445580380121815248913000c0000c9102c2c1c001d01c5511111007655655949a00c4c400d1044018002d03410308801d400124882c510444402034880c0c8003ea5030079031640002c0c000140140500364598400898040b80702c61003200d00f0501d654200020701b042c0010080d00250000d2500806003084010b000c540c2e0405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 993707535 1250 993706285 993706297
    0xa0f03020d0f0603080c010e0616080c041502070f0503070509010b03040213020a090501021c080712020913020a180b030c0a0e030d0201050106021006030b150d0b070f030b0f06 77
    0x81805030307032450a04440310092003032224100c10980b07481c81c080100401800207001c00401c0300000d22003002080d8070755407640700c1582c00c40c00400380c8013103005840c0d001d01ca00781e521420102407207003041d90360b07845600b10754894400034006800c4201d09100612a82c989400a0a0240d008024950910000c034038419010b0091645000700800043c04640e140540c24403000b032244803c1d034588a440e500540a10201d01555015025805c5803c428a00078901060200000c0d034400c003460b1920030041da5491008205841956001c014505440d01d44003100900488a5800181d40e07046001c401042c81407840c0762440001001c2800b0050b0314004001d03030742c01c0b44c1c4020381c0c15a03400d002030082e00c00c0300c50041d00c560907000d49400506425010b500c6281280c0198094405c482c002840e81c10485915000007803c0700307091808110000c040320b4140f02d10f54400f80c080c0100d0344083e22909400101141d40d440000c1501420100b40740c3d05005004c100041030300e1041d200414800021640d000310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 993708785 1250 993707535 993707537
    0xb130f0e0a0908070c06051305040911040504020d0503030c030106110307020a031205072102060f0408160206092d01031a191e050102011d061305012d0b060a0f 70
    0x206030b42c0701030010002c11284200c0d840341c214010039544000c05403203030f000905c0400c44000d40c520000741c241001d01600c8511544010380e501030640c1d031401c1000805e005001039812950404202000650400007140114442c1200741d481f9890000e0080c00c5421007414034483d80c000303000040058450000d100c00f5668040c1c0b014003450f41c0d6079012100f074021b400000e04900710080d44044c04072030401060900e103c5950030b4a00c95a07800d00c3c80001100f003a00c00a001000412680c0b580108241060b02c500348010b0030580f40200360310016150403418843c49881140d040d00c0e0507030245980e101d00c540200e0a00302405800c0c126026604002080a0f40c02c0c01000c5500e1200d8541008400d850094568144d01d2440501d0b01195212050201c4c000c0902542c42d051020020401d02a4000050441c0b0070080042c7c2d9542d4107a100d4000b4048030440c1c00d5901c9039050020701c0501181d1050300408000325041f03410b0700c480d03140700350344074500001e0242204000e4051910b603c454008440111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 993710035 1250 993708785 993708791
    0xd15080c01080912070804180606140903240f07020f070315021b03030108012f090d02061b10020f0406110c03031606140f0105040c0c0c0b130f0e0a 65
    0x7454035004c2c20040440c2c410800710400084d4002044140d5003e0020340d1031084600882a00307100a941c11190302c0d0240c0700200d0051640702016000f550004c1c054220058142c50444e05180d14107011784180703466202c0550001d508003d40c02d500d020005501040610061100d1070b02e0303060450312420740e40806000a8034001c8842100240350301101c2c81e020030100240c4003e550013004540f203400078040e42106500385601d1441c00041805402051003003c00c02404c1002c23f01c44421160f445003c0b40c0d40c0150b260300254000d6a9000007900d05030740d2074000606008050100076040561041d00e666035540b0500101c441807511a003a502540e01908140b0200034040034042d00c1c00300e218180c2ca80c58800040e040c01c1c0705c54066034840000c6e101d0714041c003514036010040701001c0c0c402c844e0f01442c50030b28001040546083d4010b02c01c1807200b41820310442c0300c42d450f15480900302d80c001d026107040c000b80c2c5015040e0314400d144020010038402d100d09509040c1c3c4208200c102800c0d8a8507151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 993711285 1250 993710035 993710041
    0x60b100f05191e02011d2109030a02151b160312050d390e0402030c070206070c050f2d01050f12060f011112070503071401020d15080c0108 61
    0x4003604050300103405003000f0404460703000500a019152080b041c8601c00150f421000ca250340000d68204031144440c2c0e02c01d280703040800341541640040115681c144108064140540c41e21441c4050044074060840e5036480c40c100010692401c00c0140001940b04030049043d00104a014006076684100c43d2048042c150804440c0c0707000719100d89101501e030081990500d98402c1210902620607690b81c01a03120110304502903900200e4100045041340b9503070101460194000c3d0f07481083d00501030309041a41c1c001c10b03060f0b0004601203602c91403810042c0b05524144902c0030b1814011141204115442e1041c91a001d0384808004111603c004a085c201d230300403403e64042509041d142c0ba110341c00c58816484ca031000380c0d41540900810051760302c055200340c0210b0300820a18004100c40000c3c1074481010b40c3c04210b0513180c0d40010301090300091030003102221280c0d04e2000150321000c08030440400c548400c0401001613401803810041080c0c0458800d8046a0034200b01065035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 993712535 1250 993711285 993711287
    0x41a070201052205040b180f10080a0b010305070b0304050a060e100504051b0301050709064e060f090507020f0105090f060a0204050f0d0503070c03060b100f0519 71
    0x409400d4800c001024040900ca50f8000d80b83d26040440b581241c0a004920a4005101c450310542c6000f0030000c4d81d200004200c000c014a20310341129400c94031984860350b03400c1050a081204004407288003801b001001403000c1000748901030a4442684c83c91070030240e40c3d04d540c5403080781d80201055100c4030300001c400c4003400309907000851500207024034a8a45040c503105c2c00c034200701e6100e0001091a500007424140305140c4605c542d501c8140003503080c8803003074076070b48001612008500d000b0b8082e58056402e4240c481032031a17420000b1404100c102da814500d4076400181c031161075182050400a02c1d4070000017000316180340600051545401d00120b01300610044140f91940c05c060602c0003c050005c2c050580c1c46504007a0342003031312800e072854140c3c8a50b119140c4d00c0003004140c84140e2030300141c4c400f4070b0b03482a4116464440301d41d40d1405072a05a80c801d80303c2554408510800b0b040c1008144c0c90b00c6080d1a0841c150805254090414040c42c80c003d62901119041d0740c150b5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 993713785 1250 993712535 993712537
    0x7050415060f12090f0b130507120510090506010f08030c0a032d020322050906101e0306030c09050712050a090f050f011d0601030209040c090c02010c080c041a07020105 74
    0x40803000f0b000b0700c804038040c20a0307100780d00c041900319a00885000080c20392042c089040c64002c0d80301e07020300a664075115215680c43e0b03900b2025a01c601806800b401041424803c2030300191107580648007039031400340c04005010941d8861141c6401c10400194107000118090741a03075403500b00001408600704441503640300d555a80510b012400501c401e4040e000000340440704041c4085218032074003400d01119211581c46281e030812446404030f1124076003019815003d41080c0f501d990071a0b40e0ba503d0307102c1501d0b010154804283d9600c000c0c0140b04103a01940080c00c000303d818401428044d10080258104c00207255000741d5820104038070449e150400900990018514064074016003810754030340301082e03400700441d1728150382c45c00c90003030140c20010030030600005090542c1c40c40c0c0901c07081100040c0102c0302515108000b1903401030501c16000c00104503400082c0710740e12580d014000420240041d40c0303144080c80304210b05102018000400945120700c0c0f82c980e000c4d0710040e511 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 993715035 1250 993713785 993713807
    0x306050a0605060c0c04050711060f04020102030702090a05150402070b06120f070f0f051504030b040501060f0e09070608010503100b040b041118040c1b03090807080102070507050415060f 82
    0x210280000d10704c540c268000804c00602d00c800c070b034201b0250302d40c140b0603181c03400946110b22403a0050310025001d016018603441d40203006005492406100d6400a1506641100c2000e180b640d514140050000081800c000d0f444007554110700c1c00d800782c1c440041c0e40d440101618850b607160111040034800521141d0500d0780c4140c21203140320b0300c13408070303584141d910f004206207102d1009000034140303807012451800c4922000041c0c0f80c40d0454480d407803030000050003030b9403964a9480019085060842d0300d4020010801001400e0a12030342c040d0501916034044000c204c4410300501413a0340200350380c03041000c600000100d20b01400d0200c4d010700400c040366070f4040c0c544900d00f500c40005000030504010f41d01e60603510342490030108011260f644524200180100c40c0801031f004c40007107401c5505009060891010741d545c403007146421455000200d07280d4000c00c80200708042003003942c0151004540900c0302c2e410400c15412500303d04d2103030742c0402c0f044940154616000d802e04941c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 993716285 1250 993715035 993715039
    0x60207120209181e100e072904120c03120807081306060e100819050a0f0203101a04060501110d2601150f0e2101020d09060c090803130306050a0605 65
    0x113407014035003d81d0340d00d1710050b6030051340643c00d0101140751544042180410f444480c540d01c0410860500f0810221070740b100c0e0410703540c50402c0089461401540c2982e051032160b1003041c6030a065262155108440f0041c0740d05114001c0d061209007134100303059940c84030f604c090400c1036080c2230602030050003043c2d01038000583c0c0d000c2030103203445038041c002c42640e280070111400700080f14225012004503550145c116044200c1c1c4100240b41e052a8801c040c2c0014125030b40d88006e1100c9104880342c80312034020014111500308518102806013100410b02401c1c46841d50b1019480503886428168140082240b45140f401042c1d0310551017030b0509080c0c0c0e070280025078507070003e01065240030351a60003040d1a081e4031405d942c403031000c05020036000350090000c032407441420074200c0c500d04075500c0555024040034a90341b0052094460480c0134102c040380032460180d001d090704509400903c0315410400804008580244880c07088030f501c9680020507507602c1c5040402801d46800c103036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 993717535 1250 993716285 993716323
    0x1e11040c05091c0b07090608060607140f010902040e0f03030408070c1a09010201052217040b0708091003050606070b090c2116050d020108060d0c0e0106020712020918 73
    0x19982c010b00048548951054509a03e00d03100c4040031b495000c11840f5840018040b00e00040450034003a0191403001c0c412508555104d100100141c20600303040c04032507150303641d08109002e6143c40e02440751402c4c081e001030042070040303040d03494403480010070103410200002440030401c441000c00100520600c07801d11643e0350441315440c12640314503c228019820840031500210b10110502500b595030043d801c120203082e52400c403d071004129488c8200d0007880001107520050000300b07219032107044210b55502c048000c110001410000e00d200705441c01e801c000003921911b04440c034043c2c00000104842c1c0e0703006a258544070051144a4015092840e545441040e0000715020801c15406030340e06080070711841e012040c420312540d640000d07400119005540100d02068010f00050070100035000b107501c407103190b401290301c240c845129044c0100700c01641808108050151810b00c4112070846e40c00140c04241c0180c60749820036064103816007008070400c000e4415500c0a0050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 993718785 1250 993717535 993717559
    0xd05060f030109241b12060b030c0c0120030f0a2c010c03050603250902072402070f0803070e09040c051002160b16050a0606031e11040c0509 62
    0x30b100750b01040400710a40600003a0a80c154884d03800b8201c1e8402110654000c0d6610040040700c08490002c8080c601c642d40d8180031501c507852200031342c0300b21800ca190740e80d200c1d00700d5407482c2180c1c84003d01c807100d900480507000d207050134002100e4004a040000400c1900c2c2c2001c1c15009210b2003c03070b40500603459010103814004a00c0540380c41c22504004c1060803c0d21000b1341c25500103d46043d03168001c08180000302c0c0c031001e0120824803507003000300030b007503101c06a180880e408040d0643d0010161148a007090005003d40314404a080d0019070414903036641d468500303032030340c0001481040013100052a42c1d01c100441c20090300010181240c6040600b800210340710940034940c01845901d500341d5400d8000641c0d10030062400c000368226510300050140d0a4020702e042101c400c11324001074010a030100000b5410034010103000a00500c0c5140a0303c0c2800c2080410030426400c001002c003144409807050001c0400342e8002c2000c6000007000c4819100e5104040e41c8a09030b01c010b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 993720035 1250 993718785 993718793
    0xb18160305010606110607020a02210114090105010f1410030212042a08060c03041a09030a03060f060509090403050f070804030c050111030d150302040f0c02010b04110d05060f030109 80
    0x950204e0f5281c0c3c0710f00309180f420394000382d00c0d150111200070140c0e103c1081c090042c2010703d80c0070880030b082803600004990070012282035484070418580f641c3d08201c10700494000a12600d40101002c00c020360074140b50450210030505001012842010701c1e200d0030104034000d0b01101c080300717a02400228145460304c0c2070250400760b150f42c000320854030285c1501100503012114141e503c034034000c00c0c3c0d5030340d441e5840c00c10354002482111510981c15002c11942030b5885042d0185c2107280c043c541300c6211040c02012201c903903000707100c00002802c080020329004021070b521201c0507a45040c1581da82d09041d00c00d40300c0c8584440320013400140910900030482c0103482a80e10441100d03641c41e070b6940045803800c06213244283d0a41040101c20321954803984114010040400059013842d9290006401c9521034040095040e41b82d12640003100c0d03082c841c02c01303404c10449040010140c1d01d0403021550042d485020741c040d9a410224003244d0303a0103002000418018003c0c0914085450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 993721285 1250 993720035 993720041
    0x9050403170105010e04023f0f1905090f06071110060b1621090632090a180903090e160e0f18060f0901030b1816030501 53
    0xa800d800080301ca90078011201c160040c102e040341d005944010a104d61202000000d5020b25045042011001901c821841715818002ca0032020303850620406000410122950030b80100400b100080010800c040030f00c0100020b541500c9400e0300003100e913141404c041c070b4050301001d0704050344115810072140907071111118024000000c26120f10309030b0030b0310030401d80307110307000d03603507511100b48044840f0161107001216100e005503214081c10940301c02415003089100780200c002145210207128044e001201038403101c8581e405039002d121800030720380d4054200b040d0340c03100110004800798a580c8200f9803001610704a0746000c00650021034510041c5180d9800b140440c20845000402d1880200e031540f1071a02c01010780c1545004481c03c072036241604202e07541c0300e18200c40b0440c80da240d076014404100012124032646040800070040f00d10804e101c2c852203005c0030b400520000b1070f600d00c82900881030307040e03282d018540220850304000110041410740fa0000e140001031042c150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 993722535 1250 993721285 993721291
    0x1206141801061e06030b032404110315180a020a090903081602030f03060109031a0f0a02090307051c02030303070e011d010f0c0606050411220e010e060d0c0905 70
    0x40003004500d40e511044810b441010071420f103918000c100030080240203822200003005e008081c0c66400480c3c240e1041d61030885d03040f03885040366000421017080003480865604502c224001c0020707441d01c0c044504c000703000800001c01b8201c940d0881d032500804005000c000c030360042c1915406a1212040750043c141d82c80250001040200400c41818003480d00707070200c0c105036024503d0702c010240d9240f400d6001030516810013600c9000080403910255200320040c040d001c507041a1304110a4042801d500940554205441004181026680002c0c43c80c11114140c80c4200155000e407441c8103442032050700a03400d030000000300403c499105400c0c0d0700c1c0307410903203440070310702d51002c0b40c2c0d507421b00c1e045070890114a100c0032914280e801410441c00c000e00c912070201d803c030b0b192070216042c0c0780304004038031a00b4804206c04983d0055001021188000075420001007803030142003d120320810702ca503000386000e003c04240e1a8072044205940e0a400031030020090f550383c01d104006107022 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 993723785 1250 993722535 993722581
    0x20105040b0109110301152c010f030b010504051905121c0c030c06021309181e1e1718010e030d020607120207020a03050a031d0a120614 60
    0x18038004110121507124680c10b03840c1503610b0324156800c00206c07050040c0410310140a00803c840e508d8000300494081c4521402010090040042c0c4240007408000005100c0020f040c00c10640b41c0f01d0b6688841a40c0858004444a4822240c418984450f041b0b00d0b07044240c0180c100700d84120300000004008403545c1901c02c00002610806c1030490f814620003000034000b440308400c100100b10341e80c014101502d007481107010040c4c0d07110300e81405c489061109241030262004080c040c80119603041c0c840d4500c0c800001000c841c9561010b2103102039402c074010b4551452280811701180611000c040929250955030312a080380b0501c7c009807444003450700250034101c1104131400c020030052510600c0b90010481c548941d01c0645003172409500c01080c5507400d10203400941d1700d9841c0000214020405003010440e603090043c49820707103124082d854082e41d0401c00703003a1285003400085980c4000110070400360391800c6409400c0b07540d00d0840307119240c400d1028011003c0d403850000324030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 993725035 1250 993723785 993723803
    0xf210a0623010302090c03071707080702010b0d0f0b0c1b1f09050d111504140d02030c151b0a030509101406060a031b0309020a09330f0602010504 64
    0x60744028540548003400025007000301040400c1222680302c018540008860411440d001d8403000b103100c40842c1112410300040b00c40b03060080468085c41001c842c080d050740c59a80b445a00d45a03005400d00807413004209400160004608515110a90b8624261305101000840e401d000b0107664412800100901c48088900301049010501c66000c5503944080075190400d012441611030002c1d0703000d03041e05070184d41c0102074183c45c0341100e184102e21030b84d500c401c1e40c3c60040c01d440c0780641656090301554001c001c8000d008200082500c01d402c9042c0c1c4054040d46c8038045442001c41c5c1d84201c10725403002003001c40b0342e9601500310a1043c0c41020071140c0c50100b140003074040d241240c942c0807686071244003040e01e506081c0c00a1049a009040205504801c580c1c8480c4c030003c01c444000020380c1d921400811031614180b8a0011301c90340034144910705540e000410041502110682d178407041c044c0c00c044840c03640204000419402c1080345219076981e81c040d010b0300003200c0895030002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 993726285 1250 993725035 993725081
    0x191103090304060e0a0311040b03030409020a09030b060d030507110d080d090210050f0f030912070c031106120f041b0f0603060509070804031b02100c031d0f210a06 72
    0x42060f0407000706c94008140c0690030606c001884010154441d0441e0180410040032824818500087c5810f00059981d084da41e841d40c207000c3e1031032401078003c2c1c1c0328442444800001c40d51200640340c2840d041004403c8500300c2c280043c082109a02c4c00501c003c0e8046599041110359a000c0080540265100740e10780c185010115818490a00e01c429011010720140030074004820145501c80c1c41c02044910303807415410b5088a940056034101d8034050004010300402808401141d09a0001da450f81e09000040403c0741c00c07582d0040042005e611814002018420300c100e411542e82109685d450425840300504402c000181c0a140c020030b042200004031410040d01292149031150b40d01031740ca846a40d012a41001102e011980460b42102e035100981e031210300b0b4614140302c81d196036201030a01d2401500160019900d01d000507041c3c3c110454944410781505d114030011204e500c060115a800303003400d580401d0741c2031464841c0700c425104004642d031195540000b0780c0700c0030503030036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 993727535 1250 993726285 993726289
    0x4030b100302010f050a0e0411130b181e090103030332060105070f0b0108030706050c0307021b062101050f030a03171e1608150603191103090304060e 66
    0xc251480001c0c00651410507903110584141c000d040d40d0211840c00c2c41c0c243c200400058140c0ea8002c1c00030756040f000150200d03600e500320b84440010700d211001c5900f0800b10b00d02c44190925a071203030354041c0003085980a034455403481344802c0b07010001c15000980d41c403410020700402000294440f561500301c11218004034842281c8041402c2010f041c4291342ca200044070543c1294004440c5c8191300741290340001c4610000034040c1030b0590085494040900f04001510f00c0503281c1001d011040040c440c40c40e6000c03520b4003201ca0401c10421050841202040d950301c00c44030380040c02d05416580000c18a000070045040340c2080f24041601415241015100c3c0c100d0400140410800c800d014401030218216545c000e071011074104502c00e644100d01c0d0481c004980460442502d01d12580d821500300307240c10b400540c0400814282c1c80c513040400d41502c8003901842040c520604c00388400d0703180b9040030040401c42d100c42600c2c1c4c140802c0d0315a89400502484c00070031541c1e200c80500b8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 993728785 1250 993727535 993727561
    0xf0f020304080715050c0a120206060a051c1e1109090115090506030307170304060e010204080d05071110020d0f0f0504090f0f02210108010209100f020f06040804030b 73
    0x602c48040240000602e4082c1ca640c0802a8559a609100c820b11011080442c01c1c01074100c0039008186250b0b009056480c001d0401d0401020740f407044050440900850310b405601140c19454095850501c1d100d60078044041c0c0d851000d00421101e10420010402c035500310000707d550310644400d849600c41070419800c0e00c9090100000c0032580600400116045401c1181c00c120064103aa00d040c40f69203039400c0c100c420f41811142c000e0004240400c01c1341034070034041900040002141001d0804d055283c542908400c80382c10080c0101c5d2910a004603810401ea401074014142405000c48640203510f51941c03035000c00210f510703503492081c0640640380300e0013101e1081c2d6801c1d240a05101c4510000c00e00c4c40e1104410664500243c4c0d071440761407000b13080720f60310a51280c0604840d4030f0391400d0400140c10220103640184204500d6440740e03400031001e0b0442d400c1a022020309035004038a001449903185d1140c0c4114810f000900c003041c8001c00c10b82e402980155511b5483c0d05040300c1c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 993730035 1250 993728785 993728789
    0x7032a0204051b0703080c0702040501030b15030106062708031207020d0c0c03120314070306080f0309030c09060d0b0403120c0f090b03090f3f040909020409060c0f0f020304 76
    0x20260200540070001b84540a020760002081c040c0908058054021034201c407800d801c111010174000c0b0511901d0540c00c5424007251000b2002448418180038006101031603400b52800413806200c0c40c42014000d00a09102030482841103a0300d550511104490a140941c0c03000054050b102c9000070413442803010350011600401500015841c640d11000c50402004e11107041580d101e07040c4981c82c2c02c840300c05000d000d040d0303404160381e07042469490400c240142c0c02565503008000101441c1c0300444c41400d4401c046031031504d5a43d800022411b20745201400400c01030131030701003004040d004415030405541400c030070042402410f2003510286c0314051180081920814204011079440d4001d56100348800140ea911600e98107103e07280446100d07003403400400d0f44100f10f0750003414020031141c0c0d4800010341c101080381801d2040840c03082d8041c0c01c07103042e21404200d00b591220340100e00d0036035211000304951500113400510b140e2040d480703d000220b04040042070540f0000a80c4c0c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 993731285 1250 993730035 993730081
    0xf28270302012d1d040603111e03070906030b060d02090f0c130b030f0f011a0703030603170915031b03040c051f0e0306071407032a020405 61
    0x255250640c0c0040da80040c0200030380103141072000b0a02040810441d180a4403001d544400d10000c03028101084030a1444c9001401103290010030000710b56503003a0030040e602c0558202401400c00601500c845c19542401609441079140000b0b071621243c0c0440e040f2805070203030700c40760b8a41904210380d908580c0000307580401c000000c0794000c011424290b810201c4207a10910701100d18401214600c0c1a41c131581c20b041021041080da281c081c10419032048440c8102d001546c1017007200c800b0f25526071f140c1c8a0500300894800e0070540254014005103030058201e015040d202c0003854140d90165901d140511100350176181240f0340001500d014454071030000e5070f090f200151101158000900903110705828280024050301c1f541000e1000469000ba50703180380f0b0702700d0400f4000c0004e4450300c40c000da020b001080012680802050800c540d109900d542c0c40c4c025003011205882c80010000c070401500002140c0240340200c88a0b8440c420b07982405150b550b03641c200d515040709901c180c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 993732535 1250 993731285 993731357
    0x901020a0c020405060415090e0c0d02150307090b040b04140a0e06040911040905010e0f06040b010e0a150f1a0f12060d05060f2401140f28 61
    0x1000610f4203030402d40c1e000d20040d00000707070a100a41480c03891600c0354800c1d40d038142e80304011100d041090203240301c0404240e034843c000519a03404204602140450035180d1000440841c0c80584182c40c18401050b41705502030f01c4688030000c03060540d00a100b941d0003400301012400d0a41272122040781110b14481902500c1d41e940700512024010010b42194001c0340c2842094040d610b03817040300440d6025000000f0580b0b440806c0710310b0440701e00c51150b2182d111804020007c0c0d05601c0c001d0548040403042145910f80411000140100350080b080380340c031036803003c110b04100104040c2150a06084c5034001051090241510b00c610781d540b070801d22040110483c10b0000200c002d0700044003800e040801142074807490b003059070944000d000641001c0920100c0e0310340c8900d210307000081c030b403c0104c00000e0000103444090302000e001d03160400400c96220300203c0201307580c21045480100c80103040e0f90801200100e4001c0410404505225045290103581158184162032003003291 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 993733785 1250 993732535 993732557
    0x20c0105030717040506040b0c040806130311250f05030a1e0827090906040b0a06051002010905070e010f03030e04110c03091e01090306092a0e0901020a 67
    0x11100c50384002e101c0414810f0700d50b0002c00b00140ca084640c411400b800190000f414507180c001c620f1000600080030700300d070030301090040150100d011600400300340b410303c03100c815520b01136a41941601084146000304540708904103802d615900f2004c4410111600030754540c210059801c016000d8140c143d4080708181001403a51408050760484003409500120103596426029a0241c84100c40004007180c02c2c10750000c000000300703d485003c80b00b02055207040e0141c1030703031040c0090014000c505843e02090498407254050f0010f4800504400c41d00d1561110190107001840c10844141c030502d8000141118081c40c240d041c0c403101034031800c2451440c1c8080300d40d001040819540b02d03985032620800c0c0f14042000b40043d0400a01940c0c850101c04c040140b003200811a80580101d40100d4840c507a0340480350300140c82e4410000a00c03400c26003403212810358601590165001c2e030041c1c8101107148103600000311040d05444090a60b03c1e2001079080c0d00554000d100824602604 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 993735035 1250 993733785 993733787
    0x30209120f07142e02010b0102011e0b041d39090c0c03030106090302040c0801051c080714010b030d0207061e020c100305070201061d0c07080708040608180d020c01 72
    0x10303400d0b09140051a21041110310350b1340360780c03603d08154100351002d1810303194040300380c0a00607440316020900081082841d25141c000d140c1c1180480020b07202e80c0c5400c19802952154404900317200084034811400d2104006195906104505082e04212040302c4030644543e65990b43e000d01044440d00c880910090141300810b000074100c20307580007040c13042d0803203100200043c5008114507510404014514014402103c0b280859032040201200050000751150091804200780c0340b4401c450469060500c49054014500d006050034121b4402108080c01500301c280036801c21425681c00300509003060b41c1d41c1005210341000b00e6401519000400e0010080201e484400d00548100c8401c560000f8031890000c08503001080c0c0e03902c01d0200155092241d0b001410191080344a100391400001c0b007625801880a00070360390009459042004c01d0082e5000c483e03100300c060703480d6500d50390041c0c950072089402081e44050a603600b07268840000e88040c41c600c40c1c1d0050300130034a041c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 993736285 1250 993735035 993735059
    0x30a0503070c0b13020a080606100f0504050901180e0a030e060306120d0f11030c0c09060d020a0f092009010c0c0f1e060201060f140a15030209120f07 66
    0x1c03a100030300412654010200e00d0014689214860321611203004912520401034480060b802c0700c00036a00600410803d601c4801c480c10381c200d980e040c00d401c00000c1e128100d5452090b80c00c070760b4100c6a00d400004074a0403802003c0c14a40380408148003480d6030040e51991802d4040e40030700041c1414100704203d080410003140c21170000740c802e203491a0381000007840c00030440030780400102600380014019074020310050f200800180614641700402c00c90039910007000080d58400c1041034086406907849240b0240c62640c050040a071a580e103000e03810b00324009200704850b42d420020f405400c0d0101c200d200c190b0365852142030341800603802c01120313484080b6004450740040100c0205040103c80d40c80070040004205151115030340134404440820749074000c84c00d581c10942c00740040e500401078001903a2441000300d410600000014032212041c2d80120007018881e050800d026503d50004c0404103400d441506440c12a6409695195442210122150005e076018000c075080c0340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 993737535 1250 993736285 993736291
    0x1e0b150a170432010605010905130f0b03070b270616020d021201020706150302060304240c0f18030b060f0312130501110106180b031006260f030a0503 66
    0x1001d0129107160034660700700041c03440c003490510002c1c43c0d004035502440134050000a880c080c84e0440c1c04614107800b01700c64540a486503010b01e52100c54442c1011141d170f000c0d00c00320400801311019240d48030b4130181c041d40000b87c102202410340c5400f4810142d0440440c10840b07010780080d01e05840780ca920005101c0140e4203d0b40207581c10704a0015984901510703101030b1110000695840c41807070500c0468000e17124614030035020b90b8041000d80d0b200e4058035030164021000354011440114119031046501c072002005514241030384108a901510004182c540b58030740c2e1000c02c07030100440301c080030b4902c0000c3c0081000d000142d042d0401f0912402428000350480e007641e10709810507039072900311040b43c1207503014074401002036603403140000d0100b01c4000020040c0c141400c008070540c0f895144e516440984840350041e56841c20030038403181c5418298100186515000e040107480003d804500c08014070320b00414040d030780030031040a65035001e4021494080f6100054515800c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 993738785 1250 993737535 993737543
    0x715140a0c0f0812042a120212190606060306061d100309170c0606100c020f0a15020705030106150c0f030512010b03010e07080106211e0b150a1704 65
    0x921003581c03101c00c4d50030443c0c00b5610500c00e0b10300c18000030344529501e251204168440840c4910f04101c030700010498185e000da01900d68942090504006a242103080780c415010600e110f4112418000305034041020340e40e2507541403001c541c2c2e6540403100b1016180c001140c01803032040c030f0542854200b0040d4102d60403802c0c04200d0301ea2035261428a40d20060070301c0c03602000082c04400a0b0010b0081641c400c2c8202c49009040000c400c000340283d40d5540000d0041440c80e1009040d81e40e500c040d0b10080250142d00214003004110003902d80c100d91142c6030081d070902c48042102501c241d2000d201c0c142654900b8003841581c1ca0781c4282c41c140132016028080c040144041840f0480d0880b4081d041e035199040e56035242108184843c00010044000c011207a8010f014441e80039220786018100c00c0d584041890710150301c4030080c10b04204015003800c3c03000c030800102a150300800c660040032070308a8001c240340e01d02001c03188503410011000600358208006441c14441e103c0740c0142c00303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 993740035 1250 993738785 993738787
    0x5061f0c051c030624090e2203020c0a0605030c12180316050c010c0c060509040b03060a09030e061219020f031e1b0d0b0f030715140a0c0f08 62
    0x42c0c0010301c01a07003848070100082e1146003d00141c0c0011440750320409112400c4139102c8250000101095618062214800944d04c041591058400000c0c1203400702c403c02c0e02140b0400d40f4005e035856069108550068000745070020320745020700207a9104045000c0354510b065601c41c00341c281104000e0902001c0d204a4607500c85080040020b043d01c0180b4200c51241c0b2440340c1841c92911085403009810000c2c50040c6200282d000c84c0c201c400c540703090070030075103503440400007501030300000703408641511030501001001c070784980241c56000e000e600c900d0b21007521907091001c18400c19104e04078014840380403a440302c08001041441300c3c00000e0042c1049094884403c0c154070a4030200350860074003200310007102c240030301e840c1c01082e07500d403418501d924081c400b20107000756468540d0060b23990326401450385824442d104210b20080036501860345400c0230038880000302040c580010590801b0300321108489049a180161030349480e40151160f039125004400694001c07180000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 993741285 1250 993740035 993740053
    0xd180321090f060213080d050706020a0c0b0c03070f05031021170405040c0201140417040506040e1f08120904020c030a09060f0c03170907210201020105061f0c05 71
    0x1005185407503070382e03c83d08000d66520a0142d0800800103507070003002d500e400c40703641740c10300d01d03003040444400c16800980036840f41510701040d80e200118160240400c80a14100280103910b07000651113400c294489180c0080b0107201103a00c1d0104580300f8024201e0f5280510428100030300c0a82d49102c69400905480750a6540d12a6284ca803000407a0403400420103100742e2034180585580030810380b0081000051080c040c0c0500d501c064806002011520103040c0200101011940605000740c500c076a0385d45c0d1812560b10005d800ca41d5030007203002004045145206800c4290100e07a180001042010556600321555901102c185a445542080240611601030010b4441c0c00c000b500c466074014900340d0007030900c40b0510078180402128154402c0003d400c0000749040d0002070420f81002c5e964191900d113002c1580c3c00c800d403c1d05001c0790880300c3c06580010b48980d18030070b83c028030417a16950180b012131907000620301c11030f1182150b400820b5200c0e00040a84a00820880301c00c26 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 993742535 1250 993741285 993741293
    0x62315280909050c282f0105070e060703050315120a02010e01030e0717031201080a11030703021003020c0109063206090705070809040f020d18032109 66
    0x44040003000c0c0229039060001c102c5404180b040690001d08100c10900e46000d0300003a51a000d442c1d20052041300c0b02180c240c80c4203200d107980422030f01400e54003401c0444072403405000540c1150f6007010642c20400007c000c1486500301c6684058087c10440c241b51650b90156641d80000b051005d4040a60341c41c0c403a81e075541d90034626100540b0026054600650000400350444558040d06050809801c099583e00000307000b000c980e501611003140f106898010350031403143d4401c05c00f425409400118555901061030048140b0440b10260041104d1060548401542c0302c048d5110b80b5041c50440000c0c041c1d00181b1156081c0400056200311542d1a501102e880011140482c0322000300740c003c00400b548101c4da81e13503c208540780717646005c01c00580c0b00704000b000882040000301b103002c1081020001d40f0300c0000014000d005110300c40f0310304c800035040112513181d0380341080100c6400070f01ca4908440520740581d5401c0903551240c1940090034110b918030703910302d5070380d292181c046 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 993743785 1250 993742535 993742597
    0xc0304030209070311030c040509310201020a050604120f090e190209031509190c050d081323090907060302090a05060c150916050d080f0706062315 65
    0x40c0c06a10061f40e1528203003405d0140b03c4800504c14040c460348500343d039400c003181c1d0500b100300c0440c560441144c846107100403400c2ca011180300600500c00e16091008000203844011081d83d001d036542c2c40d80741241c0400b100c45100030701c20841003c03144000b0801d00d14000f4103010220000401c0503162170145004a868284039820440c8100d0107a0144480d0940074841046a12641c040a5142076a951a0490303514042d208a9108468400d01c8a0800c680701c010b41c0c400b01e80b0561200b440b80c5d505c2150300c501c08034130f02403185028003154a460303940c0340101c401400b8520550040003d10f0500c0c000f41d000358003040b00c19a210002d400002503647d1918001d111301000b11f1702030980c440d600910214561409048000706800007050440d00307841d42005c4400321402202d61540340282410300301c80b02e22a0750440f140c0c1a200180107001d00a25400220803500060b0752005c145542220f440600c00f00c03128401e41c4803a07618a004004031060001e410708000f6040407010003a0031800c88008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 993745035 1250 993743785 993743791
    0x902060c070e0a14150319050f060a09050c040506060c03040f090f0e0d2a0f0308090303070c11031510030606080613060e01240f09020c030403020907031103 69
    0x50303229001c00e02080300410074150f003200564900b48001c10720085030151040008040301e0485940c0c2e4030441c5c1c1c2d5a0308020000c2050503000102052000d50305110740c54050480542555119040110380ba8035914480d070100e85401101800142d02070b0810003000c0c11000d010f9592012041c024a20000740500c0288010241c50302600d002e1403074400207600361640002038401d034070300d88511000301c00000b103607108a91403145022080c220790344030843e0341407924021040580400300006d00401c80501c111010b0f003400b0380c50b04010366581e02c401c1c9690307120455803a0b000a0301c0742c4444000136206040301000c0700009080c5e51021495503404440e84000311a9030342505401c030300030001d12050344650409071405c078001d48068a4003036100c0c80c2050036840001c0c082c1d40c0da4031500041035420b621400c07198481d00b540c0c00c2072642180c00e009040722240109170144814110005079982107200301e59000211001440c2400e10f590200500c2e04002000176040c507440f00f43d5050144007031002144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 993746285 1250 993745035 993745057
    0x130b160215010b130909080306280312020606040501030507060e060c0d1e030207230114010e0a1503050a02060c0f030403030302210402010c1203110c0f0c0a06050a12090206 76
    0x384801e102e200d05409110150305c04a82ca07071500702c02c0c40c00725000d4412039902031016103c540000701ca01c140c0701800c070703d000c00e00c018200000038044100a600004010f90900c19401c035441500d4480821088074000e10000300a0f07031000700704002040c007807056180700d0500184560309186c81c4c01031041c01e0450b0000301c0c100186d007c0e201180d0803020301c00342c0c0900e40650725045007003000c03640e204001c00c082d0000303003210013009070340c2003020007404d4115007013000c1d401500c8001540d41d1400714509041c15180080d030075003410703075503c0352208100201080341e030010018050725425800b804a0380c0d01c46020345d1514020138940180400c1c00304024401140b103a640144e5030301000d44a052410800072a10541c904600184000f50707030301821000784035400440400102e140c0300420340080c01c403400300c003001c617102050440c180704003c60881400100d440a407002c5003100c50400030140300b14010240898000d114420600b4441c3c1c00000044143c0341d800524900c00b40c0000ea041d400001c00303c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 993747535 1250 993746285 993746287
    0x3031303080702030f0301270c020d14090604032312070201081005060a0e03010b0a170d020d08150f15030a0c03020414060c070f0b03040308130b160215010b 69
    0x40680c0400041d81c03103012403004d9400c0c810f402c0c1207034543d0b100c18468a80c0b400303402c8400074144030b98030a0075945018441020800308031000300c0603403541840f0030b010002c901c2514141c0300103201c0204491900700010a45458282181d0b0760a002d05c40700a805003441d00c0c118100482c600b401c102c41d08a032051840c072151100c07014800101502d00090140182907500942000182c4901741074030901ca01900300208042e0140d0042401011810441640000310307034800030300c00401c100002001d0190206980805d03017204400d0760f461100010040000303017100000f0708882d2191001a000c000020f01c08580300d000400007402c0480f03c0d02c03818098240c00401c1c0001c104251183c480a2441da0a0030b50901b49800a29a811050510304c00e004a10000d101c6034407900c00d21a0300058040740910590194940348107025540084400b100810003c00100e066031111003410b00d00107901142045180e42c40001d04c0b420142c4020107502903118010b04459509505080140030300070b42c400b0301e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 993748785 1250 993747535 993747571
    0x807050a20060702011407151a1c0b0f0901060b04030308070e030705060f0f160606051806091b0903010e030a021219030b0a030c0305061603021603140c0303 69
    0xd10800c880780e08151107100304000c160010f0b60001480403074122680c51071900e41c0360600780030030025003100011440301e18281c03940800c03403048004100c407440c040c1e4481807510041102c03010401c0c21200040d040c04400c0000a4081c1b4595420681c0803001400100344103a55007042100c2d034109070000c80109a445c3c08100c6401d0b400403001d0b0300d00c3c5048006068903440c00c0f021506a105051808925010002e00404074214140448200020700f8584dc68009980d090081c0200801d010351031207100446d443d502d00c0325010902c1130094030020041802078641d0030003c4e4891121002c0304018400c28010416681e4080c8580408641d050000d15520400010000c0c100700d15007500d4030718031201348120118209419070050801b00c1c241400038a46d030140c00040d88103101d0382e10007003d5a0b0a0003021080040206006020f4140228095510310420300e054059009094002d90348032400c80d807030360110b4860014109800400c0e90002e00e41903510410078190b51080b1800c160402002940b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 993750035 1250 993748785 993748823
    0x60203060f0603331909060b1912091e110402211e070504080c0105030118110409060b18040b010906030b03070e07080f10210807050a 59
    0x7808241104036102d80c510328005500e140045122082d4102c00308030010103042520014404511803400108070702164005003824500020003401102d52a42c204040001c1c1c680c40d1105883c004000e180b440220411000400c40d02c45441480d24180b003616000b40d54045124010f0541c68a030110a5101c0182381c0c504000050004640c20b441c040c074410401d51011300000d0394089510119100101c41c0c13a16100d03a000711203050a00b4503018200d89501780b14405070000001c10899091100341c03410600804015a40e50009100c2c00001c4500050129940310250b0710201c01d8828180300340c0d0825403160806012140d0315000f820f0388050000c0c0440008500d2032103410203034001c0310140601503035000000c000360468031a0f04280f640301c401c082c64640d0180300e6440074004902601e0b400d0300d400c820042c14100c040d0b504502c0c039000a00404c3c01481510341003404d07122085010700341000340c4184105026400780050754802028414440000c90a10036543c3c20b50041c405c001e105490610 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 993751285 1250 993750035 993750049
    0xa030606020d050d0b04020706050f0f07020d270e090c0108010e100317090306160e030c0619020c03030412030212120103020f03010902090115112802060d05010306020306 75
    0x50415540250700c910740c0c40f5031141c00c480e40c44c1041ca001190102d0071101040190207048030090109040604110744240d01e4140036100b01c14410843c40076445a06050341c40e12010390244001a0000742e0b40d40f505c01c420101918040b1071150300e080c01c0c6035107180032086260152450541500020702900c0f580d039006d50b00c98050312074409000500d040c4070407000480440ca110050501014801c110304070310354002504e11442d4041c0c195800e9281024003180007601d103840b0817004c41c004181c4034a1500340000c81c04980400504403610b0503008401451121010382c8800342144100020348840b0340301440a44020030341e51040003040492403070042e04001d0580036078a1091010f00080034060802a5041e0440303805070b4101c0b141c2008600864094100d03190040d410002d001d000288500c210b01d1400d290003861754071686c0c2820128500d9858280807880d50a01400c2c99015805a90401c80300800b201d00c02044289083e0300700400c5000d07103e09900548643c0d901208101c40b40c1003100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 993752535 1250 993751285 993751289
    0x20601030b2d0105130e1b1201020a09050427110f031c0908060403140729040c05040c02060411120601030c0f0f0501050307030c030b0a0f03111206390a0306 69
    0x403801d11501c8881c50f00299100122444081f1049075103080c1c10035916802540c888074990403000f55a1403402ca04040c1241034180301d03850141740780070300c100680c4041c3d45801e20810340302400d00300511800c0c0c8a00c601c114000c000e1a60042a02c100c3c00e8080c2e40c201700e600c500700056030000842220f0050050010240b83d400080c103038004104200000e40c1c4105000c03200d100051a15443d9081070034214030f01c5180700035904212514540750304220308003411581c42035116001e240001c0e62a5414042902d10310203a48016074000303004900064203003120203201000c040e240001d5101c0121685142440a070300654298042200911a54429101d29000381510400c07884080b881c03c2c000800078400100420101a41d4000744c0100a119800035403804800500c080c0304182c94204d01301560907a88411181c0802d202026412401c00000c007092012518002d000140d80b200c0e01d01d50210b003c0c410400740e4484003101024240341c1c1c00300e1360030f1850080380340a40303641400343c024044031855 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 993753785 1250 993752535 993752569
    0xa0308090712021302031b0307031407091a1b33010b0a030c090512073807030c02032a0a031e050307140303040b0c0901020601030b2d0105 61
    0x149207010141e11481c107664610060740000581e40da80701100520700e1044980d07c0c2e07402200001c103003c0384d41c1c2d01d82c00c488803020b020f440c3c8a110341c8409200b0340f0300c0303202c0344290050300e1000740c2021664061040901210342240007030340c0000c54007031805820310340c0c0141d0782c140380c55203600011300e410121080c60941e819450390749802c82d41000342410640c0601141c00c000c26841300c00d100000703031180d6410001400081c241c2041da41c2a90132240d282c1034240191082c100d4011030f02c2c0c4184404100401c00c8003c11580c030000a64481800c4030554080030082c0d046c00300000010005031010810740e141a018044601c5840c030f080d441e1004c2185207807030140e2186074042c1090000c1292048001c540306818080d07046646d01c40d00e4814114011403030050003801100703920b41004280400250f200e988288140c4001e41e45540d0504400d004000d455401a4404001840015107092455401001512030942c4061901c0c8030103226148804141e8140004000100400d0801d0201e01c0c56540c50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 993755035 1250 993753785 993753809
    0x3030427060302030c0607050c131a01030501050a090c05070b0a0f1107030906261014120c0105070f0203010c02010b040b03011808090a21050d03180b04050106080a03080907 76
    0x1940d00020794802818407003601c1100c0c002600d0040088c204207428101d5005844000d1041c68500450014071100ac1d0307100c0e103d500e18a40b02c0c0d0700e42c460301c03e81d4180c95008014200715810000b000e002440340510f10001c3c00000c100700000300d519108420321460340341c2008940c600720006a00103982000d00c910360b56040c14422200040c1e0460303801015074030300d45840c0300e19051700941c040954640b14480c05c10340c0e00303400502c451104141c40400913125084001c1c0440300703c0205101c400101e40410b003040d90400700c82045030f98468401030400b540220307250003c4040d5500001e084079411100b420150703564548580141c00e050042d54003c030021002040242905109414891380d4802d0080a400001a59150303d43c1c4100d4800c02600c000c0c4d8080300f0b0442002c0c030540c0341d01380d00403090750241309074003d13846642d100703014040120401180c20f44c9800240c0d40c0741003141d040079000700d94954a03441d0110f2501004c1045510b0140607640d90030031800c1c440c0d80349007402e2198111140340d80e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 993756285 1250 993755035 993755039
    0x201020106060918050603100e0f0f0619020901030f06061d040e070612020708070c0806010801060b09060c07081213140a0510180b0d1a13020a0e0303042706 69
    0x141d900401c00c20442e13104008075041d1795950000b400c1541d2a58030424407031a00c03240c8481200700180111107c41c04004079241e03801341030320740d650310309040340c1506905000d0301c0024104080ea07006096100c0041c180030429402803e0b0400031b48000da00701d04006075a18100101c9030796016400da418610558040008491181c001a101d500902942051000310307d00788048540640c1122002a000b0713001c241c80c4c600c5407502d0040ca09852241c0f44d5584140000403c0c4a0018801c0c0c03021554132883c0306103055070030800d010360764200d40703924900e6018825000a2101c010320222007085219010190344000c10f20001a0400c0260014108150f84103070b2004c0f1360b1504450b240540d07508456a84607401c03008000c07103902c84021420030829018000000b100002200502941c036104001401803169641244405078000c080295001412410410079204298020b0004603810314203242c0b0f0300712080101e031a540c06030f845911b400e820b00c3e00c80303e069699140c040f1141e07801c00b84244681c40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 993757535 1250 993756285 993756299
    0x15091c050a1b08040e071710050f2106060a321309120311070c05330405040c02070b120c0403120e011101060501090b03040c0f090902010201060609 65
    0x40101980002800310022071000142c00c600c02c8000c0480e4440b02c0c01e42c4d030380d8403502e2203174003010b043c0c0765100425030085500b4000003107c820070f40314600b4a5202c100251500042040044102c104c20f40c10082d92002e10f8203132098440198034041111000b841e2a0418009102803007005900c9031512038400308100e070040d200e0702814520442690901c1080c1842d0100140c00071191002ca01040340c944500d5004100120904444004641c0c070308019001e03201e40b51103021310941d03030005c0c0080d8482605101c2440c2540b011a000b0443e52046007010a040740030100c2011f46c5800e07a100100c0108041000f0300d000d00840c01c00c10964805880150701d0034500e101c2c00d003d111100765158846000081443e015007042d81c005542280c4261000b0700c0b9080054a6445090161400169820708424448038140070b00c170101e4a040c1e640e071801e507241c448481e81c0394002902c01c4685906240001402c04000c0034071101901286400050310601c0b4800a421113001340d01903002e01c0b0191004001003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 993758785 1250 993757535 993757537
    0x816060c1805030304260f0a03030c090b090103050a1e091e120e030a120c0b090106140103050613051602010c03051302060705010609020a030f0b0f031c020106030515091c05 76
    0x44401040e1821041c07211b44c103201120810f039002c82580d00c60152905024480024610302c2d142c080d450404c44045252022500908207010341040c556042220200c554425440290f001480034000101011a8140c209032140384c0e0229032180d645404101c018000b640c010841188507224100002c48040e80e18504607810184c03200050284482d0a2030a44d01c040c4956034829a00c410901596010a10301603c2595040c0e030a40e40074071041c00140601105100e4001580c00700c1c0c40105040303a001d00114040d240003840f25400c12500620084100da482c003031107005188040c1d050200c89810750000b42190700c440c800380c1c2014204424451b2148039407c4030342c951034055511907500c482a05000b03000d02074550000c9080c42c400143c5c42c1440e036159001030601100c2010500c0100a64420070500e808441c5e12940d16400541c203405140f001c9203028600c400c4c043c000881c01594079103c030342c00e0034210121000396000b103008021000d04140140301505600300d1445010031380740500117281d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 993760035 1250 993758785 993758789
    0x91a120a0c06181e21030509060f07060203070e01020607021504114002040b120907090c0f17070e09070e040509160509150d0816060c1805030304 64
    0x184420082451041410241844007502e58100048000341001c0c0c0000380c210510704c2003035030007100e00d80f020389001c5042e00b005c41445d8150340d8490608124004118a136482140030050221040041000194860028502c01e106645400340c440c1c0c001000641451402000781b030854000101d007224001042e403016800030b403c568202056103000000c6104010700710078408400c1042c80008080700c6410071507410500c0c410140c150030705031550516041e40260301031002c1c1a0f00600c0465100124621030075030043c4000100d882c1c00c0d56070701e642e20403604d581210b4400642003100d81280f50740c01c89041075180c4502c0002445903c0c0c40e1200510f0291801d01032449440c580d40442c24442c483c18100d050518024001c102d282881d41d02d55540e13005000d901403540404e203c0014091524204540c03251101c0d000070310018034803004000c13405030650000c41340107000703014070395450307200e4904050150311400c030020b9481c03500c0ba0f000d0080d164504081c0c104806600c404d03c4151800b0081e241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 993761285 1250 993760035 993760037
    0x70309050a0c062d0f0c0b1017030f22051305010f05060403030c020907030e0106081e0f07140103020f0d0e1002090d060f091707060b0d030912030207091a120a0c06 72
    0x5c80b1301e9020101d620740702240c0b014121480040601951a0403a41104100d0f03074000240000f0011502d040340c1c69008040d0039107014201441680000003d1900c552031202880809c038045a07214000110065541c00d40800c4c6250348100500400507480b4201010b04070844141f41080c1c40d541c0c00a140c1c3c950454000d005800c008003041c685d50227900301240001d45080207201c041d0702e80200170307540c9400540459501184155a0001900228041600c60783e9400580041401c050800000b0f51941528504141c7d00b081040340070b0000c0307000f4217200c00402801007507a1100805140ca050040d403441000300f48100041c0c20030f96a0540700c120080e43c0854040307502c85124400c42c00a004440703000d840800c0c0d0603064400100c4501c01048154480e400801c03031400100203100424407900e80003408981217050521001486201398240184a8411903840726242d940d10b0b0240e900c10f140740d081415110142e882c031442d0420600c100f00da112001030211031019250f10780c00c400740c1d00c1450 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 993762535 1250 993761285 993761297
    0x80319060e01090b041107050613080c010204140f010314060f040207140d080708040f151b050c0c030102070804051215161103120c03070309050a0c062d 67
    0x10a405064000c0300080490004849080d0f81d1400d206002d480080300c9a8840da10f4000460101800c0b00f05603144075410000801c00e554801001c20142c8c259003209850140c4e05115014806c0024001031025084085e4042003080c011414000210311488203681894141510242107004100f06070794880c500b00e40c0c00c00020074200102e0028408c545000e8808103c07038100c00450305c0d002030800d10485440c0e460560741da540359001c590700c103401d40b002400424a598045c020032a52051280802c0380001c0014007100e100d000308186481d504050f602185000c1946200700e40180080703100580309400070340ca00344107681c0740410340c403035801030610039440e504000702032800400c4482141000540880d03200c0c2407801008074070401290000b40003c19100ba0f68821f1803001c800c0d1040c105031082d041b00c49072101d880c11700240c0c03c01418070041596401d413003004644c1c1000b0030607040d0300518010310054286a401040d01426816450820b1003011202d0030209c081086003407086190b00e001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 993763785 1250 993762535 993762571
    0x2421050c04050d060501170307150b0414040f0201021e031c0e06040305270d06051b040b030f010603050402010504120c0b0414091518060f030f060a0c0c0803 69
    0x5540301e00803900a20381244040e40090200151940b00d28161340f03145a404404000340c01e9515502e225424004240c810014000810032a8a030403820039000c0040000c580140340c500500400c140465059a118030700202600665030103001c2490004d401c1a51203403880f403902030321aa244140301d50031881901103049050a4400d44c0c1c0030007503120070241664120f08144c00c0042c45a00620036000140e5014202550800300b500c449590162024242c0e1900008546882d4005c110040c42c41c820f4481c4411403401c4c02030403a00500281c14003004258903030034510030496004a051300b00d4000d06160600303000150b03070090300b903038100d1300300000e0f0b07120141d06c5260040c5489610f9006200d13000d03002c41c0120300f0400784807a1500400c1c00b62480112503903a9060032640c02c90f8403071041c2d04200c11690407a24481c0002d01c8907030085000e09269404071340c80340880d141c805942422100703a0000340510440844074001c1051250135840c080c500c000d06900c980c015031201608074540141d5141c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 993765035 1250 993763785 993763801
    0x50f040608030f07060c0503060a060c060608061806060f0105040e0411030d0e040b0405060f04090303020408030f0a08151807022109180f011203050f04242105 70
    0x5034040d10841e026607484680303e00a80c036243c1c000b40c00844601e4141056401030314481c200341e134410b6074028030110701c00b494003000b030755003c00301401521516207604001c0f68030300c410498280100c206c0b04940030010600e0001c5801e0007409440703544901d0442c05180000ea1b07010065170290341407540c1c0c0e0b451980b00c510380382030740542148d1420340500602000c00415600f007051402070368003e540910001440b1010001101c9049460603031000c291038100b40e10f0300b030641c4090245442410010b18068582410f14510b070809401000340d03200000361940c89580c46291300e03800401003042079010140400001e1004285004240350031841e5400040203684200805594410154031055904802441c942d54527404104810f01511242c0e00c00030800f40c061162034030403c1c83c038001032056402d09007256400c0d142001c0039070400c1400c5c4102d04100c900d200082c0300600404102c003401d10004e000e03001c0c90010b100e11140902c245160303105a101c24506048020340305007800011607541d2540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 993766285 1250 993765035 993765041
    0xd1701080d181d0403091d1614030f090708060106050306010518090f090d0203091807020a0b0901060603110f032701020c10110403050a060f0b12060403030b01090f050f04 75
    0x101500f42944243d1908400700c03c0070003860f01607400303a51002089526885074003043d41070310030002c1d88440e17a000019001c14071500980380180d15464002e0f100d03a00030700041e0094100355800203071440c0030418002c00d08800c010000007084a640981501e602d404005081400000c2900d03040c4140020320310081c20000c1d00141683c800104025150b0804064110a04104035040b058910454480407001400001650000c0750b0041c24480c03089086101403070343e07440140408040d4481d2190400004142c0041d06106181507000015060b20306140101583d100380f025603400d036020403200c0114540d14007140d82c40540c1d4110019188582c0c244654003200c00c0400440039440490f40300c0000d1000f054a01352581ca4070b9060110001780e8010a0640c0f0035413000030f12a0f405580c41c1d00008182d0781014614901d5860002500b030010701c080f602010380c0701000c81c07198010104200c10142c25100d81c031708511003841c01aa440707040c1030340d03103624820b5801060322400c40c1c0070010780da80c4c0e0f03203070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 993767535 1250 993766285 993766289
    0x1050a0e0c130312020f0f030f07080d0501080f010b01052110030615060915020d2703030903021003090803010512030913150608040812130f050d1701080d18 69
    0x108505800b140c1d030703003000b0600414280c0b44100500501d1502d4070018030014000750940c1c4520061403808403042c811102562154008580340d820038860300005451b2881140d00904100c005014860342c4105a582100c40b441d0f441070600a00780a10480e101d0b440c07440302c03a041051100c0b01820740340e0060210b00303401035500c01880756080c1301c2c101c0d06041200c0c1d24081203071200e44502c100075440d811116103241c41003c0c072200513481031006400440c030612102044541d01800f002082d4000c04021301d803041c55400c00c2d001324070003450800840c28103481410313042402d8601002030100c0f50380c032091544010f01c91240b00c0c02c0000381c5880722500500488800480081402c0301b00040000b8603c0030b0418028804044080c07108002511402110014440d652040706a450282041c5140b0a0088050800007042902208100000304c5915404282ea8056401815006a018001810300c110781e82083c5110800c040100000c0d440010514202210390606003540c41d11540c0d20032418a0503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 993768785 1250 993767535 993767557
    0xd0303020c1e01061710200708040609081606120213030b041101020f100c140a110115050a1202060f0a111b180601230405031501050a0e0c 61
    0x11079260715952040c2c81c0c06802c0c50519402404116540c1170012810180e40c0f40b80b620b1600006882c0c400100b160b440b83c00200004017101c107800304000308400e000e4100450449a80c4030010b8144009500b203030340e9800804100c1c00030400c056644a8803001d0b400944101c03024401380c0000300e00f14000b150192012101079086900e28940d07a420708144809050700d05072098107100040e00210f51001c01d855403801c40c480001d01040c0c001c0442540141040905070041040740c5010642200640004004010441e601c40c0306c4481448d01d050300b1140080180001c0c20024807040003240c54000e9031000700c07013550b080140d075041a4004201c0342e2113202c401d20300201c030008881015540000c221114151400d044541941d082d15500c0c2e0002200700900313520078980010a0151030320343c42c10a5102c58103140182410300742c82c054080c0280c0794464001480310108050001c1d080c100021240f50103001c5285e44554501400f04046001d00c0c042c8080c0c40c2d442c50b00141181501030300300e54005081c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 993770035 1250 993768785 993768793
    0x20a03141e130609030b0f0a14041103060f130615090c0f170103081215060a0c14030703080c0304050a15020403060e0c100509030717030309100608060103020d0303020c 74
    0x1c2590034906903803003407070144100c40603081c0224886228a4100069991040ba00841c50701c410b60b9001d00380400609161140c1c0e1940e00c0302e1404104e100c40640030314172940300a440c100400c0c04050522600401b159400301080c4104110600040300342c40f45d95402140c00940380d80400d4800e11404000d070010000503080031200c59100f03601c82d010200c81005070780d444007500058a0b04400e41c420070b22020780510014481003480743c0420442030780000c140900c2500b120f01c24004100150440400d24002c9180c00c410708041c0b080e00c40c4540a990743e0354010b07520b04140307030303401510b44500600010300e10b8601200140402c0010804008601d0f00003007120015054803840c20060b6019020071030301d050519801c040600c100203140740f102503004022880c9078000305400c03290380d00810541c9074544980c01e0b00081c450110440c18002c1403072038001d5070341d0f071400300c24192504100d040260109032410744108039000b03001c02c5207030540b94126500702d41c460b22402c044000c0d0044c0c00c1451150b020f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 993771285 1250 993770035 993770077
    0x305010b010c110d110a060513081915091403042d03030c1505010b1c1406011218060f0516020c060a030e0d02070609060903111c050304080f06100303020a0314 70
    0x1230050081d040100610f51031844042c1c9502006448a4203a018200c0341102c45140d8000245c041071280c83d503812121000070040303400d4a4110700629440c0012115810004081c4110740212445060300b404041c42421012081d0251806403c41440054200a0666020b9080000c243c0e038801440185510074021940c540480380c405501c0344503012034041c43d220401c1624038480c0518154550405417601e49941c03050300643d0b04c0340d051a80141c00d0382d80c40b480130b07400401036016404071030b020350000902c140049102c0c0c1c0464101400028480703800f4a0311040c040e5000548088480341070b00c601d51602c418540a40c0074041002c1d00081d83c0c022044541c480c01e42c0007a41104813562a40c1302e0800d580e5030101071710b007210b00740009007583d07643c04004240c034101180c6040c0740308075003002e078000030f0983c0d2501390441d0020f03000405142c01c010415501e0910421034075801011007165038a00754070355600a941c40740e00392001070501506050b501040d0714a0000d03580d0320030003440101c0c0b0780c0c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 993772535 1250 993771285 993771287
    0x30105240a17011502100b03030f0d021c020c1009031209050a0203120307020d0507021807170c090d0605041a0c0403210207050d110301090605010305010b010c110d110a06 75
    0x121184141c2d242804044000280d49030602c01c401c1e201014a030040e00000048200400c0503010b04074401e5010710040000302941c030100c4004018490654100503180c503800c4020541094101c0a059240b40c01404195002000810880112108003000080231070040c64150703003403010704200300300c0d0a242500c0281030280100e000c111a034800c50503184850090040c2c070740280000d5910324016441100e00e0007100f4042c1000b8040e5034001000c0800d250311244002e50403000407038040000500d459030008039520041000c0d40c100b981c45009600344190213001c0781500d80c06503006044181c840020500f40b0212aa40c804041500744030300d0128034202c0c0f41c01890764441d00c801c540c8180303c08020903509a40310b003071009010081d4054a002854001000021031080301c0c02c1e1034103011401c0000040d80d00748140855107101c1c60002c5102e6145041950071900e0019042c0e040c00789681013140041d05418083d131848404455800a000c150f09000c8135007120001059040098a0f4010410f6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 993773785 1250 993772535 993772547
    0x1050903090603370b1005190e0603011401110a47070f0c0f24020a0306060e0102010b0918070e0f0610090803070209040627060f11030105240a 63
    0x60380400c4060040321759060078010300e81c008448440001d039060000001c101c4076400d41e90343c84560381c0340502120607a4000100541c1c000c0e0b01401d11405d09104204e45e035600101c5028940c07030030002601c80310034241c466480a0700c0b5504490b034955000d014180e005585400881c5c0d4105007604a0b140340040041070b45d0304040152201d1000c100c640700210300e281d10600034084002d40c822035050b070700d180315613030720908545055020100340100344424081602034406440503240c143d801240151a00c0c401600641c1680c840c0d03411a414a490100b071519403220054005400e004a4408009048103490601c40141c0000084041c4103050000901403805082d0060400f1200c641000018a0095508034058810405680c00c284221000b622702181c21651080c01a000800c0d0f01d0380c03001e516440300780e404650402d9001014041d0040c0542c51150340400154081d00300040b45404070142c03000d000500c00e01d80310310350441001200441d6540354904d00f0031044032143c1c86144480002d80380d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 993775035 1250 993773785 993773881
    0xc060403020c0d0c030f050307051b0a0b18010c0201110d02100b090108120a0203090a0b030a05091603060207050106030c061119080306060a181508060301050903090603 74
    0x1031080042c101c90a141c820100c000b032550081090075090b1441d0394494407641c0201080d1030341c1c001400601c0100740c040c40410040115008800d1011010004228206815402c029103c140c28441110081c0d0703001500719084400342009030350465180300480307400c41c0a5440500a00410418090103500001d5100c0c01c4d200d581400c1c40014108810b00c0000003091162140c00e83c0000d4101080140840c01000c03082221320640303107030051000205100802d66800901070110020400c0501c81180c0301d41600700e8040405828840140141103c1c103040c0c900001d02540c4d800a145020800254804001168403035120384a243d030314400030b0b00703003142907045140034000c50001e04120b42c2d0960b024031105a1040c045811a19244140709864000e0700121081c0b10516501a964007041681e140090068526044031031442981c020028000503241e503000fa0304100c144190703104040182e030180d00c000e17101a510396503407408910441e00980500c40300542019417a44208088554001c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 993776285 1250 993775035 993775037
    0x61e0d021921050604081332090123031e06060112050606030403050327032d220e160e0d02130c03062106050f0c0414060408030c060403 60
    0x30546509070400791689400b164010003540009002038005034410024110740700e03442c170554007115203c29141c200d1007000c0d0024034510345007852582c5c145043c0c00704864000f03000d83c2c418210b949444101c3c0216a80c1d102c0b49490f040c1001e05c3c25425071010044510721140341000300b0301444109804070f448030b50a54003140090404013102d940c41155005840c001c420280100740703980da56480803070b0960000340c64030f075000000103030345001052895151190088000007840c0d6910703010141c510100b90010b00e00e90f1065841d030384c60b00c20200304c01c01c1d141403100b070f42481800b500c0b5850a04004140340d42010001003020b00c1802881500542402480b100d151280302079030311941c082000300780035890001e40c80b461184005030800400c0c0c0220740d20002508003c541a612504d00074242d0454048054140d03902c8a8540c05003d42401515041a01c0720390026a5003803000c103210192180f4011241042c42d000440e4480307440d681e046400610111090380e031520f84503c481500d0301c8007518258 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 993777535 1250 993776285 993776309
    0xd0213080c010816050304020402090d06051014030a080a09081b100e0d0f151a030606040209013216060c050307120e01021b100c0206061e0d0219 64
    0x3907100d500901c18540130b40901e40ea070700d900340040c8504603820743c00280200d0f0442c1d024003c1049540300c1b9201005900d00c0780c031000c5514544402070004002c40341c2c0c0019000100c0c070755990700741e44012950002150f000a010341d520012110b0541d059515640581c0d200e1050468030a0b0182d1481508030805404032111510446d031800d040780c0301c1d0031001d40207602100c407461042c0015500c098442c1a00d10940340501c048003292941400c44072442140d4044490302c804054061a052061940c4180c04560031400d200c03020000a0020304505250020546481003c1e051054008900031600703964a10303143da1607500d5010300445400d00182228041d003800d000b29441409a02624418400b40e6a0058100c2c00c4103c408090181010078040c1c5542c20003030400b0540d00c003507400315803040c040010401c000404114404a8002903d62011504180b040c0030055403103107001700800000740886041d02c4050340000e40c4c43c03044444005c1d400064507840c09414800750107500300b112103841e00710f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 993778785 1250 993777535 993777553
    0x8090102040f05010f1107060906031d0705061605030304060209030f1506010f031e020a0801090911090630010b060403171303060f1407030e100509030d021308 70
    0x115090380075501401e03001c210b0620042c022544122030144c080003003031800400404001c0c0e501c40c28420785401c0000050241e02060080a4040c022801c082d507950100061a2604448040c1c8132800790003110301ca914000782030442082441d00c01c60406400c202580da84c1c1c1000e14000d4000e512040c1d1450090080c1e9913030001514011030b1001a94283c000c0140055540c040110f6018019141704014076594040d803030900591882031140c01c0e00d20000041c0e441c54018009090340405912030320589040220a10004842c204508881c480a07222000141c0765240000d4116108110802c00e0342c0e05980802c080020b4101500341e41403110008000c0050f150043c0905441903000242540e03030004140c59841a64800511500b50326804c2c800030b0039165982c1d0402c0e180c02c55180700400792204005000004202c030046e80003800b40c00e04008400c441801036803110407024010683e0703551400000c1d44400c042c8101c56517603c1402d0215550704904c1d44242801c4624014690580f140e8549 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 993780035 1250 993778785 993778801
    0x9150a02030f04030302130e043c03050a090302031015080d17070905030303040b01260c01030e211315120c0903120f020609210708090904030f08 64
    0x2124000d080e2807215942d203654a0710107030065480924000e0040b020150700090b0b000d1228030560003140725406180007001050750b0303e074880d44c0c00c011102d8194001d80c00030124003485119a21890390506101d134550840381019681d184141d4006501400340028542d800d50459001ea6140421b052034640c0803a00c40c03500a981e45c1c0c1041605000c81c0c0950105003c40c441d5800e12a0301010504e0203c810075115808281160403ea50444410710180f005218140300802c100d111000f504c02c070490700040d25203c1e6a41c5406100c05c4078141545d0701501c1418040520144200110000b80c00b003106022000000040d03000741c4851985041c1800003003007020442c620b20181c2e0350710796a2002c4142e03070360484a0040005440c01c0c0c050000d180400030000e02100c6003a00d070031074651030303094100034000006420007800504400b50707034110b10103500c0f42c500203a416030321181c445080309840d100a8600041c0c81c2c400d0800407a07014131402c003008101a070080c95080c0c824080d6454400b240c030391a403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 993781285 1250 993780035 993780037
    0x1a010b07050f161413020c0303100603050630030c21030c03041509051f0c090b390c0315090a020411270a050901030503030109021b030309150a02 64
    0x10352450004201005110049071948010b0a130080141e001800d039542c2003022039200300f840011942000c01046200c1a00d6441d506c018111420144000e01d0000005500c0380c0c160302d81d00062007079148420b01c0c00d0342c800820829101d003070011281e588000300740d6550780b0040300c80d0880d41484441343c075001c200c0c031031003c2ea07001d48895070501e815911070b40d913407000490f04842d00b109403c1e41c40316903a0209000300024921106100e801d9481d40001d401c1c481f00b038a60811040f000e001d141c4104110200d403000884d09040f107408200202c1c0040804600c101e0700b80c0b03c0d03900361100481c00c81301901c1070300850840c0307100b40b04504823520b140000c8590300d9543c1d0210348082403900021500e0000d41040c1c0c011081c03001d9003241c0640313401e9102184610002130003c81200c0705907103400c200110b00b45142804080d24040701c02d82210761442d5100da40d203101c140100c04500d900449c04144c1011224407940c48034100c0c0040e00e48074a40f03045e031255520030780d84070425424550004103e2501083c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 993782535 1250 993781285 993781303
    0x40c020f060c0c0a050a0b01090c0302031b03060102010e0304090c1106070f05091305100501020c1e1e030318100507050a0b061210061509060c0b041a010b07050f 71
    0x48060304096441d10b09204840c1c11840340200f080c083c05550f400082d00510452800381c0c45501517100303a504004e01042200c6201c61400c05151040061142031004003541c40c21100c001b84403690349a60350720040340500b19251690042d4400402c0209d48100250040c0d0459182641d6195032103603088201039494400341e500358089280610445075461090f401445140405080150b88040c0882c5150440700211080c5000301d0b541c90040c0400d40c0d0610031405203080864018801c4034034050112128440ba0100f94070031400c4045d1080704c440300d002c45040b010b44c005c0a40751143e801e2030326810505e0f030034140f0078801c40240342e01d991442e000c0c40c02c0e211403581000040035101c5069450721640b00000c0c04c40b44c0d20103103508a034010440300b0000c0c001c40d00d240c45130100f81c01d85000c803142c00c401c16003040c907030520540e4002032101c554008403003c03200c0c0d04003000c2030700360b1107a0800c94810300c0546a11103078811101c00200c2e80520b000c0051004c07910a204448080c2c50701400c5507141c5901c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 993783785 1250 993782535 993782563
    0x140405030d111309020721170717010602101104061b1103120a08100e070f09031203090b0c04030f0b220b040311060c0405040e01060f0807050a140a12031e02060105040c02 75
    0x824005003004e02317101e007455072007111810200040c07159811003080c109800d91080006034010040c111004820b0301602c444030705904078050074a42400c602604503c07000c0310501c101442c00304501d041c00214106258900005070680e1719862648440c04000d03030140e03002c040810001808561136010040c0110200e4140313101303002003501c910100302c0d2010794403207490003008807016011000c00e00080034404113401e251000200352172645030414078940000c044c0c660304402440708101203040c0c5803951954542c8101110865550815510220f40050700a40e4507480c0c50340c00c1208002d44201000c1c050340c000c0d22214a00f01400d1800395075444126031002c06c145091004100706e0401d500154030100000340041946601e54103203159a00a61707011002e6688110401c000c0c0d4140000500b0207000d1403903080b6003032202e18001c070700c9a0b1894803c9001c000d030344100150500d840b903000644116045040c03d42c00401c5030750020b55598083c041d1502c6980303801303080a20316000040c814114100303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 993785035 1250 993783785 993783797
    0x2031b01050315030a02090a050910110703030e12030c0405090115120b0d020607061b051206090c070203010203071e0201020a1709150c0d140405030d111309020721 72
    0x60354190045101c03443c84880c2c0611901520000607610060764a02ca00358a680015552500318003c5142450340c1c0f4035012623a20f4400703064203215119088509890b05800c0100c1d0414a80c00b000c0d14211031564010442c1e18044140694209070070001d004440e812110f010003662101c43c015102d001e1900d00c880418106c03a602d00d039031522038001403050b0308020001c00f0f80d20801e4000c0b80b0705a200500444071035070344a500084001c8501000303a40413465191490500705d201c040300b01d109101804c40d80c0700e003507603200041e500030301c0034110b840059018000f03544034203182034040e12408000d817118003031000f400d48584071a8030501c2910b598120b941d1b20321101c594082c1c400c5015800240c44142a405610700b50381100b00701403807140c040c84003010000c3d41c9103030a1329844100d0354100540710446500381c0a100c003140c0000203640002404603070015442880c800745c1c06551080d80c2c4a0219641d0124000652014a0307002d001034030f000720b5031740090380e600e080480c03100d0304250a04000720303038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 993786285 1250 993785035 993785041
    0x2070f270c02330708040b041707020a0b030402010e01050c0a030804080d05040302070e010803190509180709051503040b0103030c0c05041d0d02070e0a022203030305010302031b010503 81
    0x1080d4001c078240400358019030307110103620344032010000c511101012807910001803a042c80402e40c0c94503940100303d40b41248003400c041d0343e1404600c2c40580080c14000c4c02182d00000091a00210b61049600400000381c5a80d589148903441c1c00c2120180c1c0443c08c001d00007426540035400310b400b4204204040c10b480401e40d038007651103070000340069401710303414021024504007134828580901e010f9002480d0742850000040c01880050700610144c0e001071000302d02e1580074486c010015461030a000703442d1a003090100c0c03004110b034854401c0402000e400d010b00590003490b014292a000d68240010710f0f40e412601484d80f00035a00200801c200000400120f0300c10b141c2c02e0401d500c6003110442c1a039a510002c2d003540c1c0925208400010712005540c0c212208102c9072041c20f0190024102d21403800c1c0354070034017000c002d01d0402181d40000f00c0c07124400c40006610302200f24103c1c5810056268100200100400d0108034041e200c0d28406101c880b044c1c0d500d44d00b0900059590a00c3c542d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 993787535 1250 993786285 993786359
    0xd08041707030e0409050a150209060901031a030a0b180a0b0a05040f0c14100804121803050105180f06090c0d14030c0a1509170318070602070f 63
    0x54001c200640c108502502184042d075118003855000c0c41c002c1c8018500050142040302e21510090302c844d013428410800800180c0b13804043c0e840540013400d00003400d08100b210b030300310080017804607941809441005000c00c088106124007a05c0d06e2501101d142d0340e00c1c00c01965640c0a0070014000c0d4040300c000602290b040e82000d540b15100f6540c10b64500919500d07019030340c0d42c41d0030194440b0317085200417000c0d0410042c0031403482e030076190029180c10700381c03220000280414000410060a0418155000f0400c000d640040d580301000b0042071500410307514000b4806448010280540711400d402842c0001c3c00600442c44100a04500c800110411240e10701c09801111500c01c20405e6007407109040c00a840c0303407800440034041c24451468100360302480916030145003441e00c288880490140e8801111040350360403819900e0b154180b40b42d03400e81d400c00a6070000d2080c410b001c11850745c08100703241120f100159807003589844031314000c1075050b03410210000c0715496060742c00e91703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 993788785 1250 993787535 993787537
    0x9141015051e070c0303090305010b04140f0901110417060a33030b010e0f0a060b0d150503070b070b01090606120207020103060b0d0b09012c071b0b090d080417 70
    0x740300b5914509141000703c0e40d5801340e04601d81c0c415000304908180400038081c0a0003248080030003110200058901e4070701c0e072107150350f01800704168501d010f400280c0000b002d5202d03600b54000d101f000341e12250396100108614200c54004203060003414007040546105024006500d44140088401a0707084c210b880ba400c86204a56960255140700000100d911900564080c01c60b45d200142a03140013000101440400f27003001a5407858210200000341c01c82064400080c1e0300680800e452604c040e2500da42e00c10760300501d900d40900e0740c0024068101800a00c01103100c1c400d801702c0c582e60b5800190407281c0c10b20440d800f040c42d110160800304025801400340e103205040003d501ca4490f00b00e040e4541049540003c00c40c1d880ca41e2401518064810340e0040110010406004440c50300700b254240d4940e00b02c1070308070b54074404660030031b00414040741004240561003200640c1c0e41021450444269a224503074090422811a164456002d40344503036007007099089815400b900188013 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 993790035 1250 993788785 993788827
    0x191e2012070516080d390302040b030702060f0702010b03070302090606071b1d15120f030d0225020924030118020103060b0a1d01090914101505 63
    0x10440c04202034a41030f500f0b206216010350140940079184d0750000c175203200300d502040c4401c02444c0000400241c1c0680c0984502558005000541c0d01000303840069000e80259040b0b007054140110801030665030004d001841099003040107569601e80240581c07c036100f2030141c58240c3c02510052001d07040c80c0c00710540140020f00351034542605030300c81701a050b01807002d03255070001000c0d04010120f01d92505400511230300204180b14100700c0c0d0307904c1c40000081c3e101c40c011031001daa5803138448400e000c0e2441244a000940342c2d2070300310001c0c0100940c8810340c203d08814004409045c691240f054554070907501420703100d40c68845010401080003040030010884010300c500d88401c0c0c9007802881088680c207401880420101e200150982d10141c000404100d000e128990440e513202c2004d00c045605240d10042c003d4100004803070f000e0017508141006030809039412071074441d00301c9451151400070b00b0114100d0300ca10300c070001742481d4003410001400c240840c1c14107440c440d440c211 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 993791285 1250 993790035 993790037
    0x140307080601110a0f03180e060f0f0a0305061012020603180f1e0f010209030a030f14040b0d05010602010c0c03120b1c06050c0301030f0b191e201207 66
    0xd0032001d031802c5894468003200032240f9201c100560f201b05504108244020030741f241500300780c03600709007030304050f842c0080510303104900c0c44030740c00c9850710343c140250400030004c2d290b003060030784904180c0d50703500080d0380c40003075052514400601d8106c0221401d408907070082a90745980c50343c80b4a52003845d030031081614140107070126042c03502001c20440401c0f48900c00024042500116400d00704080c4007407090650340100300c82c1040340d50102d8040c24080d410b04041c50000604407044541003600542010503803000940400c8070100034001d4401002c10300410f1200341e884100803400d81e5800c00c03103903011581e160b032070f080080e020359042040c01e1040300d800100208140001440b0301c0c0245040c0316140d172210312841c00d20851303001e01ca5200c0c0820700070070301c1d5500d035540d42d01c1c1d40d1030f003640080c0800c2200760200380803d140414240c03d80480403810300902079a100c505048042d00d101081c9102e1900c5200601003001303c01c400c88003502604d8031420013011004010703003110001c0c1200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 993792535 1250 993791285 993791297
    0x140a0506193315031a03010504030e060c03070501050a020c0c03150c0c330a09050304181503060b010908150f1e0a151403100b0a09110316140307080601 67
    0x12440c2160000c04400541d01642c1c003240c0b00175451480c20b241c02c00034503040c0c00703a41040300b0000869080311254200d000c00f40d4803196074040c2d1814460a41c050003800030415420001440100401038000c0c004514410003030b03886419000c81019640c080700001eaa007011045400528200003440c042c0c1306051091055a85099452240150b021030030b007808800c0103030044e10b1300c182c80d041035a0b1951202a9845c200241841a22003c4c1d0707a00551048030304500690800b01c1e1040e1031078211059030700018515031b603019220725100000e003494046403400101c11041c0042c0071308000807080700781450a03800c045262a00300000081003c001c0c0700d2074110524282000903800640301492240c09408400074a058007148100e124403032940c05011a240d0f28010740045c3e07680456001200e0000c243d0002d0034580744004284403185a5001c1031038a85404c4c864030f402a0120001c520940d410190f120a03035141003420b6444000002d54540d00c200c0510014040c140614882600098141852 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 993793785 1250 993792535 993792539
    0x5012f010b090a20070c0902090a0302030a11190506030c07020301020f070b0f070809100902010315090e0c010207060c031206050618030d0f0f0c140a05061933 70
    0x881d41c004803c0c0e8004110b00da507141c1c000404048050030312880e0300d0000b2490f143c40c1031a110390b0649402401000403c0d40d001402d030a90f076075054504402150f020781520a1002c560030b040d008942c0380c461540c081d80840c0c02c1ea400a140618042058880003886c141c2147c8400440e0740700741c2c01080040340c05643c2000307000380c80c045c842c021b00781710392044031003070403a01d40000000808880944a18103016007602408807100002c01e44014052140ca0001150042c0c0c2c00124094958032f4902d904283e104180400d06094942002030341206820840701012040310049030356101c0c9125050025800c01c944400080c4500307040c0b10b52001d40e2501050a035220b00000e030556000c00c1c44400302c0040882c00c003000381028011030354040c1282c28211707041d20406a002c0e0018110041c840104420222103804005141583c400c0b40c0900204440d07020490307181099a0b807a0580d02403044810114495a0365100307801115030907002d00c001c02503507401c070001d2400d50381500028a5040e07681e285c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 993795035 1250 993793785 993793789
    0x6060c01020c031e1201031e060203130c050d0506011a0c070f061b0b1303090e09030c06180318010e190609050108090d0507080f2205012f010b 63
    0x240802c00c8584000e10f44d41c05a68281004003840c0ca110b00c50403100501400c0d090300c0b54080d516044981000f818400c460b05520181015000100c000304006e10100c00e100f040649800c001000a10a0340c1e0405a15100e00c10000b00b0102013000910b00c0e4007080042c410150704004809100003450318040c00e100303821042c07a0a211464000325103519000c4010403040c1c0d1701c884140688103c1407501c1072607860644401080010080901c0f1501c010032142504041c41182c6d6000101052044040503040465001c0d44030303400164542505d2141c900071030b42c49862100c1c800c20440c5004000d42c604004004007a0318000440c200707505122103100c3c54070481d01c07409060140d9000c803410711100103003031200c0681804a0764014604014208042200701e17040050707100c0b410301c01410120f854201c54070345800144107000f2214400c40d0080f49040a44000d84d50b000000c0c1580c40744001e040317031258011607142e142c4010030b40c0c4803030b009906205c11403410303841e80d0110b00b0100c0001c0340072040100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 993796285 1250 993795035 993795037
    0x40f050f0d210b210f03070b0103020a0510020604120905030d0f030507050a0210020f0f040801020301030b011a031b041e05191d0613060b070b0609070f0806060c0102 73
    0x180c41c0c00441c42d0000c4400a040c6201d81c91400060310060400400f10000d010880305400c20107040c2c2c400c13200c4488008890420444458901000301c1100d550303044610f02000840b42c00c0c48103d02034888000089401c0c0303001c80582608a401c0c0d40280107658840c2c031850700d20085800c03814140030707400102140b1920f0611034919080300f0341d1078520301101c00800c0281201c00041110301004414019481c0866011031031440012610401607220509061707144064403440c68040710840d03001030300142110064001d541240e0182c5c512030b480d40e9844403000d14107400c45c1501c02e2a407004000003511030811136900c144020001150034100b076100e80030009085040c900f800303415484240200894a412070420740105c004242c00300801d89000041c6600e00e100e906e01c3c20700b620003540011002c0c0c480b880c901050b083d041070140b2982d80d0f0790740382020300e0703201c0e600548030f4025540c002061405c0004100f0b00460055a509e8131501c1142c0048540c818090402d80d84614104481d100c4004240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 993797535 1250 993796285 993796303
    0x40b0918090d05181f0f0905010e01110f0102031f0f12140c060c016906030201030b040509030a030b030102070f0b1915260f1b0306040506040f050f 65
    0x40100c0142e040601c2d011b8010509848000d082100340b0780103214591340600d02d0b50351103601303003007910311260780980480c20246141d00340d015542c400b2023000116044ea40704d4008081100c6004844591180e00442404800d8040ea454034120096100c3c00075402042c03502035400b9241c01d44600d0f40c080030000e00301e03a000094250142c0c1d1a031020a41d4079034807039480c0b0055142580810700082d1664551904c16648454808144220aa0543d0110b0a5450442e030200844640100030300d40040c140004103403d010582c0040e18200d00c42c182820244629802100008015414120121011406404500b402d541c140d5003c0c048100025000c4d185c603244240f05400403551480c4c40c5c903c1e900b51300341b640c081c401c155042043c589030303034100300b43c000c0d041da02d51461961480d60140520380d0100110b8882e60302c0c9204185100d041c591011984028440c0b0703142c660300c0040c80440405540e0700c01a1406040c903041100860001501e0080c6000c0712446281a43c1d07201a8040c045400c2140c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 993798785 1250 993797535 993797569
    0x120b04060f1509300c080d0305090303090c101704060209030c01020a080412020a0e070801180b0312070c0e1302031204030b040b04021203040b0918090d0518 69
    0xa60414448507410300b00c0010001d20740c3c541511010b180020b0091010300206910b800d114050740003241d04d61007812081045a00302800f000050f550300000d42d940c210780065100060b00d460301144070810040112800360f00f042008100e0091008100001c02190310247c10500803071301d5000d0380303615111240c18821401280c0050303c1c0e82c00d0f0380515040034245a0141d0454014044882c006444007080c2ca003550b8041d0000c000e030038068800700e8260255600b04242c4080303e0002c002a40d5031083d146810303103480718141c494030608078070444140c07603e018840e0b5250300002100044113000501038a205402412450344450b941c500003800e0380400d0b601800c2070014440c20106500741044182829503480c90b00358a45407075a16080c030300e010081c1c402003030290003401007010342da910248251032043d511b090b41e541e15a105080c00b01907200310740050154000c0c03401031031a0300940014600c1800c030700002e0110034142060884907988000080000503001c451f4a150a4075000c140e88020500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 993800035 1250 993798785 993798809
    0xc03031e180203060105100801150516080c0f06131b030804080607030c08041a090c030f0f1c0807081317091915050903070305011104171507120b0406 66
    0xd980141400c06505030865405821f100500c001c00642c0301f40e026044441c1907041d801640c10f00318003100c561142c05409008111101010024004060000c1c00510401c000700d508698400d0b604945602084408040310820761541f0400309030f40c01881c07602401401010035966413241c1e00d241032034015411103081503100e5030030801c1468041c030904040450310f0400700c0443c5443d03541e070103080c1311000321003600c0c00200700803071110003080107140203200e001016101c60580301c16085641d08001510010988a00100450500b20f240154403510000390b4424190b940e0301d4005445503680500f0004840c0d04070040e40317000c5110f50124100141d2080c0041e55906920340800004008000301104079140e5080c042041c003610703510707454000410341400c0e600d610304500041c1c1083c40c140d20280080d420100c40501300350301c020041c011b07a440014181d0340c0f0300b015040c450f5284000c0007050b0b07588000c500482d41c001d0045001c4078915503c90004100d03c05880085015100c0543c40a985404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 993801285 1250 993800035 993800081
    0x6061308060907360b04021c23090c0d260306040621061512050f06100f0b03060d050319091d01030215090627100c03031e 54
    0x1100760041340004003494901c03030242e0300f41ca58a10441000c40f0000702241c0e070380c5610a10a44854061b81c89107070041e5180400c0203440003608000d4507450546c0d4980b10543c6440110651003095180c0c0506080402007241c0314048040c0700300c3c03021004090302ca000000f00302c0d0b88510004e1000c0880e8012240d15240c603820400e091006559041c3c00080502038804440802c1a00070b4a00c0440d80340c000c540881d091641804c40e103199074503904252211304828942e1024041c002901d0707a0755441d07400031910301b5542c441322200c0000640c0204111402450010000c40c08114085c540004004000c3d092091490742c5403488c40e40600546070340c285900114104141c1c0003403240c801001d0700350f6a103602c4125000240320320041408020300c42d00d0421b400c610711706212402e0765a8030001030304d80744da265818410400301d950f40184e411507812200032501c4a9003132001f02143e401c0120f8a50000003415a54242e000d4070202e00d1000f000c0c411442c00e50010325090083d00050a1a8081000402c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 993802535 1250 993801285 993801299
    0xc0905011b14010908211501171b040303090f0f0b04420f030501150809010b040c020618010917030604090c060c150630080403240504030806061308060907 68
    0x40c000c00c2050364260b210345501c820f036000f0b00c6c002c0d120040c0a40700d409034ad8440d410034841d04140d412035082800f0100c0c01208040d0410782c1041681c2d403d51402d90304699924440409501e940036041000c80e060108203c114120030380c041d55a02140c248010349103001c460020000c070541c01c82100c281e07846101102c2c141e000b03000d09010308074038079051010b1b44c1014a0309901c0c0803109114010440c0306000180768482c01e40c01302c11501c400500502c2860380001c0029030310380e4196221a503616030f95001d4604401d0521841c42000e500c1490030070048040415180190401845250030540340c50501001030508082c8030041c0c451519101c600d00b001c0e09000d2081c00c2c0c8a850340100503c0c095007408104a01000380800c144000c9400700c1e445480d031802e05401d02002002850108041400b104012800940551102d52051404e40024071302844005840e0301741c030003502240d090008105d903410040e000b0b103001400059415140c035036600c0300038074001044900d01c40c40d40019030148052 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 993803785 1250 993802535 993802597
    0x18010509070309120c14011d1c0207060305060d02220e28021909020702151201060311040503060411030c0a030803010603050421030c0905011b14010908 67
    0x46041c615042001480381d039144801303140c41d4202a02032002401d041c4d41000750384102aa46002d14030003d011071145101c90110340604c00c42c015003070340030b0040071000c10004011155605c0c00315500400d20580742410a80061001400d01600848510710340d07070240e2034a030700804070350f01d04d804440c20001c121849681200c00e1081c01c000d07980c1240c082d2004115442d07022880b140e2400520401036410b80c40040e03890f819a016a000008507860002219503856010b000054001d5603003040c0840318118a0500b40f0800384540196041c04c401404802e1081d0b02c20618a10f69102d01c0f4a01a00c403c0000d213803440c120f8003164401070b0101c442005044c2440f404651890035280000c46c00c0c11642c1d08801800140945000c2555a03070006050000c0390704602400c032660f5130604000d0000c500300801030140c0c0340d80c0d00c000c540d41000001e9207521680300d5038071888001e02c1403a48106155640300307201c4907840c6110706075901c480350f950100e100000206441550061143ca140c070681040c4805 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 993805035 1250 993803785 993803791
    0xf0d12060518100f0b0d0c020c0d0b0121150b1203040f03210203041202030307020d0305120c03061c050304090510140a06052d030109060305100506060a1d18010509 72
    0x10380400030b070100000c40c2c0045c10388004980540001c1100809000224501445040d0381980004144181010f000c1241c0841b416240700c104004070343d40d9070480c038080d21b15022800800203d041c40c03d001d1185200d82c00741408078001040410b05420000084c0e1654000b03811015850092500800400520481407200c1c0c41d00c480380c3d0300c0103510260300a03440b03000341c0c820344400d101c5a0001c4811540c092040301c095943c02441000301c120717103060041060300481c8003403905a01c602c01248080003018156481124003c002e02003103d8542244404a100c20204030342c503203c184400726000703402e40034040c45410000c2102007490304d80017024882c20821404180281700c842c0c03050004581c440301312848007900540100024400940ca0310f44103408903041114000301000202d0101c1ca030350490422a4010422150002241144041160805e4990b5a80a90100103d4031081d00403401494407801202c1840301040d200c60115100c080c514201c0303002e410211006001514010741440c1d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 993806285 1250 993805035 993805049
    0x3051e0a0b0301051e0f0c04030b07110d03050103020306070c0203070f0e101d040215210a0c020601080304030b1902040303020109030f0c0308060402090d02060c010606110f0d1206051810 82
    0x1001d084070181340064000003801b00c070641404c1000280c04c90301890112001581c1c04146003026142918000304101d640d01e28030941c074051001d660504900c240034650589400030060f100030f4079a00001d444003050f0103022601405058030000c1c0f02c4c112104814003c1c400100319040c21710b800710850080e188a0340100c903645100e0f00324140040f0007001420f501c154140c1d010031112041c20014806070060321500840320b28200c03501801802080e515a02520704030100b404075500e000d0307040e40c490b0402d00412000d640300784001c001150301e0f45c016903008140c55410401c0c00b001c0c0d010550030390f88250010f60250391140d81450405601a070488950011403030503001140e00e544c0d006002040c0034013918400c0750003040040b029510380c50010089540181010741e901c508001c0c3c1c3d030203072489114000c0442e40a0400c0c440403036001c80d860355040c1880c5d001d0305185500c04000c0c4c40038042c5449074040300e40e50b050003288985500c1c01c21800700d8910400c04445160050051044410320f4202c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 993807535 1250 993806285 993806311
    0xa14010807031e0c06122904060503030a1d0f0a08161d06040e1f1d030301050d060203041b1d0c0c0c0d0f0f201f03051e0a0b030105 58
    0x81d0209050010f0401907541074501b120f408491360150b003000d0040518416018030f040b0703290b14142d02d4880071091808006450134481ea917a2902015100d004808211000c141300013007405002c000740e85908903000c0b005106614292450020a50315049074002da070460303004a21103004d5401d094080030040940f40e03c12100003c0304035214541d500054000760249454030342c00c1401c43e00a12030703c01113419103445903105020b41501030010340700c040d819540c002e00c40603541e04212380110840b0b050b00c10150643c513551a055468000a40c0010000e0707503a180c100800c0300000e402c1010220003810404411400c80242d02b008582060000d020a0b02c1e00108000c4d140351000302040e08000000203e40d5031101c02041c0c18411925400070000601c0b0f002101881810403002655070300ca8040c20952055151801d481401300c83d020ad4040981c40404100c60348030b40b1440317600840c1c1c0c0903680130500202424111020202e450003074a1501509882e00703409840c90409200341c40c5c0c4010345811803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 993808785 1250 993807535 993807593
    0x507061107210201060e070221030934090506040b0406080606060f04330810090504050a32060c0a14040b04032024030a1401080703 58
    0x284102850034082c140200466800c0c02001d000390301c082c00401404400e03542518100310000d4580040c4981c00d140289052003184c620314071901a2481803d58000404c504a0303614041040b150320101c1469003031280b01c5400240313080200d405002040340e03c0010032982024800c000c01d95a0150000340190f05c3c185040010000005080d500003100350340e00c40c0d5940202143c014584225040018644000b0004011180c4008040d1038210600201c514041244501c11180080140e45511401031180c60a00642003950f018030b411074400c00c01c441040c0f8013640c450000c102c3e982204c080a60600058083c8088044040304004d5100c1000c2d01040c40c201d0380c0144d09015003a032960400c4900c080c950040714410007101c02904103100e410303840d1070b07a0b03142071950f00d040c106400440d13004002c0511700c1406e0440060440d500060140c1800c0d03130141070790056a80006104194030758a1707180c00c401485444c001e003400780231090301800115082d03091500e44c03c2010604c85107038100103006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 993810035 1250 993808785 993808793
    0x91403060f0a05130204050108150c161502070f0609050705010903030518010e092505190c06020f0f0d0513050a0b04051c1e02030405010507060f0603120507061107 72
    0x1d0346a100c1a007410000b8903449183d54502e6080040d40002d40140c500b10021408500c0051240c02508080c2070725079a90781c4001039918203004500541c02c00794804402d0754001480745c8120044640510b0f0014244071359515071014103421400d0903558255182d103440c0070f10106006e03030009000f00707081c4128051301d9941c009116100b1000441c1c11900c01180040c0180c1c45404001d440d802c00402c002006d00784000c00c140b034030312201c200e87da149500d54240c0418a000c2d0083d10302081b02c2c031101c1ea101c891104810394402c20302007011903403680e003004000d00390055540135054040003c45281d4494a803501414203c45028224520740c20014a80000150f000188080e40319030008042c141505c176841c12520704503201d5440b03c04450211a5250100d034055520071000603600385502c003540c03880c00203a031280304034016580002c0f410081200400c410303801842ea040c00401c400034019a0305e40b00c1c0d2111480418028001501c00980c0b0010720a5500909400c1582845281d203050801e0761 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 993811285 1250 993810035 993810061
    0xa02030a0302030405070807061107122a0902030c0403050f06010b07020d052a010f090f170a02030106030302010b013504110310050714031006140705010c09140306 72
    0x48503020150004001410030005110401c020000441250380316a01c03100d0103071083c0402010540b05108080c0f0015140324100b034641c05d00382e0810a8810780104403c81032180d61404c07585c5082409901a0000e0001e0443c401944a54460070400e51100e086142480c00c2c2202050300a220354030500040c490000101c1c00c90740a69412940c1c401c0f0320301c181c44c02c1d07130411084c05014150441c0c92007004031030004e200888a40c5203002d0343c0b03003104498064401d5908500780d0140c0c00202a100c1400d1091f00500140e081035445614100c408501c010340c002402c0d100b81d500200e0040c2d4584228081030350300141c81d01c416521030002d054200310502a82e4500f540d02d1440e071079224141c000402c0a1000b007002528240c1c002909889450b100c0507100c202030042038504034009440003180c0d900491100742942e008030b11412281954901d80b140c2203542804550320346408070820000c04000500c00d214200e44030700c903034403800f9070103192030680c8c404100060000e600940040040021035144c020b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 993812535 1250 993811285 993811297
    0x807231e030c0d18060606180b031501050a0908030313030305100303050711060f070b10080118060e03040e100603060b09030c2101020a05041703090a030314070c0b0a090b0a0203 78
    0x4040040c95081c04c508008143c000d0500c090318003442c02c50b012a080740c0c401c004100c1d040300301000e482a035a50748060201807200301d030342c1c490b00c003003600c43d0641c3c41d840340f0001c20554081b45840c0000644600301c0346d0942e0b0080c3e5642c003558400841762010550180101e6601910000380b882c0000e103103440c0507000780305c0e180000703260174441402140255240010b444c0300088000c0d0191303d0f181a0f10300251403a0041e00e0100b8160030030301c0002904101402182090700d20803030180d0081202d66510b502a150909450880340005c0c031011590f2041d104186219014501c4a10542031410380094105ea603d034100c0350403005d041108121a0301c0010742d5081080301a0382c0011083c0e00c0302a81c0d08443c00400c00000203500019001e01d02e1580940908152403004000e00d18044a042c0b8881e034901c10b40c542d09402003202041040860700031050f08a54050340100302d4079028150703540c1c900c146202d8010040da640c0100e00040c24030303030000e070351005000b030244c4030b901c0d00b100d211001e0341c0d81c0200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 993813785 1250 993812535 993812557
    0x305030405072c150f0f1305071d0a03081909090204120506130b1305010b1815180a0e070e090d14120103030807231e030c 54
    0x20608101080020400401401c04200214074400311505003052000d062101158028408204040f200c0055402109802000795100f0317950201406640d50b410260316500c100c00c40880010b000c99406224440c050315961804d901d40c9446880b15058444103520340250003c2e0000d10000d96850111480d001d0241c0c0b811034291a2480121414011030b0400350303525001140c00554000304a06c0081c2d01445041901d0b01691442c2d60070f44520984000603080600304008902c1513482c1d030120600340e0740a0000400d80703902c0d84020a402a80301c045d005d901d240c90404026540050000c0300da8a001c2c1100c80820708608200210360240340941800581661506542100d200811404000341030221100c1410300d072580201e071304c401d8150945d00104500d02c5441e9500b071041c0c012038000c00e140c465529007990841d201140d400d03000601800600c4410300040400c607503410302132184840b8040c40c0c0c81e96852007030844203000c240c16584031601481071080c0019070a00708280d64a000c91 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 993815035 1250 993813785 993813787
    0x100302031e011206180c08012913020c1204030c06030506040e0c011b02030106090501090612050a060507050c0a110f06041415070b07020105010915151107090e1506011403040305 78
    0x543d1174141104031800e100078024100100c0c0090160f0064000b80703038280105030f0310550201542c0880e440d8482803510190b00140c50700041038805032560180c82c00d55041e90807548580b1480080303c03a02d50294109a406d8010400e0420009905004041d03226000382c03804d0003c046038050240d550b00d19442c4003030610240c0e003102c201485a4528800c0590f40040c020b010031503585880c40000d09003030281070203640c10028080380418004548000d819030100052403095843c4d180c08004041c058100c0301008020030401d408078a003000b1219249001e41c05440b4490b41031020004c0141c2e84c0d9031000d004001c203120030001da001044e0070300180c4c40151100012003614002c104030310b01c50482c1c024405480c05042c403120a0f41584014107807544000300304006815044200360b0020148a00800303041c40b168402440d178803d4071141c1c018900c00040390345683d203500106007030381c3c0030300d0f81407120340d000c0e015200160040d80e0400d90012000e00b031403c080003070980c040e0b080b0b2100400c003600713202c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 993816285 1250 993815035 993815051
    0x901021b100510061d1f0503090c0312030417041208090f040b0a17030903030310060905031f0c0c0606090b010801090506090c0a020c19091a0a15030605100302031e011206 75
    0x40750950601d00246c0a16004090740c40081c01400e00d8000342c403501090f05c01d442c540320b0389080c000761100e001e9041410944c00e590300d660300c000d44080b0700c65000410001c117010000c0d1307001a260346200030502c81e1400d2070320382c0c00c0385003405603036031800086d54415030030500340e1260b0361a6600c4400a0fa03901c01c407504908406090640d1451159244042d010703c000400c118080c002207100100b910915035880b400f040d5140200350351421403106006a8400580401050041c1c0d0790280354103d83e6070030500108141c1d0b4070f61200b15402c2c1c0d440100c0007601c8211440b020f60303003d84110301401540b081005182440d402280304940e00030040b003020000061001001c50080016002c8090002e0181d80b0081100f46000c15040030791240e00412803c01010031503088040d928040812800303820488030034903021280c1190070200f81040c0031325584020115580d11560003075400d0308026100036a40741014203580140d074010100b50400180840014400c0540c090b614506c01608640c0c0410341c05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 993817535 1250 993816285 993816289
    0x1109040b030c1f1205160305070e120102030a0b0607110108130c090b0f040e06040201080a1d03031510020307030804140604050a020307060f0c0b0901021b100510061d 73
    0x100510181d9802021248281070200e0311000f41010f00b6040e54498684c9410400000b040d954103844007209074038005140c9415a210b58060b50340194245410303118028041c0c0400d107880601000d501c120f03500001003002c44034060044000184080e2000752410b60b141d1158003140401044036070402c5000004607054030881c7c03241c018041d030003e0242c008256112090360043c0340701407845000300784400401c0300924182c8204158100c0440180040c5c0d5a280c0c011038044000400101c1416a2200c00c80ca030300c0f508a0000d24010841030003141c1d282040d0280880c602e03144410380b80301d01d42100811801036404400d440e00030707038181030010b806d481c5da186c0024032024020400d04540f1941b800c100c113016000400950850081d03043d15012030700d508080f03c940030988a5400410360700c0c060385001600c070880ca96805403880c0001400c20002100e0440050f507041d910100542c045900380c8007644e118401c1070b03004604c105007070744807034540b01026001103401071856050f01409000c00c4095 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 993818785 1250 993817535 993817543
    0x70201050d0518250905060d0605060303160507030c0801020c0d05030703020405060c2a0f09090f240a180303020c1203130b010b03090619111b01050a1109040b03 71
    0x608102040c2d40d606102900880003400c04400400181544c0c2c54000400c1e940c2481210700803100a03015440001203611110081c0101400c41c541520003081103c40140e0b0a4044043c1c60380316402802d00e00b80307142884080c0a01135001011542d02c108185942044002032000d9400f449040198503a95041000c0e4001d0060b60701c030f80e420800c00521040c60080100b10342100c00c9141842c580501c408032600c01c03400c3d0031b205c211343e041084400c5249051800c96002c0b039000020307104841504130b10316a03a07070911200d03140401c03c00d002d1002c4651001c0d03c00c84401d1703000c00c800f4003c00000c0e400111303a81e103105451001405040e8001a04030b000c0380180134640d840c0d952286c034a640d0b4206044000d040519118098450b400160000300b6031060316022640601d4080001308025280c50a04a5400304c0300040345180036951000f0205961005000e881181c220500a1059a08071020079086d00c4c0c0080c14140c0b02860085440b0304241441c0503134900391400c0c0d800040c88050440442d01d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 993820035 1250 993818785 993818821
    0xf0c110402030a06180b1e040b030703061d0303040309180e0f0607030c02060c030a110d1103060f1210020d0204050a0b070c0b030f0a02070f0218040b010506070201050d05 75
    0x8280008100010103800781c104d0411a5841c2d4001e94005403001c4d040d8045030000000315a001101ca25035910340382c6601451000c1142c0104005071501581c00040d20303201c2154001c07945981c46580101c961342040c4d801000f08030040010b50f146140a0b64001d105030322074040d100d03a04c1e958103811040025143c1c8501c0c4490b4120003203417540740031450041e0741c440d0f0032201000000e0034090795a80d0b8a1000c1181c038001c070048181c039421500c40900e044054640c0324903402d03070741c0c2d02404170810f008000e004500703c1c03410660302c06950b810b1540600c080d000f200c40c981390050b058400c8a0300001c000107a0351252030800600140c94402641342c68000c1d214070f03400140e20071030b02c5a0115082180e0340043c044544580341074010300e035441065208a000c01c0324801511072620001840c05840d9070001c20046101d041540406c0c06030f940042c0d5020301c407122000000012404110402148480003170240900301c4065040140c903600003001481201417525665455001107850b91100c0c1122181c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 993821285 1250 993820035 993820039
    0x103051519020a091e0f0513020c030f360d140f100516020303070e030a0803040b10060329030a0512030f010f14010c0327140405070f0c11 61
    0x50b0340c03414500e000b4884c14241c06071481c1a0740414031440328030b241c00031110444241c8488101400e2601c2c08004404408840c03124030250204099105580309000808070301c040e03031083da51126a650381c0c0e181c0f50300603046100021900707003894400c0142c40d9590408203030400c40d041c140c507981c0f901d803d0306a83c4940003119040d1044640030390b40044041940d0002c0140000c0030082076455041812000041d206205d002d60010804240558410314414a000701b0190807509003070650344d9940c05980c000c50341a540c01c11001c09008100310242c1c1c200004100c185001d201d0800c0c0ca01d45c84c040501c040160120241c0c035010a40c425840610071510116004001d0301d030700d0128078825011950080782c0c10308004103400004229115417a10380c4050f1110350b00070201e40d0303800c07100542f014241d2301c0c03042e01407102d000300040c05550360b002118035202d40100d115400c64940303e0103410040c00014039500c100e05000820a06527400004600868001c1c070780001d4254041c02c00079500a2641542c039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 993822535 1250 993821285 993821287
    0xf03062205130308090a0f0b0c1e04090b0306060a060c020d0204020307031506020d020a1401021207181d0f070c0f06060e15012316050a031403010305151902 69
    0x300000c110301e030701c14580038002d41300c6514a6a9503900b80382c0f40d41110200820340e415000400b00400c01e10fa01b21a80f0540c040c0185251006048055881580042c458982c4180010701800a10502e0040300800e140c160700130012801e1580008003110014003614042101d00c0b030402055545000d480d200700758015000f10341c2d80c1800d5600074040c2c82d08240401c6081d0410100281580c800034440643d08031980c042c1400c881540c1e100d070100d03001398010000d20742d000c4c40603038626102d05944074042d030f1241e02d800900c245140c0c900b204e40d07482980045c150f00740e0f0b041c3d007009060000d81c009a011440f09414900c5030341d800400d03250b004002c200600081c03054203050080145030f6200e101600d160303046022030740d980d00b890801c0c0c140e0b500e8a860700051201c0c8804803c00450544642c03603140d502512800c002c00e00324450700d59622480144e4090b0300007401c00f4141508810b01e40710440400122a14560464850325138406040a1440c4405a402d0001d45460009034040a1040f42c141c015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 993823785 1250 993822535 993822541
    0xf0e1b0d02090a290f030402010c141e010507090501020601151106010b07051902010e0d060b030f03130909081204030210050c120901022118072403020f03062205 71
    0xc1c04026400c0d0400b058184d003280e00d12040511200259246180e100420381d00d9a684c6a0044810b91501c1c20200d031070074144c5051000c5a54107000454010400081c000802c002e030300780c11425141e000d03046134203004c507483c3e05221b0b699011907814192001c80c440290101c621031000c480902482c4820130751030240c074001041d80841500213000082c02881165083c960501c4000c202c6892082c0017400b180345020b45074110304107014140c01d45801080c000035022441b80109040100901035503006d90400aa400300402c0c0d58070401000d0205c1090400c080000d07a52030001c54402c02c010405200320b485e0002d8201482004a00e481414001007030156041c903840407445074102ea20b4a64001d0800000a00c019405209444064141c0144460190201209504803940c0a000c800032072000d10040305d44403004202c80e0000b070644103528003842016980b082d007204901913000302018010400c1542411440b010b40e50400011940440103490391100b082d0500902c0640c412000d00b40810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 993825035 1250 993823785 993823799
    0x40b0a05030106090e06011b050f0d020d031b0804022b0f0b06040c0e041a0d05070e0f01060804061e24140a0b1b0105040506010f0e1b0d02090a 63
    0x1942c101c8400340c4458001c941c484801d01e5a204044078010700040c40d107800465681602c410180703100b8000e6003aa4002204030760441d0411201d40e0106000d40d000310b030b40c0d40c030069040c4105501444000c4104150980410008088800c050806031088400ca4031b00180c0c444440b401c260064210100f0101c410000c0c58010311040ca5010260b4188081100061990a00d406000c17001102c070782c4c92525000d80c0600300f20080c95581d8200040004440300200c0c01d46131103001c0d8540c18060401020400d140604e0f01100c114011300b4603080461003401000700d1740d004140990065407041c030203c3d4821042e88500c15507a28036071404402c40c245074510414071a0542010700b1480b07005202c045c0107444164004021001a000c1500294416403c00801280b080586120b2411015080035611a0341c0c94a003035582c1564141d905400ca00010000c1403903c8501e18000c08201100c8035140c1b40044000300d003102a02040c185103140000d600846030302c1c96040f40c0344041e00038412074009443d080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 993826285 1250 993825035 993825037
    0x5030709080712021e0d0201050c01090506190b030f030706180f1a072f0106030c091506082e05030304060908190803071805060f0307020618070e04020303040b0a05 72
    0x1d0280c5c0901891500c800782a0440e40b58201641d8000c2c0c420740088050398011186907000c91b80c0d4081d00d568540c48140080c0c014170001707019528034a8250480080c0325210000c486414105178424ad01440445005240200590720320540103030303000611800d0001555040c6241c001d0040000280003055003c000381d1204010a004d01c442040c0740540c0c520740c0640c2c540d5818044c0d90414094641c1c00ca4558044401001c0c1c0c0c01d14490011540342c5e900d0b901c00c041070780540c10920800e0b4454501700840c07481c0f045881d00420940c07070581e02c0760504881e140034141c0101c0c80c5040440c440245600f955402003500001014083d080700d9440d42c3e40c0c900202050381d00d00034800c460040c0512805400e01c1800d01d0000150050001c40c6107484020054982802c0401400c02000108000058955414025020102c20a80e4559891501600007403e04000403c20b1484403083d45d8481c400000004211064540e5403a46540b0742d11a13000081c60f40c025a88080e0b50300400244007284113034050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 993827535 1250 993826285 993826319
    0x4030b090115093b07180c030902090c0a0e091609120b2403010f0b10090803091e0306041b0602010c120507031803020d1403090d050307090807 63
    0x500841043d03110000882a1401603200360381803240549543c02e401c20051581c003001803000c903000715200101d542e40b814003105d0b42c0000d003010845141070304003800a0081c001440c42500c0c00300211941313503000820200f00a40900528040421007020036400707000c100c400303603200808003903031440d1007140b00d000c4502ea44c400000184081c0c200141c549400248441d42a5100c1082602503480345050b0310040302e9080812170042d00468200d0041c1c60a10072450600141907000c100342c0070040c180503142c2a0b00c0200400c025212201300969140401941d8603180101ca075240350f800301d8020240726054250340158540100d0781400200702010f444480351100c401a001c0c5040e81d00c2e8816401c9031000741300300380400c100407201d030701c051000d03400707590311098904000403c0409c00400c8190144000812800b41e0b1049543d840600d4120941e2104c2a2100c0541c5145160504010340c036503188008000c140030000c001b2400044c00740c4140809843c400303044440055507449014040c0e040c0e2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 993828785 1250 993827535 993827561
    0x51c0914100605031009120e031c020312011211040f0207021f090b030403090e040c180c230d02030601110a0b150a080d0e031c02010504050c01020c0a1a04030b0901 72
    0x3c45d000c200005294004c210340c10b40c0000ca40c1e280c48550b000141c85600801c442940c0c54000e1068880001d0014081b038580b0444560046880f800200c4580050000603048045200c142c1502c1c0c0d000190114980082c240701510080344500080700800301a0040c4103001398040080030a4080380a0300043c0b40000c20226130790105c00d19a2000501480e00c001da0b0043c00060480c001480404104011513800030720501c66088140d03074541d10445900380403080365020320344444003081002e40c005a0a410b6950b941c8001911100b40c00030340c3c0142c42524070880e400d540100025101da070140182000b800d4a42003990b460040ca880c01c0b056124086904102030301c0d01d04410b4895052022211003a0390040c0010103111040d61001e5915102090ba810f038188241c400080040460700850440d40f002030b00081642d0070540b40c442c1c2481380d40ea0b03800e8119400050b440c0e1603170747c0d4082c3d10700c122000b512481d000d2640358010401140700f01d0700090400b03121a402d0010501c3d05522030081d46142e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 993830035 1250 993828785 993828793
    0x4080a11120f13090501050d0b100902031f15050403030e0d06150f090515011d040c0306060818061303050d0203070c060e0f1c050403020a0e0601020d051c091410060503 74
    0x244c01220007154030a015058208106024140c005900c1542041d04410b03600171002081f5510071104050b030340201c94019190000c11640341d135800105903954003030905403045004c03003503081000401c83d001d5480081c01300b20204000398915100d040d00399a40d0b035003000051054500e0314010131a400300300e2059002e88c0528120000d2107034600c0c414140a060001424a0001910001103c0c9000d520818032a0303000700c100d40100c1503036640305089a000c09500d011840c0e5203064405440e200c402044207440741b45040c1c0b1030751503501c0440d816030b100c1d01c0802206103e00840c20120350030700492400c400160b1001080c041040d0300310340b9681c500d5104501c240716108403e4074198a5408402034509103600422010344001601150800c1010a40c0390442c2003c1c3d817500041c21880c425440440c403254020284545564140714200c00c042c1c903401d2240c50013944540c80120303d980f49918144083e540c00300c03d82000762002d12000a0450f010488000b04481d001207401032040e40b18480c40703841 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 993831285 1250 993830035 993830039
    0xd09080102040602071a12150a0e150d0f060c02060121030c0602030a150b122202010c06140a1d0a05030405090a140405010902031504080a11120f13 65
    0x8014000c40d01a1810fa60161000d00c2c91300000c25890484004c00400c1040203204942c1004440c0c01c00500c501c6564002900f2000a00288a1800125003241104152070400c101b440c41c00102840b50844041c1c3d1100c040c001d40b0300b0011107082c07502c03500034441820010041c0b04240e0000c1c099058640c0707104802c50382054014100c40c13240001c040140030503a40410300000c22002d40c06582e2140d20058081440c500700e1110480f41c01c4107070491726419a001c03030050410000501095401100c05440303040a034141c205054080116481c001d04000401c03c0d0030b403c024103074201680e03d402c006402c07030030745c2096004100030b009003003156500c0107101c02d900c40781c5140005036060850340060107545460304040602c15007080090180c40e2283d00e5036007460f032272a902c035042440b03a0b00407000001e60054510415040c90819900030301881c08220074040402e480804076420701c070290821214010650591500340a140740d0751000d036402c0810501086800c2d03400821440d140d440030503552030303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 993832535 1250 993831285 993831299
    0x50c01050a020604120e0310050a050a020c150408091c05062a03090c03030c0615061207032f070b1e060d1a0a0617010e061909080c0d09 60
    0x3001d4105680010307400a00410085041040c9290003580640b511449400f02e034004203107007032010714506003083ea07540c04000c01388043d4807401c0e8201a00400035480c0102130307403d45541e0121054505a00420348000c42d042000c24812604070304c0001c0d12002469982502007189901901000c2d00c02e030083c1000110076040003080e00242c4218141000300d85a0040840e003580d80009280c041c440c0300304406825076680401c058078005074850014207007884c144090352109a4922040c0340150414000d490710030030b60380c00345680600c003803070000b42d02d031444801d50000380c0c044502d489441e0f907403410010302c0b4040c000060404601401c8814040d40303c0120000703016140701c050500c00c00c62400880c0080c03500314821440c250041161000841c01c10b100810348030026a05022900c1d950441008006040305815201010303450081040154520b061074440300018140081c0010005070300900c0d090643c484180711780c200c0e00680e121626032051540d40d050004035840483c1c01410700047c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 993833785 1250 993832535 993832537
    0x16020d080c0316091e33050322050c100e0307060f090f3b071101020418090c271d0d03091106040e010b0c0316050a050c0105 55
    0x258a01c0c0d070a45103982e59071603038900020041202c00040180d006800103d00c281d010707100202811a8044041d800c1c034142c0d162003a04800410b524038100000d800500315402003101054a20150900541e642c1d101c07407403c0e0001d410b4501e04400d1002922802080c881c0000c0e801d0039a090980b00a1240d241103181902e100310240c07000d42c0e05030b100100034004240302d10021011210182007480019480341005011081c4035002084c000c1c001007201a20b481624038410440ba012040142e840440090786207000c85005090f042400b03050202c0c0f40c0c01180941c1114020400d46510100c0e90b00f984c444400034201c884002e0b15601c0b0142c80101d122440310001c0100411160240085a6601417240000d0070003d01c050b10106804200b40440610034414a00a07400c0c0790f400140b003410300e1501810810050700c10500902c1c00388424880a1540b00c90b05040d1100b884e0280e4403881021261441c6110700350700402055841c90715142007200c00912002c500d44a03206540c0d60030008001181e42e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 993835035 1250 993833785 993833791
    0xd0b061b0f060a020f041a13120213060305060f060a08010903020a2618040b0d0510110307050a050c01060b0a080f13110108100510051305030105010b0915040e16020d08 74
    0x18468100010018029541100c030403d00b00881f1050600b02990f98254802c9801d50140401c0c2c0442c0705100210701c0e04a000401d0f808461004000c480c0c190b0321819540d0000038004064000700e100802c08642c0c03202e4001c001005100e009000d070058500d0000d4a64010b4070003218420102400a0b0b4203007610581d01e070f1800400311505040c09102c0d40c845802004000140d81c101c0d43c2e420880c0d10a0329540c042048a901441c02002040d030420800c0c0100c03071665031108000345044c028000405e80c4402101c00c40401c0e86002d40e21041d13058005801070489501c03001556000080b4150841c1d000701402c0c0c820021103154044c0c030354643c030303e02002c2e5468250081c07160074600040c0c1105c0d0b014031011a040070b0a5141d2514490b1039001182c0c0e100e80c004100c0c070114030b0100d0400c11180b01546944080c000c01e800034495549414100050303401080d002a1243c80030031004000b215180041e100180781001c500105400c100c041c040c20b000d007154101005004107210000a00e0066880d140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 993836285 1250 993835035 993835057
    0xf20040e2a10080c130f03020102060a0905120a140a110f0604030507060e16090515030c03070b03220312180b0a0b01030b13020c0105010512030d0b061b0f060a02 71
    0x40940d8151400c490021000b44a081020020f104880e05c0300c0858190070080e0510124010001c0d00f140006890031400500c00030166080070b9a100000341c0c00318100c01140c1d4250310860320b032001810196a907c0c0c0b011510580c81da404140c6204040e440107003001c030032140c0020760b904540d025821503180d40c0122000b038045076041040c1000203850794031204d414101401075411006191a10390700c03000282d40880c40d400d480d6420300c05400200080b004841c1021401000c1c55038a100100341c540c1c040d840792a0150001000140f071040c0410009007252181240e908100ca5aa00d07000d0710041c0c8292820180710b140031080150f13107020070706416a03540c01440d14201c2d5550445501e0140c214100d40178109074450301c1d0100b440d125003c980c14440121100961540c01000c509400c43d40168400b03441a000600d03485100600802110150183c500e400710303101003a800072400b14031401c52405400c02c408801c00a03a50742c085008001500084150361158413a0b40e0250103078025900e0544c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 993837535 1250 993836285 993836299
    0x1806120d0504051905130b1e130f091205040905070512060d0305040504020d0603060e0102040e0403030e0c1f020c0a06020316020a0b0c0303010e0a05040f20040e2a 72
    0x200c240d01d441c20b03007451140c20955002e03903029110004101301b284204a00d9130541e0b1100804c11052515904c1002d0340300301070a5205001c541c5e07100044403e500d84403040e8000b81d0704c0e5001041c200c800e4119101d403a8101100c4610030000d09002030607076006100340d810b518501000b24060501c10000c88120310800a162006601e03080d0400c40094240501141849000c100004480c3c0742c60018080c4030343e1800340090850f2960070a1415103440803a0321a040e4070400080c00540e0960f0421604181c040c034002402c0d0f191110b0651820aa560a042d44544103010071490003060542c0905642e003c3d5082e1070401c65001d040c405681128001c400258005014041407891183d12040d007690000307001b440600d40d07070203035003d182d4000ca40c6001541c00000051200d100075680d0180c02c824900310401c154a071a880c0c100e0500c2c0c0e001001004c0041d0000c81100d020707280d8402402e1940e00070000c04c03110301030031406035031801801c400700c203001c10200141841c00c0801d00c8490191201505038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 993838785 1250 993837535 993837539
    0x102031b1303060609060617070c0b0a20220501050901141e0a020d020613082b0222050d032106030302150a051506181806120d0504 58
    0x803408035081819500401404050000046002e40c042c3c00018208803500040c0383d0300300503000306000d108124298541031400e007400a40c540c085405058260094500060303902c501074010081e00112200c40140482a90b80e00c1c0e0010782e04c03004022002c0c085601003124150641080001c121520131b0300e000c40c0003440034542c99401745000400d20a1500c0d90146440c141c1148991240c05814613680d500001207040c1003101d8040050103812060b50001348054a421894140501c4e00c2000080c40d524001c610000744400c9400b180903017840b500a21181218a001c007240203400c0102041d0000e14142c402e1b0700414950f4440da420b0b224007034100581e01105071010348021410b840d0b90351544e0220450b40901c11664400c00002c3c51103a070141105c0310510b04501004480901a031003011f01c1d14051004503480501c0c1580d0410f41521820780340c80300e10202c14080c0041a8020350003500d6044024000e160541d09280300b10400c40b402c40c41c0c0384d040811940c0c0c4000181088010030740400003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 993840035 1250 993838785 993838831
    0xc0827032a0303220503060c0f0f070c0b120406060909050c190803130f0e06181b040308030a181a09030d1b11011b0c080d0908120702010203 62
    0x1641070010000d02140d00e0b2070303020b140100c0c6140146103501d10b0b04080803802d016502e010711220380c000d110820b2242c1003241e1040b131801d241c4540040380e0006440001c0000800503450b803050000c054101d0070640f10400e2241c404803110b0111022903101e441c0c2580403a0b00003207072092040d03c40d000402000c031100a40284500f188906000044681d5030203000200c01100704028040b45035604140440c080c03410381c1c1188410441c1d0041590070140004101ca0307501e68032160a480c0001c0200340219440b405890004021352490710a00004c0c002404001d001240000b94084d00c2ca840040128130800401600d0411640b14001c0544500001a401454200010b0368000d46c0d401c2c140e33460031400e440c40c4001c070b814581881c2c004003400701030003100341d400c0410001940f017244000c0c80074094002c8404084000030102070103201806100320180028001610b07904018218200318030340d210304005240d5001038604c503943c01c40307040010309800e20600a0b80e0040040c414242c11075824815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 993841285 1250 993840035 993840103
    0x11010e031e03041106160b07020601120f032f12120f0a0e1c1b05060a020f04080703050c1e09010b0a110709060602070b040810050402010c082703 64
    0x2005441c8407003030344c801804c680e4405000380301040101c603404840d40070b580740210929600500c0c400075508101d00411144a00c12846444181e0184940c40002d60300d2805589002c10401e007651034240107003001d41d030340010109100300e8a440da0116180303072418006400c1203100b41c4008903041d2a004020804080300e044402e0f400840c0c900b00421030450f545401840c06000020781c4d40c1000c00e0b416a480d0f002d40141c0e800d003120860f0031001d428440c45840b4140d0303c40e030142041c15210303400155240324004110550703016140c0da006545a06550381021a0341e02a40c201c91407040407003014858904901842444100c031000d00100c040b0782c64107117003100039007040e40d44000f0b104500c3c00c4000450700c14804035001e030032a0701d00020300908103e4000d2401c441a0406407564000b040300703005e4080e000070948509031085801107440e40e51440101c1d0750300d9814800504c902804910200c00024100324101e81642030140402c5a05040040580d0707131042600460000011003000d062004540c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 993842535 1250 993841285 993841291
    0x10e1204060f210207021201090f0803070c0c091b020615010302070c0e10030506060102010b03030912071214060a230711030c0109060b0a0303170702071511010e031e03 74
    0x104283d400207002059440460409501e403881d1198005616411490440b414000c0c10b0003000c020801d400007503681d080c0c1d0b10f0344d400018082a03004400929428440c40070030b80c200d60700100f002e00144d9544c521201030842d0344950341041c00c402115914143c40012440c1c407440f40840100280154140150f0095102c0c3c00165507841440c10041449803809200034000d60410f48a80c0b800361039410302d203091143c0074281038116410500d01e030007255400820b5408114040f902c00055480404003503188c03001035404070000401450440007403115155031151080150390684001c0e689101140c021118090500c5a4042424080c021a081c1240c8029800449400c0c10024400b20445007491034020114100c1c0c0c4e40c0d1070341e103403900f00711190150844490064034a00241030440d600030301a00d44a240c1003810a01010000d58424403c0010708001e2040000e003448450b00c011000b002c45a04401c140c0700d540c24003020444000001007112400c3c44881c00701c0c96501c40e04d06601c0c0b007a501c09 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 993843785 1250 993842535 993842537
    0x10b0616050c1203090901091109130f1805060c1e0c01060503031801230a1116120b0f0709060f14160b010f062001020c01110a02010e1204060f 63
    0x702c1500d80e00c0b900c490854181d124108001941c50700304003803c0201410058100e408014108222070240b220400140c54907003c0807200d041c118100681c0e00d10040005020199001d8200004d20198000e2414a1400d540c05003040da201a0f4071504015aa40300d100da00600c0032000d420b0a1580658403409400d403445200004250a0382d108006491758002032215100c0921500e0081065070301f21003034140107c100b043c1003200408a440e507109600803255030310148208103001c030540e40424009d082c0c1c0b20000c04d070781d4036030652107895103d64604120b10807501c0c041c001d4041940c01111100310f620804c030903a02c1c82c00e4582016011142c210008440105021052002c07900010400d4080d16407a60001c4440688440302d003001c007100c0300103a0048194510050081c044980d20500c404a2082c034160500da50240d40c803d050300901c00e050b941360f104e502e031076006940203903450001c00c1741c01c0d050390007030110600b103090a41e05c139441030b003074070717103e65803c000800009000f030260008103101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 993845035 1250 993843785 993843793
    0x9030307050702121203071812080c0a08180f12101e020415030b060703020c100c0f0c150f021e0f1b01030f090b180313080a05060108010b061605 64
    0x504244945407030710345e160100c00170b8408010007162581c408500d20611140d10b8410480529041070824000200321011780a00000650f5401102c2c003046030a40d641c2c1c0c040c2c419584d48106240781c010172202c03160440d100e140f40d4408050b0700d241911690300300c4c40c40310011f08110030414418200070000c0603845071001c600a030f180010703c0d0940c409071004001000340c42c0400018504018200d4080c10140c500c240c00c2802a10046580000c000c04100c1040d500b40d80080c000000039900303001c0080c8024100624800843c1c00c101040861008580d0303580d84c0009405d034408801d440070700244024800581c00151200c5d05138010042d007108100711a0103580c0e80101107190a82800d0350f842c2c00009003050f0082c00f520b0765078588110780b10306520280c10840c943d1a99502a00c100c0081c00c01c1107100f0029080c4601c1207014401c64880070907414069480c3e95441c3d11980c9c40e240d00243c241ca030750041d40d000061040c0e042c0030f100b40d840d07401440d0500e0100c05070846445403421100039142445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 993846285 1250 993845035 993845059
    0x705040614011209050c100306140306041203050a020702040e0a12031107030c02060706050103030908060f041e150f1e1104030308070207090c08160905060a110a05031b120309030307050702 83
    0x6840c10700211501c800d42e40270030b174141006100b11003a082e507103459009074800001c202c08240000d00b0b2059110043c5400b080b540c4458401078003901400e04044d601a00d04080d005031031100103007001c00e162282840701002002c144013601118202c11071600c3c0440c0400c404e80000744241c410450180c4001c21160420602e0788960741119401d800480218070050014004400104009a032101c0300124070021807415a43d4019028205c100c0c404071a00442034650400c4001c0040010024180c002003101610001c5010b0203803400084402c0079512005d0241d50049041c000c3c5544201011a15468103280d41d40880c0c4d842c0f4001c1c41c2c2411805521804a0704000c0750140300840e501035551000c8505041d41c501101e1041d2240340b1003840f0300140100310381c0d00c0d16425241010540d051018105840900082c00d0016041c4020402d000004141c20b0401461f000d4000c403401110498100176001c481d40d81c0180b105807652104d5510a10008101502c81c500801a051001d828540e50785 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 993847535 1250 993846285 993846289
    0x3260f07030c140f120a091401111203071d060901051b0619050901021603050328050717070203090607022d011101061d0a0e0604050705040614011209050c 68
    0xa010ba005222981c0004104c1e51952104002d000000c4a12080c505c0c6815606440034002d035805224006039501021018200c581c090003910034028002d4050300c06106025600c0a11503004660a01c0410360504d0780324002d9589500083c00300351b014061606e09410b040056a41c1e03008064603030703420180c510825907080400d111150081400f948000c6809103281c50950640b107004096002a83c03040c0030106805011038a032000f015090305001740e40752034000e09920010391013020401102d103519480c00c060b4505501041c8913562503542c442da440503402c0e940c009088107452010040e40240120003441c645000108901407000f003151061607120140f80f46419101d080400074082c0c0c24681c6a5956005001d001081e0712032002086090b0a00e100c04920f21851010080303400740d100000354421550f5402940d643c1c1c254421507080d89410f10b44203981304854020103001301d0034140c0014041201515030050010143c5070b000880c446011440c0041181c01d1055030329125400400c1115 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 993848785 1250 993847535 993847553
    0x1909050f0102030103170304240f06061707030501060503180a020d060b09010902030603120f2a0706030507050a031a04020a09090e19020d17040f03260f07030c 70
    0x390888000350320f84d803460070f00001c541d40586400800d02d01c10010480044e01c181c4070803103002d03100580030b0155101d20280b40001c21b0b05600b4001c08a2030507002207440ca41045000b0303510f0018158800e1107940b00701c0200c09580081c440d480102d03a0074408210031058a151580c0106410002c9824010301500040c0705000c09201c180d96451f40c880e82000981000e10059001d028000025851424124007103980e828004840650411005c1b0b103903242030201c40120741c01200180200c0100d074000c048000c21086074040102040d21400400069581c024001c0f1072140603140c492a0811858150640c0174000310004d610800000c1728030002250349a1000d4110001c00d51344001100307041038625011144000c4e14000da9501c05200c0e01c014184c00d1840c0c9084940c192104460300b40140380182c05600c0010200702c003e1004500406d180f04082141c43c2128020080403160b0070149404440107072604050880c0c0003010008506100100c030010690107129103040c07110092039481e0a102 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 993850035 1250 993848785 993848803
    0x11120f0d0302030f1602060c0715062c07141605010e0304050a0608040f0212070806041a0f090c0103200313060e16090b0d051605030706090806190905 66
    0x2082e4044188100c0c00c012102c116809040180004c24090038481d021b5a101c07001854a2000d91002031800300304075101d00078a02e0403c11030800c4c442c2d0398842807a10340c10301d00f1001c0f02d0407520302c9041083d80c018881ca080d0303000d80312507142e101d0300400c07410000200303901100e0100707038080700b07010550005803092040341d005031440000f07503480714145400c0008040c00c940c49a0308111102041c000400d80501040d0082c99048608143c2280a094503505019503a403241c21203014403c01c1000388401580300030822070801d402c641613643e03549000d0720602410f9502540560268801c100306c1c0d4000c2c0e10201e81540c1c1c2c1d0300c50444960b030680c0f0300c00c1e031644100ca0302028021903c0c2d1b8102080014005c0000041d100c0c0042c0c04610122002c0d50080308081c85405407454650135104850b4582848006c052a044019921090302010342006d20b20302c01c0c495580640300f501000503415118540c420140e696800280c0b0042e2210100810f40c2d0341c4044000d00000d43d220303080400036500b0080e03c21 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 993851285 1250 993850035 993850037
    0x13020910050a050406060e06090a0f15031407230c0a1110090e2e140306220b06031608160806070c06020a09270605030a11120f0d 57
    0x40386801c14042c45141c01e0140e0009004074103201d801d1010a8103d0211407541106580081d1103010210020310f4503c030075845448000d21100021810303040c0c0a100020005107078074140714241b00180e0342c0c0d802010455110300019511000d02c040d0900c07101141d244c940c9404017050404000c408810306006003108100d400c0811507282c0000d5007040b0042c0c074030074141810400c000781c1c80c003040c25402460013440820711050040fa01e500c1c960b041164150029008107004440d180c40e0541180b0074030b40b40403082d100303228220000d071125a1400c4a03202590021200c030305060503680e140106040c014115036410700540c40c021421880e882c0d07010000344140002002202108401488482c809400800441c0c001208004a076500010b814030320341e6101c4001039a424003283c04039240c40b015000103a040b208190b031144414250b50608103240e00124007088295a10000c260f990b90fa2080c0040080c624001032045070700d4001920940411040e0039240140d01601840341071078040030000c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 993852535 1250 993851285 993851311
    0x1d01030e1c12050f060616120e19032a03020405270c060301030b0403020c09010303020d03060e04020f1014030708041406101a04080f060402031207120305130209 71
    0xe03081c2a8031211045242088072030800981c10b018605000b0860000c146038012400000c204030030a00d11000c0c00c0076560400d0000400e890340344d500600c2c0034440608184201a003202221141802c010100c04403903020b0302403800740080100702d00d40c81d00b0001c41c06101840e40700d000009a280d5015440c81440e002c0c125130480d90881c94040104181002600c520b40c0c01b001c260b0340103488030401c81e030542e600100b001c1a9980e0b9803904070b20300290303007070015005403141000100301a000603183c155040985c030180038460b11007080c003d51586c1242d010307500001402003c80c80b820101c03d04691104030b40340201c11000e980301d0390503495009880c2c00002582150402c02441910807001000072141030207044542003d40780c84000070014020480550700d000781410105c0402011600208156800d803181d001b210246a900c42e441124141c1c041c2c02500745421401c20001c01300c40341254807608140c0c072100031200c110000c05c0e00504507600384a005841d0400360f0f640b0b44c0300901c90144106a8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 993853785 1250 993852535 993852583
    0xa0308030601170903040612020d0e0601150f02071802130e010504050c03040b0a05180f0304090c111504081216030c050901090302091506030c04090b0d031d01030e 72
    0x10180c960101c00500300183d450103000207824003100b110200c504a282c0155230b9060f06040200070301c030f0b1004411119140811004d0a500085041c504030b640f46100780c080209080000d8038503ca404140500503000200701b40414840804a80501d40b10384134010308181110400044100c2c20b0b42028049105101c01017010786030038055644d00c41190981f083c11800c0c00d90702c40008980251401000036104c00000c1e00415010608240b42c0a100b01100e07200102c0a9403191a41c2c070601440b10301c01e041425220030540105420070101e0303000401040c01401903c244010118081d104444548080040a0980c140481e0040c0030b0302401411111a00e04014060f084036540c04100d01032000500c80b050441e0b030000c4013102243d4050f02c45203502c0d80c540050010055400c2c40580d1b00c4071010081c030541074100300140041d01c040e11800c100c108002c104024640e801020300800080d15406041b4101803003100c1903901c034030706040c0130802560401503a820b0105026101c042180480700c9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 993855035 1250 993853785 993853787
    0x30c01200118060c020304060c061d060a020703090806040f0212030903030d020c0607022b031404080a0807020a080706020a030b0a091b0306050d11030f1006050a06030507200a020a0308030601 84
    0x10710080c0d03d00d0741c0006c40c40c3c0b034a481c9001d40b0f824410080946803603030b24074610b12038092004940312040d03200b4041d60094509449036030000d4210500603000524050b130046090070f00000c2d4030303000f541c201c100800c070141c540d82006281c00d000c0010308a240401c1c44200b50f2a101000504501201d01001507250a51100803c0c41d202c0001c1003841154030181c148101c1805c8010740340c00801600040300705100d0512010380181c001d00c545403010550320020801409010300c06041c8592480d5142e44464841e014103e9641071902c2d400f4142640412071000091803e500408898072203040205100582500065140000307030300c211941925865410308080c050f6911040d030300401e08003080901d0a1030045980c04a2844d4010f000085460f4444060341c1d08100c8540007696420490780c6014138894240054615449000c2c0034149400c0082507046c024002c56228000c103a0380c5042d5402c00c25209000c064180004810500030b40b1507c80141e240d0900580c003a50040c1c04c0e80380c0d01e04200380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 993856285 1250 993855035 993855041
    0x6070203072411030a0906050c160b09190303080f04021804030809060a02070804121a0a1514010806010e1c0b1b041a0702040204180515030309030c0120011806 70
    0xd0043c08136001001414242604450154203540b010700e407441e10b440e00c10705050300d041148143e03c0d504040d403440001c0c48a0031072000300140311050320030f418480f0704002d00c40114a203502004010850520010301d01d400d4000a1551081c0001d003010b000003c1c55034170701c0d00c10a0a407810740000b10030304200106028200451038201007519000c503d880c0c0e0b90340302c001850181c0d016070381a084810310b800f010b000e07000b950b000d10054040d6140c446804c01e20350b00001081c040b0100e140c025402e450004204040c05503034510b22a060719101c0c00d96480400450303450b0138020a495114103c10040c003003400800b1280008a441500030611604000440120342209409100d40b0820308003c140664042c2000c1101080f0841c40003c0d150003540c40090064001c0360465428a002025010a200c000f500183c1c09000c10b8003040c0c1c180c0541c8424151680b00b1540f4580d051342c00440546195481181541e9107056031902514691155104181c2514413014070b2400000c02600220f0910440344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 993857535 1250 993856285 993856307
    0xb0304051e0c0d0201050c10050112030e090c04030f02030f101406060403051f0915051509160509150a02010b1009350d050d1d0a02060702030724 64
    0x4001010301c0d00110000a00f20000c00100a0401c8004152082c6190041050060380d01c81c07450180419a101c821004004225001c01d600103060500b1a299a040c00d5078100d00500340c6a80c110705e030a085885e090280001d030841280c2501c05c0360890701d9119000d00c0000c001181c0c194010070b01e0810603a50758440b40c07000d03003107910806c010001040050b00008640580d90642240514484040e6050100512143c11302030000c1d0098903159a03580c2130340d0b210341d100364600e0320040072138030b20314051201050088904031040c20f6203413041101180a5400b908a000c0001c080150b40c152142d0000c100b0b8000c510890050303074648000b412146003003142400c0050551030a012541d02e8509950952014016a105034680190340d100852042d040e0050002c10100201d074071904030040014620b42c0016180f2001e90b2600100f100c42c40c43c07040442c11030811050041035100800c1d000c016040d4492881281d241c03040b1400051014041950310181e024034620783d4a21114054000d081d13071542c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 993858785 1250 993857535 993857593
    0x12010606081f05090a05041e051c03020a020a02040e120d0f060503300702060c06010f0512061609030b0c07030305060103180b0408040b0f09100306060c0f020a0b030405 74
    0x1a07005114580741d030050290b009140035000300f0140c47d2401c1a4140400e40302e01621003060503400d4005004001803403001055500c0901d21900f54003000c104c04901400c00c8000050301302a5190015203000e40000140801c55801c1c1d402107107401c601d50140c0d074400b50b201d0641c20f44507c41000e140c2d0b0203108071401420b041d405001084000d000c850001c038031242140c4a15040c0040410300740d04078200fa038040644c00380404e540c035100e100e003141d80c403182403007503100c0d24011a801269a040070318100100364041c00c014002a1113038100b40d0803403012a0131520801096040000101c0c00c0f40c0355160007000c5400c03404d40d5a00090400034162039000b40f160b0b0605041c84001e501307030800c0a40f647da0007a04480b000b196902c45141c442028840c43c0c0c07100d50b008101244100c1050300f05802090201011915450001102c02042c0c095030b5003880341c180404c801e6111070011401054503200b01c540700070001d02103140c42d4828210a034000b61801c0c1c59940c403d040740440c029032480e2607a008426 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 993860035 1250 993858785 993858841
    0x1d030d21020a050d02180d0b040203060c09130b0321070507060305100603050712153807030e0d08040612090b2403010903020d09060914040b1201060608 67
    0x2c2200050024030580c00342c1032400d40d000440b0030f140303403600520030b0321204c0041c86c0600c07003030850a00c002c4081041c0d800340d1203405100c0201c0d0b00035910104492212001825444514807038590301001417900000d46034143c001c98a0203110b60752104100c0d9500483c5452281e00d4403414141107180c00d4440e000007050500c2c000901081c20481c0c03600404072129840c01103815980ca9008941000c0005201d01ca058200a00e02c030082e0368140b5518259035020a0f104c07048110f00101070021441c80c400c2c4400e001c2c0007550b0580b588184402041c000b8000e00341103048e50400c401180040e0181c1800386c44c07512004c9028402590b100b840031100001441c001c1c00030441c640c031942c174220000390a62010300340805680e5900124803031000c041240040080003002e0f81400c010b5102c0e5a407105800000d000780c2c802042d1280a4000c65082e1404554095150381812702884000c0000404a0380d03c241070000a034190102405504e024000f5a52404414180840c034400403402500c0001d0b82000d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 993861285 1250 993860035 993860047
    0x141905060703171503030d0e03091f0212070b22080f04060f05270a050607061a100e0f120f0d090b071e1b0803121003030806011d030d2102 61
    0xa40042590031f2840e001c9400a0000c2c4150001441e6200c1c01e0a200c1c0c006802d45034074200800c29a5000780003010f55000e8039400c0061905032116071007008030052440c1c0502002c1000310b0810800d20100d81c1810b108140500420745802941d41c00c602c0003042c511800140a011243d803041c020001c1800501b0321500300301c585480606c1002a540e0301d0303005a11004a55011a81c4095040c401418060000c0b81d40e032455090250151040211503074600340011013102541c14005000810303510390755140c042100c428402c103d84120152030043d07025200c2d80d032401000c60240412480344810382c0040c00d0010100c2c002034450305007988a0b030240380c003d100c45404603007c2240e80081d17070b040c0343c800d0000b0328591400d83c103100c170000c503002d0100340f400c1c001040444000005005039001817609400607590207401d2000c69090740401000501118040b8005501410010058800c0c0246664000000030042480e1031a604000070005802a034130303103001c80b1800c917038498450000c6002e501d400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 993862535 1250 993861285 993861289
    0xa060606090506031501030227040c0509130f1d0f1231081906050a1107020d212105070806190503011401030506101419050607031715 59
    0xc08000c0c100b21000c92080c2402411b13070700c02c0e811190261070018080404401d005081307684100e0301c3e2400c078010b524202c044011b60b170040081d600c08840042c0308038901080445000098440c14008003a4641c440c0c4c0301400c4120511030f00c200b8281040c0c0141041c8000300030440c41c003044020702d10f041c0031080003c4032210b03d401c0241d0305c910844500c000000821124040038411580d40107410502030882102881102c4401000d03249020310414420742c2c42e2000c14408949107184150445a0704004034801402d141045031202801a02501c14401d0100c0368410452044481c0383c000030780110540702064002d4158051012060300c041001e841d02d50006003080da8003170482840745817024602c0080d40002d0040101400d4003500a200c5c501075902c800e20706001c00e0008480501886001030358580041c8030303c508a07170083c40805218040305003170010402d0f00f079104480840741580c011841c0d40b80c440007444c0c030a11a56900901c05c05845458000700d00103005c49107101e05080340b400f019 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 993863785 1250 993862535 993862537
    0xf0b040e0318030f0604060209090c090d11040902130c021204050f06160503120105010f0f08011a1605161d010e150409050705010f0302041a0c1504050a060606090506 73
    0x380e100c1110304502c084140b0300003850101c6942c030030409440350108000030085190003604a10360162100403458550703600c003a04500a444905d908010500c5603c1c021550103400040401800b40002600450303580100740c00540f26500d000d1140d031034440d01140580c3c100444080c41505038074050800b4108800284c800312900c505070320032080803400c2c084000480ca418008a58002c2c202c9569003186042c10a100000344074a80c040b43c1c40b8420045590700540051000d01d6030340d651489503038204164207604400d2080c507062400024480108490800d82c1a55036030341c080d100510415400c188031807140e00d125000340c3c00300c054a2940c001d4503044802c00c00d05407095200c02c203120744e80d00e540c2c005020501401650340705040a2041c0f003841030108105059940070f0ba0780e2103001c038500900303070260300c140e00c507140d000c808111804e549603800201401141c12a00103aa13030804900d09030002c8003205031400da48580250080c0d40070440b0314807070342000f040e19051904180d850040000d4035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 993865035 1250 993863785 993863797
    0x1507020d05180904060e0712050c100f03150506180a09090305030f090102070b0c071b26070503031b0f0703110603042409030219120f0e04020d0f0b040e03 68
    0x43c1d8241001c603041252907003040e000004400c044801165941c00d50089849035131806440750700918010300302c0f60400c41140107442c0d41a8860482000ca0035504800074010300c1c44c41c1d080e0315a1707810080360969412000703140d07401d04071000c03c0c881080c1408002951140d544000d0510b80f50440550000707070881c00756507204000e41e150348102d503a1100741901900c00c0b010700030b000c0d05560302000a0031082802510308640514800c51450203190703170f00c280c101c060780039036a0140e5507180944100001d042081500c0843d1009448500740d032040800d1071604218080d00100602d5401e42e021176004010075401d000f0100300501c911b81c5140c50318076500000c010020f004040c00000038003071200700c42066a400c541451300d80e080301c44540d0b11100422081e8403c03001400350000400c1d58400c51860040c0482d0805180c0041100c02441a106840320304521414051926010012a60b40e8400341019560921000c1440344904a210049485161980d48640c4c1b9008800b05074000020035181 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 993866285 1250 993865035 993865039
    0x10c020d0c031502180a0f120c1d0106020f0a030509090a09020a06111009050303072010201612050c01020d06031a07080a0f06081507020d0518 63
    0x4190310309400c006440300d0254002501c0c0200c844541010074841ea4010028201c04000010820b800e8204000f041c50442c031410800700700b041028406d000c01d2801c070341c1c2407074401c5204100c9195115003124140248489103001004081f00422929406029400e140c0006501070300d907903000307545c000d46039010340240d09024860303d00c0040d01c40041c82e48a00c0055400404500c0115618030008145000c94144c148160050031401140c000241c020320b840035901c00c0180d4115560310307500b00c45465803107050104080304012014003800c0180b001d52101d05c4403d030081000f040c00300a0305a42e01192103045100003003040294804c0c0104a550304407250f11400e1600c502010350710031120740c003a034103540c072165100203440b4520100702d40c801400c5a06c120005240c2118015010058200499164000ca00c5000000e41955130710303442004045200d0000142094580304003526003082d100ba1034651110b52020700070700c15010081034143c04c12a182070f41c035142c5084020213000f40d0302d2038014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 993867535 1250 993866285 993866299
    0x11091b0f03181005070908010c05041401051216030c170a0902031c0c05010b01030c0816020a0f050a03121a040f0603020d1a010b090901060c171c060b0405010c02 71
    0x10b00c07980600c2151860008a80d070441c1e00e0103108102e81002842c0a40310707070000c1502e4150010f00d0800600411100c60714035200c1074100351070000c505e000082c2c0c1a20050400c0010404458690b00c6210200d00420050b500ca0303032440d0040d0009000c488080c0c03000014030007115800343d0000854a40e29a1123582c1da5030200da03071a400e00c0803d00c2c001410f500344000720b591400000046030f0021100d507200380280001c0c000c1c92004801502111151021240000d81c070388001586144284141c6c51005072500c115481203140740c0315180c0b45410f5940880d41500101d02003028075500034401035021000003004c000f280900100c2030000d1109610041c015034603a0503211221050740d000300000c54020700010452030185c03505100b403100368201d04945d9840c1400100e6115070040a076540024041c10400c600d90800200382c4080c0300c0d100088031660f0682040c1c0f460704507940e01410403000d151710741030107115074400002c040d60185c1e003018490070790a0008018580c0d00002000b045901981c200c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 993868785 1250 993867535 993867541
    0xc300603330626010615050703120b0306042307031104361b0306140c0a090e0c0903160501030e0c1e010212070b070e090603070302100e04050411091b0f03 68
    0x2103000d0017180e4000081035200151600c0c00d15082401084018440e0b40c1b020866404510100300f00c4003220191038140d4002000030700041c1da503100c6603038802800290150104106000c11f4034184103a0401c0700d04c5180c0c5008850f26080c140254480101c4c00160403065001c500c00e01c0541031400258000054244010042031050b448505904030b103601d0300e1007044507160705246001e0041c4a281c5004c8a288000080404502200f40c80200386280d5072100024a84148007056010162041d900f01c0c00401100a560b070303041080e83c51035500311644250192501d00007404030343c0401020080c50308a0901c285082d0303694075031001c060103450200e0203500d0048004034038041c1c8894200c40e42280020b141d4080c00358600910b80b0402c40c55541400e040084001c2c03002c01e40c03040d5916600340e07200325418030040c80c0c01d0001d001a002e1600c4c1c500300424500001805651055409903842ca040e401d10401d6800d000f085140c0c070081618030b1006d0811001c1400030303548220540703415000008004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 993870035 1250 993868785 993868859
    0x30a0305160b09150906010b033c0a05010609030302060606070317090615010306150f050d1a030f0d0206180a0819030c3006033306 58
    0x7070200c1c40c0c1046160010389010ba02440d03403444000d2851100c40351400025582080c0000d455050300d0b101d131805d078255101c0864580141400c04840c414241860504040030200008414480c1107100144c00701810300c0045c403011200103070820000c0000f0240c0c00c0c8040ba400045c15a080300c400d8504550741c1041c0c2c2401c95801180601d00c2814034103540610002404c00540c0c9c41c050800d07444000301c20442080150b0072101688030f844003035002c0c0c491601c9080c0c003075145c59186d445141000e6150200420244c422160000b04000b140c084035591030000c0d003401c02114800101ca40c000313240007601e01001070340d5000001d00348414141c40d100040b0401c1c205001c1c0c601c03030719400b0100780d450715804100c1c0444080b03030614810001b40f41a849180080c4603540c141d03030307520170f8025121410b01401c00c541c2c00c0e44902d5a11210b41600c4200000019440d030258641c508a40341070716001034005428a40310325650107800701d100e405c0c1002400310907000600d002600d10756501100341c440c10144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 993871285 1250 993870035 993870067
    0x923070e040203032809080c10030213180905060907030f170403290f0f0117010b0d030e0a1205280b01081b0301062d031202070f0b09030a0305 63
    0x408005503180300300c1c07220f807005c0505080e03c001600d850b042c4640e0380f2030351515130300c0e0308410200da03210800c141c42c00c811078000c0e4010039410001030344003400d044c2c58a082460008200d1501a031880c0e54002c0c6409016044c010f02e5000f050050107044500d1450300e07102808000641c001e001641d11220381c03501051000c00710f600655100c212245203080000701100004001d0314505c5018a0042c0050b038a411949021031003032103c0b94001100d0303400d02446c2154803600040e0b03c01c05668509001d05079a448440389089280300e03a0300c4c040e00146010611020104580c41100d101c0710100315400002d4000c81c06000a00c002d880102010303c2c010b05020361000d500101500f84070042e0700100d40f4000101e04501c000c0c1c030708600043d40824110500d800c94032070b80314440700c0340d05d5040503501d010002812141980100c4146040300d42e00c0e41c0702c00040c1c01104143c0b03c01b680c0705603000c000e58418080182c004020300e2450320b0030407107030368003290f114040c8010003803c00c5000903240303840000c482 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 993872535 1250 993871285 993871297
    0x1030209060c060106050d0c0e0d060b030708030d0614010507051b04090204090606080714091b0702181b07050c010c03120c030b131b08190c030923070e04020303 71
    0x803c41d0000c0d6920301001d0b096078030024505000a08080c8030300001030103100041c240880240c07401c24a07100c1038036054010940f59817103541c9030051410005c0e812100b040a8014120340703e20000311203107030000d090305851682c40440c0c1444000e00447d0045100410100e41c1c2024000d907001d8851a500001001080062030081d80540b1f429840d05c14440c40740c0c0030700c0603540c45008035652961200484644070107004c241d00d9110046c03c00040e041c00c10b15074a950707140f441080e41d0742805d52641c00500000c401c15a01c0391080d4001d41000100e00c499015000c902001995951400280d41c03241c545641d660034a0300d05002c00420b00004152007200004050360001c00200440b00d480170b07005000e4004001440c0c414801a100c3c1d0004890728031424640450808012070300e41c641e500c09135400c080090801424140182840208440701d00a41200100c569000205070400d840c02448901c500035001c3c00d0003910b0401d200740c4000000f0322505696800c421800c8a0b900c520000f45144200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 993873785 1250 993872535 993872557
    0xb092d04150506061611060910020f0115050d1407080d030f050a0624050c030301030303050711120901030e242508060607020d02031b012c0103020906 66
    0x44400c21052045158407003200403054282070041e03440e11010031845001c1c182072542c1e030a5110b100800010b90b0290310003a0243c1c040e2000d410115050300007482d82094800d00c6e400350301b01c0d84201e41a401c0a1250f21a00f01941ea03039a14103500700004038010a0007680f008116504000d580c1040d501c007082a50010030a0030100c43c170407000e2183c000d000c0e082c9101c80184050901c4045001680f60780990030550700c00c1850308d075900404066080000043c94100804d0240812002e48540000e03c02940a5030103502c0104950921040084c00141104400303151604081c46da807081213040300c00c44000c42424038000c106948409481d82c00e0403140c800d40f014004504002c4545d118822100754031441d541d403a4a00e2035a00d907521011280541c1300c0c008000f07800c1c800028658540700000d04003081c00030305040e20321103555010030701c2d020240520320224151340d0740c00801d0707607808a10300a03036032020b07900552601940480a0180200f0488940c103154004c035418403561144400e4400032000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 993875035 1250 993873785 993873871
    0xf1b0117040501020c010c0e10050a0c1b050f0405060906090606161b0626041110020a0228170102070b010b0a0905010c111207150206060307090b09 65
    0xc2807510b14000d5121040c480000c0d400e100480b8a524040c244641004d407001c1c040004107500c0e958100d03130a912038040042807004007510840170848064020708001c8000f060124880d003848204141c039807604003040e200c1c0742004100001031710350741d403242d411680a485801d05501c0384000075145025010103c10495000442142482039010300415180006204110307c6c903100c0c00c0864007150f0780121551140c101101240a00d219102c00c168028022084a07504865050000c1c0620540c40c2410700143c1c89540300c5003e51411a403d110341c40984845807429001c890307580c01c415501441401440032040555480704142901180c40d41070340960304801c5503840f0b8008404503086a10a000000e8015602240a5000d103128942c1c4681054400c41110402c004008a051850090182034016080c001924200c0c6c0804908440f0840e000340090b858410241352030701c0855400b210782d041c10240c01c00e46a880d4403000c1908012210031082c00840078418482001c0400c241c000290780c0c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 993876285 1250 993875035 993875041
    0x9090402011407061d1c0f02070504111e041d061305090d11120306041d06010603203f0403080406050a0b010912020a0305010504061d0f1b0117 63
    0x5403560081c802c0c105d4507000340b00700b0469030706031a5549900801142c000390f0b164010500180c0900c06003825914188101d484680e01e89000c0341c142d6100311144150500089a01c1034544842c02c00031a106185155140c2818503109881201c24136991000521070212004038480751036071204400d621401d0032091190f1b080c43c1405a50307456025100000242d030f80340e00e9100d06007003c100c42c1811401c0074581421502c4400c1004001c2518101070554400b400c030303441a80c01d0003402200c1c001d0490f501d0000d5a120016000d03101d803200a1541c0f180080200003401039040e03282c0b100a0152103581d4400c0c003402410302c0fa405203881518014001c101c40d2400c10080640c804261407090344154400c0c021303510747c5801d100595156907009401310700712101c02e200302054112612100350009040c80001540c0c0e44640342100c2003620146c1e01c20307480700e001c0a151200c1390118030504000b03030000c0a00310301c2140c80c581c0b540e00c80d544006650100603001c0c0100d07845103c400104d2129001c40c0000c4e41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 993877535 1250 993876285 993876293
    0x40b22080c030d0e0a050f031c0809010b0f0603040602030c0408060103230f1b0114040b1e1c0f0603050d0206060a0504060b03060d05030f041d0f010b09090402011407 73
    0xcaa607001c0d00c00e01c9010241c0da541840f1314150014500007509040f0384500b00b804001014910f0102c041e014030610140f00b0f100700310050310404038030068441100c10f0a00d05425800e5400d00c24505014880140803903540b0749070310040740d6100307800040040e180d481d040b10000d240d111710740c020001c0c2c2c81080000b20074810301c049440100c01c4810b04a00b048101c102d910f5807121382c458000c4070280c000300c00c010440b800b80c44100028400514000603003016035910810290001d40000383c8400001c03030880c1e01040d04041d02c00c0701d803600e5240103003007550074100600704001056413440e015403510320002012010ba0840005107500c00240e030064002c40c1c01c002d5480340101c3e1003920800c01e01c0d800082078105840b90005450018200500e0740d5510f1007441403070100e5a204442c00c1c4020004c0501c0c100d2003001070b00c00f600081d6040c4c0040400d600c400701e031940015000d00d00341044000100003020060048628024094a0801003a80d681c001655001c102c2c5c1c0050201c1c0d400080c80c2030800c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 993878785 1250 993877535 993877543
    0x90303090a03060219091404050903090613080f0a0506070309020316140405011401050d0207050a0c0303090f1d070c020f1003090605130503030711120409050403081b040b2208 77
    0x20002c072518170880152070400866031108188220040c0301d00440e200941820f10ba005945c2c403401351801ca82c42c0c00000d102052013a8484049200d40014204003401000e9003031200d911103501420052560042c0c50300c800340c03500c90103807000b0245561400c0c0f040031034170305010042c8138414804911080079a42d030302c0c02d403078000d003a400e01c0d201d1441e00c80042103103c08100243e00400040c0c0d182400e081c20709071820000d6021013400c0c0c42070b22901103410000b51410441002543c07207642c810185620f00a02d022030000150010f03400c840303010018881d030005000c45107522503030340d15000c0c89001050000c98101000f514000c0d0300f0100c1c5025141d1040d41503007002c040c05200d0001040300d07544071007d10400e0031b5901700040c080e8004002103810503208008401c503c14101054038480c4c0040012403103598015808003001076150703000c00040c99007000cc0684d00041c6031050006d2403a03406a100c42c0e901c00c0b4040d800304c1c0403011600101003000c80c0e40d039034a0340f42c00c200388840e02a10b80741e0456075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 993880035 1250 993878785 993878797
    0x40911040c09080d050a09090207051f0203041101050901030f0501090e0c09043c0f0b0723030a020405060f0904050c040e0114120d08060307140d0602090303090a030602 74
    0x203038180044101c03030780c0c840c0241d031003118a07150140014900c2c450f012203850f4407081216040002480380800e06292900c01030110a02c41c078002c195280362020480c400c52500c604016405105000b0040410044240c1690a410902c0c0c115511004140103800500e01c51050a048515000004c500c001e1a40d21101441c109003003180c240e078203c00104003018608940091007120b541c9544c00e401e5003000c0425141e4042d980e888100c0d948048a0007015110610058440d0720212412205100802070b00175003003001c0b031a008404003d00c039044025200d01c1040140343c143c00000049aa20f0301d035055a001d0540200299507540c010a8006002e0f00051002e6114925000c089440540410110f42c00ca91600008403040da180c0542803003503d42c1d00b040c0d143c100804c07080388132280b101403080c008081c0c0039403a0891282010340503d0302d8441c85421424a0b8800101008102d0303551004051443e83c0c050805a500d90004020900394002c0c524140e130801201c081c00300c200401c0c0e40241030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 993881285 1250 993880035 993880039
    0xf2907061a0a06020309090a021207080f130206090919140901060e0709090207020d150f270b0a0e0f030d1401050a0b030a1514041103160c0302070302040911 69
    0x21240400104007100350b003441002d000d0b0380100a40307000c508000e40910b5200038600001400c1c0300e1440c14240c1e40f0b8108442000000303d00e01c0c104000c000e216aa6980c0000035071008000000c2d1035404144244a40d0304c40c14407540340000041c00c643c0d40e606469074036a05404092008040c0350700c1c5d0581c80729003a200c0f0240342d403c16002140780000ba030041c511852041e62583c0304c540c917003140c4a000f03520000060781c0003103d0740103440104600e032808404590f403119000030340d828410b00c0c0100300e42e00c01040c400884441c5001b00c20402c603c0100c440d2107038210010400382d0b2a003000309030051403c544000000c0c040d44081c401103040c0480540148440ca030414082410700828071242000c09004180e4441e8a0740701c1400b209690b00c000e1a8080d080520004000106140e00e203039410581e440401a109001c2c854021030070710f03029400802a03084151801d40c10320318820052542c10210000070031150406150506108002500003150098410404c040442c1440d08148950000f414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 993882535 1250 993881285 993881321
    0x1e0f120a021c030e090912040b1c050903040504021b060106050a1b05150702031314040b030106030f0b04020312180907020307050d050a020a0c0e0105030d0503010f290706 75
    0x80b11a520400e500d40c1c2ca5035259403080000b21409040201201d0302030b100507503034400d41c2c086400c00001400140050f05e00310f010a0b407601c0d480c2800d40f4800381c02c8030388500d40c0c1c0e08240c1070080200c00001610141c0b00200c0307000d600c5030094049840941e0100c0c0901c405440385000004d600c9410a000300001c4a056954048808501c00140c00244a490340206180c5c0000710503040c0680c41c0080a03001044c1c1c2c0705680c602150499034098010b415080529035a9134180110058541846950800c0c0b0040c0c0081c4500d038030710f841d058602e1000b0b550181c080c080d9140014219903082c0003600d6000f031803c40440c1c44501c800341d00c100344180b840c02ca42c00758081401040100380000705550342203a10000a00380e50305021004c644540003008840158866000c05000288808035128003404801489100c1980740c1020145841040b00e80901030120030801407004010f207548140548140302d4229039000c0388000015007109601e056090114004900c1208011484d000608009450101c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 993883785 1250 993882535 993882559
    0x501021801110d08072a0309151b0609030e03100902040c0504120f06110408061911040e04030e0909030309060123040b030705151b010b1e0f120a02 65
    0xd0340d450b6084403080021030350800c0005c1110b0b2040410200003000b540b540040810301942e10103d00d9946141140400d4103c0d80c1803007200602e0f10101800b011616000c466404090701003040d140c020807024004070b484100410070300d8010b14a404203681c000e0206c40d008420b40c0c003440d0080c441154105d11560500011409051140741034030160340744070100040070411a03940d0009080320780c90490303066444034407403140d0078403070ba0280c070003802404060805850041c443c0860701000384035164405180404110f9103d4810741501e05640c41c5581c5040d080d101c0e4101a6072020500710415403002800382002091640032016502600e2800d0850342240d8850444044007031043c0316a143d20711042041141a190a80204404443c00740644180c02d0b107450120b400940c045254103c6680c0004080d400c051000d540654094601c13070080155601460004061f280c0c2d0602d400804549601c14803103a6507074501c54038440b00024600d605c124001c00c002a1165001076083c1d03c640e003da207035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 993884892 1107 993883785 993883817
    0xe37020703090f0b04030318120c03110a030b0c0a030f0c0507050712050601140f0a08162112110604060b10170c03070c0501021801 58
    0x159440d00242809408000190701c0b890b00fa168030101001141d8500b02500d0076242d00d03103422488a08402c55940302d0b02004d07085040d201c41b420301c1543c100442403403902e04407407040d0203000c0d01300303000b1081104900f980e03c4064066805100082c184c00d041400415181c1814200060364180000e142c00c01c80d4200504a008518001030080500c01c080090100420b403c2c540e5a051803404c1c2c0e19261954418410000720ac10400c07408001e940e2406036043c406100030346100c0741c2035580d0500c42c0e03803080e070085601010041030202007111991489004003024401482041e119100c0e40d5030540d00b029550207804020721b51400c004540c0c024440a40180d008141c045a00c034806c404100249074100d1091042c804407440000101400303107200d0381e0002410500f1512a940d00d00203481415140c0740c02840c1c0d5100041e12074120101d04810b1260240a030f80e500c0304207030302d111 = true := by decide +kernel

theorem cover : BRFrame.Cov 993705035 993884892 := by
  have h0 := BRFrame.cov_init 993705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 993705035 ≤ n) (h2 : n < 993884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
