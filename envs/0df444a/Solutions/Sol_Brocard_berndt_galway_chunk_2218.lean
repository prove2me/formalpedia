-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2218
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:02:05.383931+00:00
-- url     : https://prove2.me/submissions/242abc56-c89c-40fc-8036-82a431c49e1c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 398741007 ≤ n < 398920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 398742257 1250 398741007 398741017
    0x152704080f0705030a0c060b0f01020303060d0314070c0509070507031707031805010b030601120b04061107080c030702010e09160c02040f02040e150a030c0509100302030105011409130305 82
    0x44a89503031164400c84450380350b48956a0003806500c408540c072030745030781e210316110f01d0244920400c1c08012180070074003807a00c0c0307000026809030300240002241ca04100c854120010f001e031030007103080b400b1001901c40a500c58102600d481240d00001d2219080020794650401d00c0c505d001441c1c400c554900414414002c0e00c90642014200042203046100c0d401112410403907005007680070400307251441c020881102080d00a0140b2f034000181c940183c2c05142c1c80c19088134144056943d0b81d5903ca000788100c4296042c1d00c00c081c4000f00110789004040d0440760a40001599075495500001d08240316a52000344540b01d01401c00018512131a50001071a901e070411400500301c174030014001c0d010b510700c2409035510120700050740e404100e500da80184284001c070300c04120014103200c0c902e1000d000241141500440800c03ca0424462096100180703c1d000f000c01600c0340c0c0001e0a4900c203071302042c2100c00175203400304c2619205100d250000780b83c8146009459450750301030014055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 398743507 1250 398742257 398742263
    0x130e04030c0c0605090d0f0c150c020301060b190f03140403050403201c170d020301030327050f01020f06180706030603050c1504030519060e01141609030506152704 72
    0x11419690080212300016070010f0008031402c80d0021450940c000c00102810005034820740c24a00c0010300c04021408a4880316040604042c00e076080702c509032206000c404a400405603603c2e9040031101c0000d080c82d004500c6950303181e690b207155003801d0030103076a16485102110700d40740090b0011380c3c4804012054841c0c14000c0141c0c1c6a04d400c2c01c40f0042c00010184000300c10014186040720107540c01103042e28400d40300d100600d01c10400040520072034590581205440e4881441039261000095620304d038144102d854101c5200d0842d8107101060b40d4584107008424804904070320207001034000f07400e2901d41040805d2444d100c8070b644000303191820707004184e03131803404019000003c1210051500601101d42150855940080d019014841900e18502d010007041c00e800040c000c414010001c1200300d0b5854540c14100300e221316501d06044148034012200000042003030048074401d419869440440c51070a4081c440340641ca14030703081c82401e94030b490031804900444059049a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 398744757 1250 398743507 398743523
    0x1012020324061912141014042123040e1006030c08010b03150f04020a030f0c05120c13121a0f0603060604050c19020a0c120b010b03040305160602221a130e04030c0c0605090d 76
    0x1c1412b0800c0031403042d034021300040c1400c14208550428580340c6002194143e590802c404d003800103040b5484c0100307010781d031504074040020403080f203140300c00150b01100040111a400f0b0030603000604907800004114080b0313846000c049200340c1c0601c6210000300140c01c00a04c1e042c442d413005119040018800f141108000c10f620500046681020b4060402d0581c1c080c818211400d1000c1ea0038400c043800380d0310b0b00c03001001861030240281080e00482c0054020803264035500100400740400400b0306240300c0d000d0008001c202d90042065a2040c4c142c0c005d860520001d04000801540c15048140d10a0074406043d0004000d400101c1c11a820f4030055900c070380350791804980501c41c00c0c104005004000610200b403210a4bc0105804c0c040101c0b4000b0003880010b400c010b01c480c521480c14101c86403c4503200f400000d1004240041b40034614121940e283c00d2901d120407020380307003500016030700d061903000c00c103440311080041c00c0d45080c028240014400058013013040c0c400d0040500e9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 398746007 1250 398744757 398744807
    0x1211030d0e0f1c0f031d01020111070b1513060f090e0c10090f0b0909160509040b2805030d0810120203240619121410140421 55
    0x10115000c0c10303e070160b105140d0303c16003c0f40e003030041a0284d00c18094808113803202009505600510400c030f030300420ba02101d0708004281c2c43d0101d0001001b040c084064070700811880c940c0d0b03a44140358500c20b48003103000030341c1428800841552001900701700c84503480d20000c190f07003100000320140720840844d2000c0e965202e0320411184d840c015413107000c1554034224082681c846102c00b500c0700207029505044a40d0301e1302241201400c4000c0c5a00c0815801c1010b07800700e06054112480ca150090300b002d4100d0310610380000c60001446282c4519800b104003030050703181c1030201b14820361071841c007401d44d41400c4500300154242031160a0b16074206001340021901c0901a003041c01c450007105c4007009460840190f240c0c1e40484500f8031505c46429407410268503090148261455940240d40b921040d07a1241d94410b650001080207100d4039480880c50788641c010b90034050f0301e1130040c104900b000d00d0a07058494120081c6000d41151700b41c0c0b0000303e507000c0c200c0c5009000a0030040101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 398747257 1250 398746007 398746039
    0x8060420120102030f04061803140d02070f0602251203050a0b040207140c0a08120d0212010914010911030403030b01110106080f07080303011206090206041211030d0e0f 74
    0x21480c08416811550010080049105039170300424400e50044809201659244003500707134400c40b1440c000c000c9200f0715860519024910302502d440040c07904010300d481e4890b1100c5e440e615040c04222a51030300003401c541025040c40b160340c8006040c40851b101c140c0c0941d109950085c002c07100b101055503d80000300291190b420544032002e010303000315641d5059040c010640140100c140c1018031500522410904251180e94100c070380c82009006070b070094284240a43c1c0c019140e010319560240f0456580302140d45000c0e000308040ca1000030010f0200a07408007002050384501d840e00d1605a50003951303d1840304803603200740d1500d00010059113050050364031002c01ca03c0d103290341d880d001c030201c3c0340302c40020300d2400c8003166800c03100100e9980d04029038070b1000b4010b40c181d000300c80c0c0c5084000781c1103800a0a84501c01080c1d2424075842c0c41000c8414500440162401100c442c100c504904080c8a1003588251610f4880801e1792a680810345045020344810702904408d245a401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 398748507 1250 398747257 398747269
    0x80a1104091d21070c24030c0216091503060509060f0601090b030a02090a0e0108070317070c0302211006170706021b0303040803030703020304021801030302120c030d0c020706020708060420 83
    0x1d0201c054544560011008843c6814180c003403070000801d00c1c00e071001c0d241900022b10500000011000484c400c0d051072545005403000d01c0c51900500c00a0b8001702c001a924021644904076440003000d0303520300780c1c030140070202000d420541030140348001406581c101d44100c07540240030f003030f025075941e20700400716440a149a1201040000040000c1510000420344408890080e02d1410f0b1500000089528901c101440204034200d0607204000604000e00700100d040071aa02c00304000c03c4010644c1d060000d4018510001a540c6100380300e0040340c2204414025604002410054207000d00a907442115610851000005443d001c0071036404004880c0900100c10669849081040300039000e500251406c0344074081c405019908840c1c0151360038100c9030954000e0240c081c0300d01c018801540240e1000c00c40e8041001030b000d224845000e406c042d510302d60f00a00d01d1078074000009092180035007042815420404c00d03c004a002d00c0c10010426400e020648a0b0030031084c00148 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 398749757 1250 398748507 398748509
    0x702030d0e0c030d0801080d05090d0b09030c060a060e16170c040b0d091e0f08070807051b040e010e03070602091914030606060406080403080a1104091d21070c 70
    0x2c3e26100d071000002d011070b1701c041d0060403103030900c0c1141e0119041a00513181c6000f00301681c3e4000300c58030440c90104850b0706149030007210301c5082d030f40340841010401d820301504803126025191101020080c2001601910341d204420291442545c1352003a002014142c094006000a00c061070124040d401c0100403100188808400f4a0782c0d000c0b441100000b0f40228602034401d21252940080d00c0001b021030003110329440101c103a940d0301c01d0fa980d040399400100040e6817400e0b0078030810700001d5007040002004076034003100e9001d4025074010002507890fa5403e82105904100300c50109450000a4990840d44a0b10142e294070544000c5080d245d41005e59818220402e400040c800b02c14002020342080184c082e04c20a548800900486104034891380380000c1801c00054042441016090f401c001c085801040d6011118117100c03080e045900010002c960702c2400b044a40c501e900d25508038030300100900130221a151704000c044120b000300446800b400200c440070001c81105040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 398751007 1250 398749757 398749759
    0x8031b210a0c03090f0807060605060d02070204050907140d06020c061f0801090201050a08040609050d020c09090c030303060112020f030a09020906030109240f0203091507080702030d0e0c 82
    0x912100e084880000310060700d49110803464503001500d40341c802c0c015550001d03000203480003c0c0c0041d50343e88105a00c411410b542c42c1c0c0e030b6641d020a0782d5490f41c0042181e03041384140540c80b009071b40100812a080501104059485000200098a81c800c80001c40075411500d03203160001905000b4081e2180c0319032045240070751030801480b20540f01c100e680311081c0700f01c450741080c0c4402d0928221420b101000e0f0218401388a903c4801d80306406455110303100f13060118000005546403031402c10032102c0500542c10a0841c860300313040400b1103540c80003200300108603100e610008a901c80c40701074400c42c100038148001c1504160150101c3d1110309084002c282c1d0780c9085e11418000340300c030410403480b074001c1901244c0e451805000c1e82c080305030040c8617454000d655481080e542c2c185a0a84096251103850980c00007036184060b5218031400c40141c01441441032800d01c1c404c400828000600c0504014801c40990000685d14454805000000d2074490000c07440d02d054181c284d06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 398752257 1250 398751007 398751037
    0xf0e100608120307050d0902010c0c0311120102040e01120201200d0f081005120c0a0b030a1d060a0b01110f0d08010f08191a01030506011d0408031b 65
    0x200624580c0003a00700c0d4400380544a8861500440d41d10600c020343d04600060018412081502800d52205482c58414146810001600c2d82c0e481c035110510352040e103800d030328480e00001c281400740145040074048002146068100307990304410500601880c00507000f00340c2c804085900400070004215405200014000040c03010b4660307902841c40e449000400c4104105040c500440034907004100c100c1c400c4c0d0006084c40240b1880c0b18841244540c50310032004d03410400c0e2941d0540401031306c030b0b40c00e5003641d86c640b4402d450b060780d448014021400182c41850380400c04003052103038100700011400f05803128104012150342c401400403844a004102c03080b410461300059066466034181c49000d400e80c0c2c0d0700c1d00080401401c2c443c49103250085100c0303840056501d28003440080c8540120134005e107914050041c40340090f007049074558401c0e0018012003d84074001d401a807260030010640d031a2541d0352141d03e00014020312014039804c1c0707155080014102c15102015240c0c604 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 398753507 1250 398752257 398752273
    0xa0b040506030c0706020c1e010b0409021804020103020d14090c012f030915090405090d021e030c0f0a05060c070305090f03070302130911090c0f0a050c010603060c020c0a08060a0f0e 80
    0x1603c0030400c0e081c8d030700098030f603c0d141d50a099428940144420642c00420040c240300340040682d0a8440040c022810940e00704400d000b9001d0030f05c200c0c803003001e609207036146a00d0703c00d40d075900d031004071403885040c00500501c80da804068000300001d0b040c07510009042d254100c010840c40c5025040c040c96100da03000c0f0503600d00140c014040e2070808011a400e1004c0e4032090040d03611104009403400058118080e001c01d03004003002c1c1c04080e07542d0402100e191a03400040d03d800c2042440e402e007110340166403440d042c0541006956009104d804ca0300d03140031000d50740075059101d00380000740149222900c0740e0899a080c05410000c44d0041c00303114101c045552020000d01c44a401200c00303400194030340102c0d0600c04502032058420720034180c40d1054075210049141c100c509041c00b004004c214111006c0c2e03080c02030100031880340384041049010004c0c01703802d21061110140c0101000709040001c00d900007199a00300042030303400500309050754000f00242c4800802e1050320304c10859 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 398754757 1250 398753507 398753533
    0x30f0706020d0b041a0d020607120f170f01181503140f0304052b0c0b071103010209030706140d09050a03080601020609150709230a0b040506030c0706020c 68
    0x51030001c003000c80403c5044810001c200840c0d451055100751a44090080e50090a03c12001180c2c1070000f0315041c10700415980c0c407410307595460313110310001e0009040c003440184c101304906034a18200305d8555540c640f4404860b910041441011030005280702d59001e100250303441040302c814000323160200d45449080510407020540713481c2c00c0c10321561443c0c8442d1040070068905076034000f002d80c424030b110960200da44c02a540d91421920024a0040001032601400d1300c00402e16030030311603220b5955043c0100140e2401c1000c0380203034010043c44174595400b041b5078069800030b0900311508a085c00c60301000d8003640c03060591003464030482205004002402c031641e030340300e9070f510351059444000480e152501542e8846181d40204016208490040314080d03115586e0f10344240000d03500e24101d5062203004e0b4543d42d41e101803060400203410102055005131800200281c82d003071078030011071820700c00200361185501011410800308859601280c004c2082e91044442000b4801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 398756007 1250 398754757 398754761
    0x101409130c08061e0f040b04180b09010f05040f0215040f0906030c060203040f03110f0d140127061505100207090b1504090513060e0d0206011d0105060705030f0706 72
    0x24650520800c009001c8204903214031319503154211000e0250281612048203100c0500240901c096115441c0c42c42562a05486000030200a000e0880d401035411b200900360300311507081140c90504e90900e804c103c0800c20422020110986c10345d03298105046002019003107000e290800c585541444500180002080d005401900d0003440001050390b96008280d99074403d903c280340c4404910b000400200310400d501e290100b1010300b1949811882900280317212601e00405c64000c0499480450703580300901c0b806440b4a0a1100340300781e0084001a40d4a0b041c041500610140d22245668050540e03100c00d0401004050b00c1c4510076880040041d4072948a4000d0660705071803c00908464503000c507241c6000c2d259260180d18040c01c00c020390b006014000d0889498a20086149000138030b584112880c60071803070701074a004100300000074200030041c2c2c4900044036804003640401c0340843c01e06811154200d90095580c0507074602a4114010300000001402001c504503041c00746503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 398757257 1250 398756007 398756011
    0x2010f0c0b09030703080115020703080a0509040507050d053411030a0801060206130809010e0613080f07081f09140a1101030c030c02060f07030b03030d1a101409130c08 74
    0x1c1c0c40303180c1b00341c1e00c0700c0d0840c04811400e0507074001039002e000d04001180c2381d5001801003040f54940145090b9121012405503042035820f28000b810009081204040b180b20341130700032440e81e44924920400c4d50103016844420002c4040e51105c040202e00d0140c01102c41a030740e50b040d041a40c1d117400c4811070142c0181400d200d4600540136038400540b1283c1c5a0350114011980545c0d160304294000d00112844108041ba940d040381c030030410102081c2a900740c0e48010001d00d001800032004840e034050410059034003088150f800400318014180104545055020b607440d0300144100b0b60342030003d60f42169904500d150f0107500303500d10501201901201750a54280c80074442c866212408404840d8032607011401078000c807008c507005020940c45e4681010440c0380c00714003099002c000070304542c06002d02010490703070340e0b051f90054081c2508484914404443c5091140c01751040a480380b166a424000d01c000000f4103001c0382e90310200300488100030310004101c080381c40180540a0708017 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 398758507 1250 398757257 398757263
    0x12010f090506090a0305070b1e1015031104050f1f02030c0d0e06030414100f090b010902040302181b0304050c1305090d11070b0a05131401080402010f0c0b090307 71
    0x142c00300280c80305000140206195605035205440c0840390303260342503080406800541e405905400075540d843d20398003080d005240f400c414140d180d1801c0702003001900203144150030325080c10610054150700710261802c442c0c2c05c2e00d00308030115500b0000303645c1c090080b290311250282c01440321540c81d800805070407050342c1307101160000700202c80141c48442800d00c0c0698400c50810004000030700110340b60003802590000c4480075842101c0d01015500f104a8035101c0999411903071081c0704002045900429180508520f0706003581c000c20f500304807054040e040240b01101091b011180c0e96104143c00d160754001640b2402c0c60320703003952149506040d891050b17a1000340003a071a005c44c0300e840d02a1040b400145101900d08030207036102c455031105810103000e0100b0000d2061080780040082c0e509507941e00c0e40c1d400c0b0051409480c0e2000e50480720050f56001d4803054266040458a40c2044d02420034a0113101c101004a850042c00140203040f1040c0c0700c14804210000000f030865584 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 398759757 1250 398758507 398758513
    0xd02041d1005040501051c2d0b0105060903071a09060708030108010b040c0801050f011101060602060f160c0602090d2001121803080613050907060306170d05030612010f0905 76
    0x25580b410403003a01c000b80202a03000c0d00440001d0032406a144100401034030803a00b84caa9504001c3d80000c403030101c0c03a640007041c242800d00c42c080090729140107000d04401ca58950805242c5c3c00425500d0880e0301805800701c520079142e001300c0300c0b110156818800c3c020502d60740c580491404407100e130801e200e144020741c01c1c02c0c4c0300612803074140198501d0300e1403a651080941e00c0c01040103207442c200760040d41442010707030800d1b442600a02508000d809940c006100c035003030484007040c0c1e02900800320b14042c054000400485688080000030f55604031901680390303400840003a01201c01c0d240010452144d8000c000580d00352109011200e81302601d441c01b864028603006070581d0034001440c603851014241c1700000034090441c954103c032000e00b00840b0300000140c031500710b400940b03540009a0285004000c1d642e410f00420010b1f04601d02581007202c10003031419a1032485030b040c0c4042c0000400002d03502d45071040d84040c12200c0c0b0740240000146100714400514845405441c00c1c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 398761007 1250 398759757 398759759
    0x307023904022803090b150f01050703050f18060a0305040b070c2414040f170c0c0f1318061d03040b0703020a0b0115320d02041d10 58
    0x86400c1c420b8403da03854642404481480c81540342d00c001d01d440d07071841c0916554500a0000c10300c24040c442c46134140304a034500060b408001c000000060070030f581d04002c810002600081d91001c152480b070207100382e086458031006c030000501102c4c416080e940100b07001c07030050821581600518003807401440001d5030340c2c945600c1180c05100d107a00141401417442013002d020741140b040d00d01e003034030828000034000ea880c4050301c078003020544040d40d00c0c964040c0407009024141840e0828602002c260320f285c90b1100b20201d4481d105014504e101c4c56401010030141d8a83c8119281d0f18462a00208544108806110a840c080086c02c1e62f802d80b030080a5460892202140411050781d20011801c191170001c05030f90b90381c0100720460850103003d0305c0000083c020714010707000e454241da40248040d5190002081081c0028070304035240a40003201c12580651943e0110860a0310b1300c003641c415116020340064411a4001c1030b58440e6001a0700b42040100d041a00854206a40e10780c09 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 398762257 1250 398761007 398761009
    0x12180f08030415150e0a02160812010e060117150306070914040c05040302130b0a030c050102060709050f0f190803210c030a05150d0b10050d050606010503070239 71
    0x380c4500c0c512503030000c0d0031401803010580b178403045588240d40c4040549400c0710281c044490072580c500c1114005004102000415031403140385000d00344854246002e072030550002041940c80e0740e010030026a910b0003040300c06003003403013803240301d50042c01300d46250414100003010001a0b124400b08802141490907091a050040d0300c45942307160748590609080d0707000c1044460f4107800320700002c0c1d91400d440f59a526014a901e000f140170721003a118540c6400006170a004005210004001c11140240229520a444150107090030b03646c1c514a0110600440e4403040c41c003050781350780c20040d240000c00020020041080302c41d01c01c410303420b0b4401408040c50a071070039140c002c480041031000840d11501a84030b503500c01d6460502002500c00040411207428a062055500810710400c01100246d9001c01c080144401d4520701e0011100751a803d84940e0f0141c2000c2c100070f03000010a03c0140b0820203400320780c1d0540ca0118495408800c1604001c20200510740c0a846882032104a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 398763507 1250 398762257 398762261
    0x31912060b0f0d1509060603090618120e01021009211806031e0212040201030e07030b06300a0302070b0f09040b0310060603020c0c0301020a12180f08030415 69
    0x72000045020308000e0540f442d08050310079009030900f01c5034500b4001400c02d00601035400106185d8400144a440c00d090030400c0d0b540020700d04041d0b4410066141c009800d042007410950b19502e00b111600da18100101c1c1080021040d0201150800c036220090042e1188042640301c51015440e03080300e0040c400307881d045641035000850714414a01040914000e4000b0481180f0400f186c0007001421400b44e412a080a140b0240098581040004558041c40340c130545032800c400501042e440c1d680e40b80a04600201000e00600c0030700c001e404043d200d540c111000002c00e4050300c041d90f210312210ba550380001142580184150354001401c88044400c8464108010060501d88065441444081c01000c00c403e84c06106942c0050504902d0744034002c0a441144d0b00940d4501c55113084a25044044010612903441005030b441d1903900301140c2c0c003560b0295200070810401403248100c0d0f40d031070820082c0400d45480c15850810030604019886948201030640c1c4101000800d001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 398764757 1250 398763507 398763517
    0x1206091d010b03100c090302150307030b030c0d02010507020f0d081905030f04112107030c09060e0106110102040e04141504020603011701020c03040305030a0909050609130302031912060b 82
    0x14064012020344030880101760080e0a050800d800c10003861a079940c04201c040c1d1841d5440d48052070040f062200c0c031941030041e40c018140803001001c0d0014000006a0100b5200e60000c0c14004001010300c11502d40d040c000d000c174140102a60401889030401d0f035840d5001c1090000c90b00c074058040c0c61030f28050000d890050382400c00940c42542e65590300c483d10110304012a0384050381950030b08014149080210301c0d02480000340c40010b140d0300d8640704200441d0032201d005400c000703061082c125450f0940341110b01c64a080410300c0f1509541c0ba00910680e0006146404014104402e00c400304081681801c12071045414441d803991034500c01c0341c020380f002940900104010012481d640e503d00c10400c2071600018501500803520518580c420341c012a016040424205800c50700001450010850250280300e03914182c000200904401400c108000c08081d0400e028103100300300360761860300051039051015054030340183c101484240070003d402d00740003001c56000c0780358059030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 398766007 1250 398764757 398764759
    0x140114130c030f2a0f0f1a131e0e0906040c090c0509033a1b03030f0f050610020304121e0812100b07020d0605071206091d010b 56
    0x18941d06550703440d2100b0b00740c24000c0c2c40380080c01d9a075204c0ca02c10708090907142c1451040c00e024662500101850501a50344001001a1090001c1018801d00c1c2c0134505d04095000620b80d40362160080034500401581080e90041c09200200603081d8610280005555004010b648556649001d1a070340300c0c022240281001c04614040040c2c800f940c01c800403003105802c0c210304044000021a107080030003426513111010010980c1110b0b068108402e500b40300509c05200301c1c83da00e04001d80124401c0d25032024942c11880c280c03003414440c1d40f01c03443c6c0d03101d190024816441d9100d4000050203090381d0044c4075104020000447c0e900010413541100d400f41808a00341445440d9840c40c04092000c084c000d102c1c450a520015a044009040130600c100b041011b509080140015200094000e07811030782041002c0e6016a0341d00300890711030707540140b01180587d582c0108981c04070444841c100c0160820341c01140840c40d640051024101d00c2ca4403046520600201a0994014103145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 398767257 1250 398766007 398766023
    0x151a041205010b041b0f14160308190b031b0604090c0804030210020c070303050309030d060e090c0102210c1006080d020c03070e1b04080a0b040b100b0a0e0d14011413 73
    0x161000078091481f21120035a807100c002d081101242c0d20341c4a00c141c580e0b0807030005d0f002c0740400a50071500c229400000007007001c20829242e450020075a184a443c68500c43c10f110b00da00d4660030f58418044a002c1d10020009000a2710044030140c541d55055900310090f00960b503614400d000203100751400090400000e02d01e10b40340d618155055400070b050702083d07010401c031060b06019240540350050001c4104132149140440c0d0043c01d009403503803070a0442d08000d01506081002da41001ea0b0901c80c0480342e5030300d41c0800030345454036485510403490107051030300018500382c0109100917044016020344a00620075403c15807551060f0050300014801200800c8070b07140101e07180500c0c00324101c0101d00c4c2c1071300c800b000c926080c0760f010104c0e0300c0c081c2c4004200800c45410030b100e80215265058020180c10021100028001d4200c00010010101000d09643e40c4000c08010303003540200d02d5407545040304041a001c1c0a60800400495881c180816107108803822a03e030096004528 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 398768507 1250 398767257 398767277
    0xa0e0f18120f07060603030807110606060406110c040903080a1a031b010219111002150c1602120105090105013006020405220f151a041205010b041b 65
    0x21280680e0002c0d02c0e5000d0700c1905024032400541c1074452200654020b0311a9100d501d4500c00040091b1315400500b00a40c00840600c445500e80d0810303036027540c0540c2050005903600001480c98034246030141640036003800e01a00505030013055886c02160500c0003485211100140c14107906007005946805511201e211199140791040c4c2c0100c041052040d2501c411407040300d40a501e1014506032a5000c070a9000c20702450440b070301000f180854000390556000c01484510306d00300080c07039103140f20000602c045c481031101c40c003d10a0750380182081c49030b00c2081e0786140240011154144550f2901e0700104440115400108042c14410446c21015110148605884119a20881c1d140c2d1b000d0002250b90b42d2441c04000c140c9035180d550f18132400883d03002c1001c0d91350090001c800d0a141041d06505405c01162034410380d1400900e00030554501c0701e07402c07c00c0c407881d44a24542015001600c04108040d000742611840840702441803544507504c50f030070104606403c5000c40c000d141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 398769757 1250 398768507 398768533
    0x180f020a0e130207030c1b0f06120f09020f0f0f1507060506150703140d0905030705072903190c08010e060a0b0403030f02010e0f010b01030f06080705090a09020a0e0f18 74
    0xb5501903201050300103407d06a2345480800c0380e24000d40040340419003880306041c0000c95403166601c0c6e01c03220201484412402d0f0042b5044805a02c0000d0103490240500411a29003c0c003950b20440c010713140c004d01444044c075840440e0401041220f00c0c0f42404040360360740c41c00031001014070385490216032401a40345d42c150b1742c035a8041c12807a60000140301c40a07000d05284039841900c1d000340c0180d41c0c3d5060b00e01d44103040900a8204028510144002d101c4e051000c0202c424021803000100d952600d802c607400b0303510b41c00d808800540d2810880e6040c6072960103020b050494038180e4a030500780e00c9207010000c098407240a40b03c41d041d001d000400100344101c2480800340e03d1800009903641e00d210503641401100c800889841c1e44801c0030140d296071601c244400040c4108040082e281230403030154a0746601e00c1842e01c9140c00c0008210900c045620203402241c0c001d040c3c5142650b181020f05c00320208580c0a52800210b80006120446103c01ca0448480e048040c00300d010b0650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 398771007 1250 398769757 398769773
    0x60328052814070908011d0601060509010905090406150b0708030a02070f02030709020a0e090c0a0f140d0504020f030d0903030305090a060905070f0b070c180f020a0e130207030c 78
    0xc0001e1845070b02e070000140034120b6004440c2c0140d0b9075541d60185682081c11003420744810101c1001d24211400d00107e00e1240460b41505407119460300c50356a20001004807250982e981005a01c07004140074001005100e502c4040c40440f000740d4410803641d940da07480b400380241d03d005000c0c50802c0001482d801004c3d4000d060042c8030710f810300c1c3c4005140d00424a0036007076400c984021307640022000101600300c3d802020b9100201c03038101403443c0603400c0b20398a000340c130090414810b04541001c0da8901500d441540107a5080415031200d0010019030003600c420340301079010351605804042242000f00e420352180c201e640f500d200091850340c3c1100103100c000c01e00d412030702a15942400140d041d0240700600341c046c40c020301e00241880406100c035245903000d091402d07410050350f00000c08600c200d004603201e501c01e031038031003c1c81c1c402400a04007082c000d490052000503510002500400e00c840118415183e411040c0071840c1e4460803446148005408212418124400250b0300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 398772257 1250 398771007 398771071
    0xf0d0c0209040f050609060613110d05070302040e10050a0501170f090106080102120105030c060a02100c090b1611240f21071b03120f0b06032805 64
    0x408001c039040c5829120117060a40c01c3c1c1d40319445400100500c2118646a0342800d5801c130b1160003000349040d142c440c0e10b814410a16400c0103652a180040d121500a070705031401810070150240310f42c50040340c2c8056484090180340d00c5028442004906940b142c1e02601d24000c200c4ca0000d036036110040c1855950380c0044c91480c80f592961404101b00000b8000b03400d06400c0031034664495418002014100541e00030101d000e002c080c40003110560f40094400200b0301e500400055a42050404030707440741c1c1d07981010382e9111001580700070300e600c0f5010600d2590701408031103005002d5081048050101e92500d070b041c0d18030100303415410b42c2048000f07050001c03880c0d58141c82c0000d82d641d5071070040400485002c504a0038010490901c0c6c001411520000e460b044c0112002e00359a07000d4866a429101d142c075555660b40003100200b40c1d54442c0305620710040829480349860017a481030840c80140c00c0c40034450045007130700c142d102030180038000e00200f0b02c150545c0e1103628040d0401e01035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 398773507 1250 398772257 398772263
    0x101406011b1502120f130b09070e04080d0e1204051309060e03090a080109020607060e030d0f1b020708060408130e0a021206090f0114040204030c0b040501020f0d0c020904 75
    0x1941c00e041c00141904491028400b40c0705405070311a01003200f85828018018a020803140710102082101d00250201c0d08410364070005040c05502d48041c840e21300722583c2c0103c4802810a028007040c00a03802c0542006206200140700341c10140482c0c07038031100304000103040501c0910003070203075140c941504080c0603001c1d01e00046440443e140d44040e40e06110050f905da4100040c40045801c0081d444805840100000c1c0802052980441c000d4803032108043c000640d02c0001800d600740501c11244090f0280c41d0510540f85a595184001c22804070017046030000600701645060010070168216500b0601410b4155626120702c82103901c02102481740d80c02d1100041418909014042c0c00303403892071801600d4501149402c20b0801e0090206c0340b040c40c0356400c1101707502d40098114151341c081c0c903030358880b800400c002c03d000c1e010300e80000705090811400880c152001401401c110f0340240e00301d0742c02a1001054035100c0b2440b0200a0016140d0fa00c9407016040103010b481d00244 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 398774757 1250 398773507 398773547
    0x30f0522060c031e1a0102070b040b03041a090c040b1c0b07050405130c09060503061c02030316110310050412260109090212070f0303080406090b09070810140601 71
    0x4134461048000d07550081e11603240b1583d5451030b03400b840d05404000f07a400b82c02e00082c0721741744c00c042050310b090180b0301c41c0c2c550042002000908102c40c0e100e52034040e0046c071a29a8860410184e801d407503145d00030556000e00d01c4c0c880c003140320b468180c80c002c91851030f0a445104548050700d68140b01100100b050003400701c1004006003c0d10f40b42e5000c4d2449040741c0300020810042c60f0010140b0304903a100b0801c000040c81030100b40c0e40c43c83d081c11034200154880100e10791081c80400c1c00d5006080010744032012408031074080c0401c40924000904040301910705400c1e4151100d01140c800307480282040107a16036005400e40641048011403440070001a10903504501010441c2001d8000f6001151101d41c10030860900390f000a90b264400d41c060b240c602c2c200100106421410310021302040408008101070110503400144c03402d4002648142c1d51030110110355852109108141041c418100650418035803482600c901c4480c05000481d6070300d0b40c5004484040d0162402e4840b08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 398776007 1250 398774757 398774771
    0x6080303011502010606030c1b022d0f040e0c0d03140a0f0e0f010206071b0203030406020309030f01050702120706020d0501090f180507030f14010c030f0522060c03 72
    0x50200051402040c03031410004100e2040e4400909560150707101c00305140c10302c42d07401c00301604205421300328203400312040341d52201c500015403200310351020310302074210070640c0d4001203409102c000c1100105032480c003150141c081c148811911b0203a150b401c03907000b800110509141c10940d0140c030f140640740629003030f043c4020816547c0d20020030308002c1406142ca183c07240341c000b0050401c0b91000c480c00444180140300103505c60500911080402004442c0e20746104090042c0044160300901140d40700d0762600e10195480e40559003261203440362100340a0145014041d42d80b01e00580c0d4090f2a0400c3c001c0c026400540200500303c4e50142c091040c0c1601882d1031007000c0c004c0000040115005100c85840f038112040009405500b242001124010450009002c012a81e110302501c0f8054014242140b0310300c1e4012005a042d420018010b90296060300101c640701540542041203440d40b05121040102c00103c066101146241c608080380b15a03210601221141c20045460 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 398777257 1250 398776007 398776019
    0xe150f0613140a180b07080604150905090610080307031d190513092a0b03041a060d0f031206090c052820150a050f0f0601050a1206 58
    0x19480b40c14014421020020401031000d0003401a0f035500302004a8008002d00c05480c0d1020401005010070705102030351004c40c0c4c3c2d07070722075070b0118000368120001c250030300d80c403412400d01600065603034038050310408000c83ea080109a00f030004845480000f140303003120070354081d2030b510828642a00390750700d10b4010040940f034404403c40448180140041d42d2401d1004000792000c1560705c1101561610418000180c0070040660507100c41080980c014040e800410141a00a4119804108010050004101c120032181c442010f030441005040d90300c090a1102580b9150009024000c0341d01d4800007180c02200e1040d004030034103c000c60170315113400309002510102204040040d00c0054107964400b042426440c1d25106042d2010f0100314040008108481259006840080d10440301850007010810715a26082c448640012441d1040b50000140303011a03048400d07030f2910000840c01c0041d400310f944a840e05031111401c08000c071004031101092a21003201280c1d0f9144003240d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 398778507 1250 398777257 398777261
    0xc03030417100e060a0e0615010305090c03010e07080f16090203061f0f080a060815280b010e0d0210030207050c030a060c0906030b1c030e0909030901030e150f0613 72
    0x340c02c3e4200030041420140b580b03c04a814507544060b00b50010018002007900080b50662000002d1801080503110312003654100000b0716002d0b0b600d0341c6000d04d103400110b00031411004a030581e00a8034203841800c00700d542c44003132006181d542c860049106102d56400750703018641240c80a415140d1259030301e070003074807045012149170006c81e20055404207042e510040195022aa00700709100c0c01c0d1900305e40f160345d0100b14110460141c0740d13038001120f241e07840301e42c1406004000070780304007400405a908000c00b5488891400110000e180440905080c8860b12030241d02a001a611a40c0c002048000b9080b00e50102d03014020b500f010a03850f80c041040581c0c0c640104000518a2800e41000d0115a040c2d80001b003410b08100d1030040d0365540d030b1200c800070208200172241d441d505203012100c070101d40c028540d0005204017889540040040905190303482a2001c100c052464001d844c0d440c05036004903901a02e4010000f01944a400d06032034015201410810818000d036084c401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 398779757 1250 398778507 398778521
    0x803090c100e0a05010905090105010807020f0d080609070f021b01090902030f0a180803040615090507121109060d110403020604030f06061d13140708011407020c0303041710 76
    0x400501c0d0440a96010300c2e00900d540f00500f024208030103440d01c0d1401091340104144246410711001c1e00000e0141c81c0244210392002e4512801c2d03994040001c034010b0706d104c0007603d0240c010803100c0000345680303010701d00c0d40398610747d02e800a02c180603004c038400203140a091800c03410080c603400700280080543c000b41d8043e0360501c0c030009040c50310000120880c2c0000c12030300d808031601c481e0031010415100490350050703080000030401149114241b170b00c1002c103600008200d0303d014200110198040801d00d580c004504080c00651074110702c41400b8020580c142d13512a004000300c21100300c0c1035215045003040904210b04040d80c0307400045254000382d00c250b9403050441040410010315120b0b640140c44101484043c00c00c0f8408074240711030008100c05408110030344d40a05002c0da405241000d520510304031000c1c20344904045000c2d000d17003081100310303060400c04181c02c203002168110030395602500840c1043d1800740074074501c0084600f1142540143c040c000002c0d8218040d000b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 398781007 1250 398779757 398779789
    0x915030307080c01240603050726061513290a020d020c0603040317041a01140f0f03030304020607060f020d02040501021605010915090815040506130b040803090c 71
    0x380d11400d401c0c3c0e1181c01d41d460401801c2d1000e000341e007890104804001c0c3c100941e801071800160560354094141c83c161a0b0400c2d1768410a00c1e1003211200c5c04480510500c50f40065800508000516580c04001e0151000c0220004140a400d1200d9030246802c9840100645040b06009040303049006d0554022031140300160090320703903403003210340410044025074020b5070310a285150680700200100c420380b2401c45400304410100b01404540b801d4121000b45d5070b9240c03055540d5554003840d003441c2103000070b0f0184c0d21411400b81e8602d800405c4816000024014520b1965164208200355110084c11501660390b032501d00b00001403031000d88040342402c2c60050b51203041c01d001910f409040444d10b0b50403150003038144020391b0b004015030122502d2034204102103180100c10b43e00d100a5800c140c0c130b14803540007005600c4030350030081e60182d80200c054075102d46845089038141031141c20090000d030341d484c002c00c0025403003100441c0c0c4048458140c92000389400009503d0040445201e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 398782257 1250 398781007 398781023
    0x10806040201080f0106050a03020f0903060a1509060f090506011b260c0a0204180203061f0506030f1924240e1c080d0903020d110c0915030307 63
    0x881107582000341113410081211004450f585465001003540c4190740c40c4504040d0082a16124480380909565001000800303981301071030108004401014000182600c89614070400130f0318154034031815094805640b040751605040400403405008050315060400c5544402040d0321000c02480504280c42040d83c1c0411086078021402000f041540d0300d280c0040801462446140000310540b04076130656010801103018468100902650803019400d801807004000d141c80e0300e00041c0074040e01a01010410340d84035424000c20303000071141c030b400502030390001c101c1000482100501d0001001000308180b24014020050800d48024a00280d15a0002840488403d0060f2103030180c0103441d4903070580c80000e0041840141c000b40e9030051884450102c2440d6400e0038803144241c01802c0255030341500c1115400408507048150014051004002030790340c40741e154201d1007024200209049151181004081d88010384507100e4280c550100101740d4809002501c1198003c01c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 398783507 1250 398782257 398782261
    0x20912071211120d110f070803040815040302070303051e070501020c0d0e0303040509150a03030f020d171f080f071e1d0a0b2e03061809060b0603010806 67
    0x4501c0c2d0110021080d284180c0340407a145078000000203003640902000d152903541100d20222190070241e10340314011960140315004034614400100a104684604040b21001c0460a4203050812015140240140c01204041010038403940160030081d10001d00484070811503564804640e00c1000d0496850b500410081c004101c180301412882c0d1443c02d0546076201d00d80d001035121301c2140541403080700c00d00007242001216042010103007401418040049440f0700f0090140f0008038016001485000c50300b494484c8100207840e08516406007050950b180c1c04000c00106c80303001d0855010000d1301130300007006e0000f000782a0311145102c2c080c20020741401c1d14203100300b80041a09103851000c500c00c00100c0036004002c421001c1c3e103403c40c0803640b1446e03011006000300c5842503601400e03c01880b8a483c20790008412107551107019000400209001035080d01c00a20070103201c4400d0a502a40142103904040d5a5034401c104c005010007601c00028030381d80080e00b00c4551540403170300b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 398784757 1250 398783507 398783513
    0x902120a140c090114041a07201e010314040b18151302270124090b1c09050304050442091b03180c05040209120712 51
    0x4501d26020100e10003101603403030400c0c0c500d0301c1c502c902c041080c10800d07000034100740c6007900343c10744014145000c0704846405101038141d403c2d410412050323480b4030740e00212500d0200460401007190300080c2080c0302030031008020f0200076000c00321840c18103484680ba8001558101a0b50b03110fa403042c000c080b160308040c0d000d14400b030700e0020030804540c004c00f100580c00c1a1228220380c4081c4081c4100103080c00b42c400b14243e4000c043d00c64142d03158820708018034010030f041d11416141c070500c1d030b86035180d002490f040007001441c0350390b004101c13562000c3c00714079420350080c095000922942a640045602c124080303469456064a0a1304007040a01c0945058040e22081c0c1e00501000c140380302510490409458540135490341c490092459111188071001195000301102d0300204240720300e01c000c0b054000c0342d01c09440d00003481c2084014404009900f4114400d030400200e4072a40d09040a00000f58048079515500211444c4c140e80d0310901048040d000c2c008600801e2180c0c0340601d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 398786007 1250 398784757 398784761
    0x40314160602070e180a0b010801020a1b11130605060406090e0106030506130506040f020c0102030609010602190b131e050601061e0c140304170712030221040902120a 73
    0x3402a10840d0400306042180c1c59101000740e4100540028204e9510004020170745050141d0500800080c5001c000084c082c4065001c2d00040800e6182e4005080060405283c0d0800101004003842c140c1c0c00c0b891440d003801c0701d280c1000b0b9a801300005030b00381c54100051540c1c005a22140000750f19800038440842d40602681c018200c0e030500b8001410f10740300250000c00c0c501d100000c165514030020302c040d036494201400800702c40c0011581c0d490300f0a40d69010354422501103000c0c040000c0000340c00c62000414003001801018454400681c5984d044c40321a8054101c80c846810b12401d000411780c0c421007210041d40c004084c080c40c40003464141d0510304144c1c409014020090a09030706a2100d5400881c1602545041c3c0d620810514020704207071403d03000e42565200101c0d0128080382d07030400070740e80d03041e450003240d410700d03561900504502c10408008005070044900c0e011544c2004114011494481900f10f00b81522001000e08907080701d11000786c407190500902c183c680c0d0303078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 398787257 1250 398786007 398786009
    0x5041b031a0a05240a0512071106070318020a0b13060504140f040212010308090102070b090307060c0c030611030a1811060a0908010207061d060106080105060f04031416 74
    0x242030080484110715001030300003901d034403d450040024242d9070300c1c400e91a050814122400790425074a400103020300030401c4d00700c100403c02540c0100040391803c0e014860502507001e03c200144502d0740d039540100d000d040b0071182c482c0035950018420005070703a500102c40142c0300c0c816016860f5804000c0041c000d40380c5a01490a101d02000144030320114044940101001030b5082c4031a5400c2c03001040080c420703101c102c40c0c20450310300088204a0f26000410904100341d08603030311309466402c909468400c7e21041c6601d580510001c1210798005c4030000d078014010b2101d10b00702581c0c2d8580c0003d031440c0c075600940f02c0746c000013005041216440344e0420355100058014504181e030340c1c0c190481c82c46890261207100701290ba021080c2c880d014080c0645410303402903448074507a2811304050100364548968a00c3c1c0c0061080f001d06e000103046049035203691341c0e201140d2034a024410b09074000c00714410010800c00c404070101f0b48039030400c554024500018502e540c8402d030843c17002d80340d07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 398788507 1250 398787257 398787281
    0x2b020c1e120c15061c020120010f0b01021204060c0609050106210308130b0a0e160608010305010b19030605090c0a030b06030d020706230903150f0f0705030a090c05041b03 75
    0x94044d45c405e10300301303401010070b40039828206585d001000309a140d03482c0d6108406c101c0c4941c00c200242501d0492600285080c9500703800b1100960b010450142d4580694018800050203440821000c50020f410001c40c09028000004045454945a0a81500c2c00d40401600c10002031100304041c1c0c481c90b103651281016501d211744034030507907840a40d404042c2071107005075118810300003d0b1000b445104811602045162069503031280060414542444280c1d544d519080f40c5047c2420030f81410190340740030b00c1d0480304060455507010020000a80606198801c0c2d95503014581c859261100113540035036030a843c0f51402d0002c02d45441040300d0b9503800c64020190070010700341c1040201913410800c44080c005862a001d00314180c0c0980f4010552502c0351800d1044e56a50200e42c0c140602103158034105940d44100e40720501c94000d545e00c5000900400c0011600c0d01260b206c500e038135202d0403581030820398800004041c4c07003280c0d1008103000d00d07003100000802c0e010720600e149100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 398789757 1250 398788507 398788519
    0x605041706040b0705070501150f0603050108030c0d0503040305070b010e0105090604271a0c040e0901021204030f0e0312030105040b0405160813082b020c1e120c1506 73
    0xb9040d692081500760151101040c0040405c2c428208002074005080e5084103683c032480203541d4481d48020410548074540200346050004100107401000302c48070700c17445500502820420f0702040b10140d000070815400c000050120b90000341c84010311074000c00565003002002d5040204000880101502e09441945045007155002484c0d0300c0480c040c90041c01615481460341c01e000400b884810600c07101030050000308000300780010058803e84203c81c0515106603078030180f103800c07849540740c4503960350380500000e07001a200701e0190040002c18034152050003101c002092030694500c44c0303000041070100041c0035a00b40391062240751441218107101e9814405101113568810000c10750402203610001255805029001291240d10081581d80d440e502c0301d9200080801000354000c1681c1c07440b4051007442903000351040c15039031001034800c0403a03040c482901400d102041400d18007900d000030301170b002c000000d06130203021480506428403c0900c0a00b0340c810041189215003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 398791007 1250 398789757 398789761
    0x3a03022107080103080d02070807060203160f0203031504090615061d0a15050705060403020f070603090b13060b030d0302041701020f07030e030a06050403180911180d05070605041706 80
    0x50b4001c203201c0c1140d4010310044d40d03e201d90010300010b4490806d0107008510000b035007104100c10781e40118402c0386510555000134011440072162401e1b490f007403100507031050000c20028080028000403102d4028000148040540e0342d40090743da080c004083c550040c00b03001c00105400600c2c0da251031101802080c0c407640f5010006001c0c180c64003d81e002d04901a902c0030b0303a01e004008070b40c83e098101003240d41c1e515182c039009543d040150300440b030034002c1840000b561030184c05a1204c1d1640114262001c1d03132081d081d09000040c200781034821545603090408691018000103503040071035540940d0f00c608080c0c1300d230b40c400d0803103401d041d060f0303c10810f43c1020113861007a40c1c8010750501e0100c1c185401d24001a140c254810005044c4901c0e0105000405400030382035110a081c03021300d40c0c0303525614404a0704039800c6480003010442c0800c4582c1500050905142109000800302810030702161201860b10303501c0c0e0000e00200d40009014040d50403640d1818204110b42d0740101254 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 398792257 1250 398791007 398791021
    0x102070c090c020304030f02030109080c0f010f02090913021f0e15040b1e0d0c030c1b020306010605070503070c060804350711030d030f0b03010e3a030221 68
    0x3030f224900c00031f8021480c05a1a400f190303000e41008030810b0b000b02034503480b008078030304060311880c900d03c504000b0341ca0b00d08200c031130407400d00070360300d0b41c681c0208044a80c1e40c0741d402401001c0c0150200701e0b4021840303240c50407048201e1a420441025541e11000800c414005014010125084d4800720010502003000700001440c00c07600c1c104000b050400c0800c004620500d00c502806600300002802c0440780c5e507500e60b059011242c65203103070b80c0342c1020f48107204104400818865000e03416420690040c4034080c0104002d000d25480f0307004691500440e922002e01c4644540c1107007000079152824041404008500d403c087c4030b180b413200b260014404c03110504081840441c4c13512078808180c040a00100c2c081d50029880301506492411400490040090801d100d074189018900b0000d214142030500c5941c00405907100100020032420030b071a40807a200e10006029040d580040d0310640794083c11210100c0940c0c0c41c056159481c241f80c50b014103003098400004045694108000f07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 398793507 1250 398792257 398792263
    0xa20060c071401050d020a030c030f0b090c0a0e0d110f0612150105070b0f010f0b040810021b0715080f0702100b010e1512011a07080307030603140102070c090c02 71
    0x21258800c01100410b140c120059609004400490000c0c40c0302040601d095501500061910101070f501004824410001e41c400c0302c4a0301c56103501300c8030725800262121030000003003203d241c46003401c030b03150600000014031650807808100c80403070352080020401e04010303040c480d010b50100d8150781498103001001c42c1c0c4120041c020880f140841c0700c0000d00d80d02079821204055081086283c1501d41134500da1580c030428072841c514045407071000500c45c4008400d90b810b45407450068000502c0c14000d410203500012600541802404899081041c0070061403004101d20030502e20a1440850098142900204010346400246081080965000c43d0f6030504100c40c2000040004000c030040325010803050525400c15036034070303040d114403051801034036140204880030001682c03610b81611035041d404041c10500e41d420b00c2000001000d410103103510400a01e03000a28035581c2c1c8a100d0034401542646d00301da540090100140308510550b1800750a030f80d907050010045904009607 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 398794757 1250 398793507 398793509
    0xf06080a08181c050105060f030309060d11090904050f01050a150312021c030e100b03030306151903140604050c0301061110091b0806040b060d050f0a20060c07 70
    0x200303412044210612903481600d03c921020520038204031120740c0d49000350080c0801e641302c0f0704c5059a0404458a841e00004170303554440c01605040c103140c5060f1044015003ca850001c50034982404410075076184c05049911a0340143d004004004c1031003640360840b6005411401900e06003002081e19001c1ca08007403040b81d6100704990741180359004101d09000c001e0400881d0240504155814154150003802c603a08916080c0c483d03c1c11000050411030f220102c00301d80640040c030024203240307402c0c00d844614014805007546420f030300481d901181210a091000403903901c0d940150304201000030b003a4810380030350f02080141044d08441c000f60005100340010008801420610300e9030500140018100d03401c400e02070071070545803c0009a040d0801a0121800c5d04030001d00e12100140445c02550016a02c0300c42d5103c0c0c401f0b02480d0042d0032801e58040c42105604aa4060104520740040f409041d030701111100e08451004502d0481e160588104c4050102c06145040410014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 398796007 1250 398794757 398794777
    0xc1501060519080a02130305070512060f011a040803042306030702070e15030105010b04030b0c0307091202060426010515010e040c14121902160b0601051b010f06080a08 74
    0x540f06030f0310340b00d4640c0a4880c2c0d10b850030280822542c0002003010014411050314001c46150358003403c441107065848004603003980c2c03442d441400402943c050114000c2444821500d01c074a815103d1000d80d2941d4441d030301c0040701d141421803d11502c14205000303031078140100da9107403640c01c200500039a0383d281c07801250400c400206c0072511246900d00c001441c45000b0f0000d018079a074459410020390410700c010707100903080c107001451b000e2103c0e0813680f00b00000d8650310034bc5030901910300908040d4890490304180100404030701444900000c074281d1a100000c103090840081c0c8c5242550006880600e0801003075082100c1a03802003665041c0100c1910000780390380392080112040f0041401c0c0013040d582c00255403007020400c404080c42030103480c42c0c0701c1d441c4103512912800c9101c0d100c03100b00404d10480900c00002d860040054012605141031400c200040402e1500401c8484003840942c3d074584150418602500482d0010203291001c0c140c60032a41d01c580705548209140c40e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 398797257 1250 398796007 398796017
    0x6030b090708280e0606010201020a090b0904020403080d0207020307080106270212250206010b0702280b0d1404020a03141c03020301061d22060b0c1501060519 70
    0x24003000300340e11880c10b0a0500c186031441150300c4040741c0018040035585401324001c100014549500500842e603c04900e56074504d4420315141d145801030300406040d40d032240c4c00300800004a07030140c02400d01003120406c016502c1c40c20741704144c0f8000b01980a800300741d041001c20041d440c0810f12601340b04400010802c1220340500c0020000d1185103040251080303501c06125444210880168290300001c05640d0b5070004064140e079241002d105482c5601c00c20825800142014a60390a4802410901700c6e24490b0060104903841c040d90400d4012441c045641da4468803240907030b220207064081130f100f0604060700491300c10b4035a0300001e4000082d01402e800603140410820000007044407a2402c5030000080003800795000b84605400245003582004002c000c41c0d0740d25100d05002444034240d94030381e13070603042e5598490300c40d0b04006a5510b000120b450000c001040e440d0f26030000780c50841c83c158440302d04154181c00132401c01c0820300c002902502a0500e26000c06198189 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 398798507 1250 398797257 398797261
    0xe0a06180b03030c0f01091a0c04060c050f06070f020d110d0c1a100510210e01090b010e0708090706050403060f0603021c050c19050d0c0f0f0f06030b090708 69
    0xc0303483c0d8450402c07043e2180c81100d00c0701c00b41000642c440c4144502c5141074903141617080040c21004038050b50503501e8640200401c0190318021a40344034400c7c401c0e07050761441a003141c5680d081003c211a1a00030410030298400420303414021000350742001c5c01c1c80c6c0c005001101020b0341d01e02035038281c0c03014003030750003021014803040490820040700c207a48102080d00c1d2400c04400c00c0c1c00707a03208030317400f4414080c20100c0e510700441e407000d18458101000c00703d0a0124800002804102014648a55980ca45070300030400030100c9a0180410048007040b6052050004012a2000b00f043c0d40d990443e1009004488c2d1100807981180e42052000c1445000c070f1300100000c00380d42d4002580302d020507045400346420480c5c042801c6000310f040e61080c01c2e80d6414841c036461401d11841c102c140f000d40a0056107000369040b040c95014140300c103034044d151a15187c3c0600b403600325200d900010102001188000d007106006026646000d228600509011584501020b84020140912000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 398799757 1250 398798507 398798509
    0x3040807050f0a15031509022506020c010f1b08010e01060518060a0e03061501050409090809031207121806120e010204060302070303061202030d0f030b04150e0a06180b 74
    0x114043c11085a031801072035107551300540101501c810300c12141c2c404910029090a4920a8950b554111200005d00c0300b06201c84880104480d0806c5034041e03404c1c022458144000d10507583e80c0c510320100000d0401600854a00304018102d10900f0840544014010340011280d0315044580c2400d00a840305150a03110403482c8078004401e0300100c002c24400c2c14070b548840c50b0b001c0140700b681034034400e449980d181481803200d0310320140855010042003000130100e030b21010b50580100460f50500801e2000039045c4480805c0d000800e02003c1108014403829003103034055014241020402c07494446400940320aa40c80b5a50a209450302110820802c81d0043c400e4016560001c6554607110000a03000750880740d81a000289002000302c0c45002203440d6840040c3c000b0300401e030003250315400700d428404554214080545840c4040c41c6521580640b0140781d5480313441c440c1440c108280303000b60707403402440b8285850030030b5070170000c0b00c0b40b808011202c0c07290b8940105001c16180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 398801007 1250 398799757 398799769
    0x203040503160905090f0d1805130b09070e010804020402070201030b030a05031b03030417070c0b040806070e090f041e170301050906120c0402130b0c1005060303040807050f 76
    0xa400240c140c019291045410b049500759074040e22403c001c10042a12034503042590360f8140a261480c50b8010940155200d001b0045614000b03001c120b454042a110720200c0da601884801920509846840000076450b141c01e080d0351001017417920030205a140c0000070850140034001a02440c0d00180840941e44242c11020250101030115440ca84507441c14030f55a40c404c4188080060285260b415540b10101c00c590003650031048100540c41c1e50764031116241d00000088564000080c4001000e000c110080e2000b0078203080901082d02d03260000ae485450241110f0b40314103080000c009004c4451801190401d40000c4421012405055115410f004902001c1c1038115085844204503514400450507a5010396090020b030301d5480c02e200e100c40110340352200c1074100501e01c114908082d800b50001940d841503011006542c0d50b0004c0d0a030b4001c0809070507a4200041150740410280540c40d00004298001c42c6401d1030540030b40e455460900901d80f05400c071120050785a61a4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 398802257 1250 398801007 398801009
    0xe060702061902250b1c060f15170f1501020316200306041203020309120c0a0203010b01051303080c0111040e07080702010c05090f04090b0a020409051b1207020304 72
    0x2c6556103480401500000e07660b01030900e40504030480560550440c04d000102070021104040301c2c403414003080014100345030450005007004e03c2c0c1c3d20000020410525a0b41100404024451400359240500028103846464441c414041520014003e00301218002d032507000b41d88155809a00d800ba1004034158454550309d038a42c4541c481400c0c003800314150034036203c051701c0d00812030351500420070b1545590f0200c402074003042d1013030700c203100f1180a40c00442c0e00010f02c0c01580d245203400d090018141c0c2058084800340c2d4002d043c0c4a003182400d100e900c03055402404d0413420699011074803a6580ca03c0e00005000c030768003250b407001e00a402d400c11010000c50b004801e882d192140003000d04000112141e0000450002c04103600d580180314a007c100c0599070313444d00d48200c06003403000740880703a80910f41299944800d0b501007014054001d0003102c6550001d40da80345800550000d0b2103010b8582d641003406945000c08104000c0d0481d441003480c008000ba20766a0342a042c0d046001d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 398803507 1250 398802257 398802277
    0x1f12030f11010c05210103030503070c050f0607050301031505041e08040e040609300c0f150506240d0518070f030201030c0f020c130e0f0a03030e0604030e06070206 72
    0x28810143d29090300075001e004010f8850300c121034044540301c401031499000f88006008100d04001040b03249200b6003040c079002e8040c0040341c8a00e5010001c185c0740240c11600c840005001000500400c8030703800340c0702c42d0b040c602e40050002d41400e0300c4000d55600040102100751940300501d40400c82c03004141c5009009400055055140c207041c41805400074890071204001b411050900c1c40301140d95495a490700c0341c0280300c0b41014804143d03007911011000b5030702c0d007804400d03101c00220032207541a09100046008501030511106000500c100c0c48908004030b50710300081c5d4041d43c424801c0c0c4400e0f108003070000c505600e9001c4500c14100310600c0c440c0940c00b8400005c1980c07292000002e089910031383c3e040105c02d038461000c40c1c5021a0302d14060060f08220a0400e0700d06e009941449100aa5640080d140f0f175285241c501c2c00892050b501082d40181040c40241501071007526414041c1c100030380807038500744da001040ca410000700d0511641010400109546480c015603040240b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 398804757 1250 398803507 398803511
    0xf130510020913150905191e0c2a0606080f211e0d1b020c0a09050c090906011e2102130b03190509030909100501140c010906060b031f12030f1101 64
    0xe1341c0b81000c8ea0200e40c02d09514030950400c400301000b1407041001c10503010281d5004e082c42d1002d1005d1165415100805030303151502c1d1000805d14050030b10284402034070100052080200d000c90003010012404000c10b40150180b0818540c1d01c0492402104100500249039440100f400b81c00d008280f85445a0b40000507000312032082500001c808846080458203500d0385a912010034040da44100c0b072058081800b400180c0b1503061080489070040340504041a0b0040d0b02440b8014a11000480000161995516800d42c2c240c9200d0a860f041c071402003907140c901481440d0301d034000f05105551001000000290144081003084141c02d000850180458109094156625000400314a22407007201010809050009640008503181a120a18841d449a02c545c070140c01000d42d410195482c0c50041300000c0c00c51280b1009130003102601c2e5100d040584850100303005413040041488540c4d8003d0181c0b4803200c0303070301c03107200d615140c201c20180740322034111000507146a03800c80d258 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 398806007 1250 398804757 398804771
    0x241e0c060e06090d090e061e04110d0b1c0b01030f0c03051203060306250f0507020a15080a060e0c03040204020d1d0c0402120f13051002091315090519 66
    0x102003010402c4c0015583d072880d00b40e13191103c0c15106a001da600603403004018404040ca44500c041c40d200002c00244000f640c500645148082680041c130381004c601d507a0782c00203126141c08902110010403010720310401040395900c800c800340c0180400b8042c810580034810400281c0c02c0c1d41c60295501c41c00782c40381540058160a8142c00641e001e0340b290180c600001c4a240c0040c0441100c9030b2215050014000c074603000b40da40300340700ca0030001000003c01c071610241c1c0791202c0300d400038040e4a41c40518000e007204d000309690409801008071b10704107041080240780032449940c1241c8042038080d41c81c1c491f440050001c2c81111444040a402c1c00d02c000012603200d5804802d00980e5000d0311183c614100c00c000c12481005c2c0c1a59058401e8804215120340d030440d5103030301445407005210180100d40350585041d417000a04190280c0000d030281143c240241d01c01c002912101e000d000110301c12a02d04101d41850040714140c954820018002c0c1aa10a0042074000500c90400c0300f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 398807257 1250 398806007 398806021
    0x190605070305060603070c03030b3001061212200a0c050a09061d0606040b130303030f1e0b010e1e03010606050a08010605130b04241e0c060e06 63
    0x64501114100c02080c50b00c800646a4101007048900c2148181e40310001500c0300e0354240c0003402c4482e2190f8006c407850448800e050074400c0c441c10148a0302007141616800484441d0030340d075094004110044d04406400001012038074850500e002c03605090f151000c070010042c40108003440300040320b05c00d42840c0014041380d0b555850644078242e41c803410540d102c1c2c011001f41d403510702c1800c1c500c0e00c01c0300c0050700b01d80c0c80c80c0200b6084400245054501581d4090000c5070340c202843c900248507100324200300301030b0076101c1e0f403008004206081c000361103014600ea40000e070f4204564146a262400384c52030f61b110782c070346132800d0800411b10b0440f20100401d10b0705c0803068900040c0258a1300101007011400303081038403400a0680c2d100343c0c0ca41c5c20000202e0b1550040541c40781072031600080070908030280c5000d04041c00350a44800d11040b510900640704107500740d402c6042c4041c0d400f00c002002207111240c400503050303051840180c100e42c41c0000c02881b0403403c1008a020740010310103e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 398808507 1250 398807257 398807261
    0x210051b0301120311060c070f021804050708070f05010f080601030f051e1f03080c010f0218180702190212030c3301060309060b0301091511030609040b06031906 71
    0x7180a9078580c520356070100c00c40c5e03941d0071090322482e000da8000e200c101e0003d038900d802c40441c544042e06424a8540a1a42050100083c2d40444013074000b0b401c240706240d002c00607407000701402c00d50040d00a107810000b800015203a0300403010400144005803c1c2e0b40070fa00203105d0f000455030308002c6450b00c0d80403802c116100410240354054000040340c00b0510700e250031102d90303001c4410003805d2455651108040d600c281031041c400c1d52030301c034461440c25a0f072002c1c2200005d0744541000b0001c0c600b0801240c0a003048503074259041c03000a10103010750000740c2d9459a58441d1004281a0007800001c20b420241e02200310f05100000e00d01d5040c0201113181d01005001079030300d04a4840b820041400c10300c2d076541540c1281c10300001041043d20075000240028000d80c3e00050031007108000c40e09540b44d400040d50385114814451460b25810b209210105112403100703801c41c00c0c8003002900209011700080c00035010302002c00e4841d501032020340707107003c00c03509043c000302510300d42940 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 398809757 1250 398808507 398808539
    0x613030312060603060b04050123040f060e0d052107170904050921030a240807080d05070f0825020310020304150e011107030c0b06100210051b0301 65
    0x1c005402c00c180042c841d402070040405a450303030303800c4034101414800119881d4442184a25441c0780c013950841804a07a03400900180216840070031456041190190400c100101c0b0325004000d01c0031a00082900840c0242c641c3c62481c03c011590055804100c030103000300c40b000303010300306440300e104844400380c2c3c0100241d8500356424082075803500303020b40c1c0303038030246180284c80605d0307000855000049800940d80a900802d001940d080045411031440c0c101c112881881440b00d0410320a408003002200020100f00c0c0082c10841004071009000c1e002c0c0400007080300d2118083c10f0708203c000000d880d100550490701c003c400c00801c1711030158503503101041e4041d0050b002000c1e40329802d8005c40348126009202c460301e402c1044e41880050100b0415030003d950394412a00070401d0490082c0005400780d03440d80a0440300b824407100d000b102400103445610303407541e0507030f4640d00825140254100002d00040360740d1211034130741d0321100c00c1202c0030b28407000100108191000c1484a1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 398811007 1250 398809757 398809787
    0xa200111090a050409080a03090602070807060507080901060f0506090d051501030311240a090b0702010c080a05010e1602010f05070c050d0e150d0612030320030c1806130303 76
    0x30210b640c0d800600003280c1c0c4410f0050502c2d03904002e2220214048e41141d03007a01e109001c0103140c1501502e4030344481c0c00c480000c842c05901c03482800520355000031070980012811000700b0410b8a40f850300d00c00f040ba90701c2086e000b02e03070104990015946d400099500c2c59000000d54800c50500c1e10042c3e5100e000340800c8008c682c0100c2101d40d25880041c3d0920a48000e190240549c00389008980c1d0350034000300700400d03141e1542d4480c00014030410946014401540011070700300d07480c00b0007524040b801003d05a801b46001c004000841d9151481c642000311642d03003400c0300c000c502d001c9016000800d1401010f500342014070011030380c8000f9405900d4060000d03580c031030100000031511443c0c00001e00e0350000002d04e01020030100c1800924000116610000d0702665481d0420b4140c00340160507804680d4a240001203904c800e891503415403010581c161030351820086421481c01081404401515011080703c02c54545100f00e400412b00708402e640308a50300e20300201107008180c420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 398812257 1250 398811007 398811019
    0x31103070602030a0f050c0a050a060218090402030606010e0d240c080f06190504060b03010e07050307020a120e090a200a1e0504050d0501150e0603030a20011109 71
    0x507429202009540d0344402c0c5569510924808503c100c1b85500301114440440c0604541403002482c10000c0442c0c2c50311aa40140c3c849442869595070880719411943c051115a010440107a4000c13039200d03400381003420441403401010011400d044000c1b04010500783c942c14075050304140010000c406016800e0b01800305a00b5800200c501c2c010940780400d140ca641c2d00401ca091a00d0203400340ca4070040c009174200036581d40000b9094411ba640306280021b0000018011f83c40c0c500e20055110b00f190501c6031841c01c103040000d50b20140450050240c1c1042c0c00d4580c0c0d100d1041807120b282600080000007203040c50740f8020000c116030410800b01b825a444695012a007880c180c420030865a105c1051030080b0310500850740e841280031070104602000045010380d1140b03401c490003801180006540c0b041039049281c10403081c1c000d0380c40e207001103080040c6660000215a0850864a0110307441d45e0164900b0034042103803548080203500b050b015081c1d203001d002c05480100012104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 398813507 1250 398812257 398812259
    0x70501141503150c130f030203010b0108190e0c09010305030c010c090602070314011d03071509020604150207180c1b0503030c1309090803160e03030405220603110307 73
    0x1005800452185020b50903410403041d074410041540c001a50054040c0300c000e141281c6019000b121a006402603d5140000d003c1401903081c02d2140e214000c1007828649817506103150302c0944508513500440c0c6098440c84203d4107010280115109048050911501943c517490150b48a4004880000c0380c1e40c42c0250034401c1d04e101d4000320b81202d007160003030100c083c19921a078032061844203540c8039030342d25001103401c0206091352040c080e03560350001e5602c4540500d0108490040350503443c50f9982029441c1c40543d884900b118100c50700441043e5000798955400d81c142180369200400c01e904415481e60120603d40000307000000a0340c0341480740c2491900011780034070582c005001a40700344000758401c3d80c2c810081c41e00c81280340145480981d184400c505880205038104c606040100501c450b40766034894821418070607003041c0074040383c0e600200341d0740e00441c41481d200d4648082080348030006481d204810b0500035405108890700c1e030620000c000e0b4920404c0e40039102d4140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 398814757 1250 398813507 398813521
    0x9180a0f06180c05040c0e120d110c060307050903010b04090b18030f0336010c0f0f0f0e150712090605191d0d050c010e06041208030c0405030307050114 67
    0x1c40c10032a5010f042024141d0402050100501e145100b000500c006412002e060341c0c1c2c0d000e030003100380398280e00411400102e60b400070803aa12803c00802d041e442401105c0130340c0e403400190b0f54045060701d005074496504c178000130301601c07030f101a20b81c00c18907007001c0e0800d00c400340c10a248034040e49004d203003181041c11005035807440b4114681c0e408407820f00101d445010107a42441c21000e005085d0310401c030094034141071458002d02d07084800d030341d50b02842400035040705110820410905145090400e0903c02900d0751841e030050404118042076060500d903541d2201810341134040c0f20310f0740c90318002e01c0c1ca1069101400510350200d040c0100004a5a1045c003c0301c44c0c01c04680300c54181e03102c0d8070f40b09442c1e1500d0b00341d104144281074103202c0c3c0c154460f81e201b015581c0c011402031500c1003211001401e210078240f0b4036400303280c04120601213200d2494101641c03642c07100040c0e40e00e5469060b009410b0003039400070f50381030000103003030028010150000c00c106d40c4481c00c4c070590380d140e1103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 398816007 1250 398814757 398814791
    0x5071d010e030c060d060f0b0307090f0b0714010e0f07300602090607080d0f060b09031b0d050706080109060b031605070201030e0601080f060606070503040509180a0f06 74
    0xc030140e6055009814035202400c00078003500d1500001031740031403000d4880b4180040754030250800b000e0035030040100b20a003540b0030035441c01000c0003170307001910724100210309102d0311918134040e1100c494840c0b0182142d00035804400c0c44024202030302c500403503181025841d8420740c40b03400316540c3c1c00c0860319401002e0b002400c0d803a60a004609460161030740e2800040d4021100f0070f94031031800d100310000304502070024101e2000c04400010f840c0203203e80d4908961481d007004a042005020340307420307600c002600590724440d0504104400743c1070400501c0808540350300500c2c80c054401c0004400c2e03000801d290507070b06007a81c00e21000740c03180c00112150000315044906914000c0541c141d460058005002440c010701d00498409484580c81e0324160081e8080406640500b050785100d41c42844440d8100c003003100d02514010342515401d54901032806114232a4450760f0106d084450048105040300f140700043e00c2910005041c10304030359010841c25119203040080580b2902518 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 398817257 1250 398816007 398816027
    0x30609010605100c03090e1504050a09080f1e1b0d030504020a05040c030f090c140306040b0a180f0c0e150108010e060a0512030301140319030503041505071d01 70
    0x18001c0016495806012504940c84c89020b90a0003603180d00483c1c40c0415400d4180f041004858409a2982c40070610049070f00080000307240901d42004800060010340031a00c85055104406440700001300100b141c5d03521840c0385a5081000003104a40c207010a040c0c070100c41c010304240c401a120503401034081d04c00c11500258019040a0300740102d1601b94808030080c115840e000982025042d1254100c40f559001511a28070021081144400c58421880c84541c264040c2400b41443d1395545403986014161400007174660f22401200505e260415201c1742e08209062320200103401c1031400f213039903401042c84081c002c0b400074000d060401d1440404550694802c1c03401c3c1c2c684880ea040011002d041036901200010000500b82e89003d140401e82c548c07040650340c0d035403401e0040139142203002c041900981100d01c0541d1250110400c0845964040c1401c41c1c2c1c0b42d949103002004c034000b01c001800d8075171422060001290384481154956a20b4042e00d110405106006403245001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 398818507 1250 398817257 398817259
    0x706020601050d081c09050d020304050f04090f0203030f0a08010b040503030703082a090a05040501032d082802070807120501110304030203180405040809040b130c0509030609010605 80
    0x200e4001080346080100c070f0302c1003007401120040d05282510001d0035008001d2100c5c0b001706901d840f240000d000f0180318000042c000c80c0001e41c80c2c40d00e03004c0821109906400e03060300c81c0342c0d60250039060040040054400303e900500381d0b035651a040703c4658040d04503c07501800103d003600041034043c0b28004440036104020300941c105005030f50201c8103100c1c02070560b000300303005034803080b200c0850440140140b40f401c00400d44980300c0070103010134201c0d01d5004a00c0380f4148001000842e0119523244d007066101307141c401410a002040c00c01c803d03401c4400034820385000440c040604243c1020090b0949082401041845c52140480e0303100001e00407000300341c0202408101c01140400c0105c8101e12039800851104141c0c1100c48080d0004c540c15400b50304001116160a4002c1d201040e07101400c032810405410552074805540c0500002180107554604a0344056135803409030254014a046040c020000049001440c0390000b084990091084402240c00808180102410b9501c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 398819757 1250 398818507 398818513
    0x409051006050906070201020703140f0610050d140a020a090c0e040902010f1b06020d0204050108130c15031506030e0c091b031b030a0c0f05070b0609100f030605060103050108070602 80
    0x2034150200f01c0217900c0124220306622549200000180403e0083c0603404117507009882c811030414130040c00e00c42d00412a03040810410400e00c2140d0718900f6005482c1d4110320410500590443e10700e203000380c240006035007c044850001171146164022034640500c80d078508910421040a1005a0300350050090100d0301610003101210311416002c030060303440e040c18403444c041d15100c1c41c080707910000c40d8076161500003c1c24451541c021880301c2e000720102114070f98100709520fa5808451950084d8201c0e008482683d9281500c290410780c0f46092442078018480d0303951030060b005108102240d01c1c103001d8081100b00768076001d0b8072248a0780342c004102a040000b941c0070b611070fa00052000300c0100158291202540c02c0f5006540b00d07070b41c82800010761680c4200060002d0500c101d140341000002c20a13280040d000c4504260062010b0b5480c446a071548080494100000e40004c4003680b8802400001e0240c81e400460207903100703032010041640c03038941d0f4686400e01d0b03003c0c03080035034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 398821007 1250 398819757 398819767
    0x2802071e200402040e0a0f050718090b040204081605040507051e1e04030311061b0a0f02010216060501030614070815030c0409050c0102071401230705070b040905100605 74
    0x3015250700700c081440062006152a403078100750202100300307446d00c0e500a603941801c1c40080e8840e01c5082d400c040d131400c2044440220302e00758100c00e1400e0181c43e0480751a810a200303291200c4d01958050103182040c0c584c400b00d10705001e100c1604078400c6074402c0d411b240205d5075090040086a03488403808000300b00c111030b84452850654001308024091003100d01403003c880740c040005e800510310a694084901d48620328640c50840007070100f0826100740189200f1020801040314034485180c24181484009894164024000d000425050a001d241c80b40104111a37001034180c901ca80006c0001c145c1b07030f0b8100c01034103a0403600c5c10f0108030984041056412410560710503240c00400b1145801d01440105c1d0503503084c504120f80c1071380400030b40c40496070140300d0b42014000e0b4058190314100c6c00e01c002091801e41044840d4101e458840c04d40d028003031541203804a640100458202c603a55128290303482c1c2c443c3c820f200c5180d161401195901d45840b400d001240d060baa00c070340c102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 398822257 1250 398821007 398821043
    0x10f03030819060803071514060405180d02033106120207060908030612010e190305070503040b03061305040818130606030c0e0f13052802071e 63
    0x5120098039606042c405004998100c5403203003d00b6002c0c10f03180c0080c6840f981d1519000b002d0f102d1440d1440252030812540b0001a1600304455a10540884001c0f8058507000312244801404038016107031406100800e6003030980000040045421046a07100a103134080e0300d844808403404506c0d600007025100c00c0100c5482a2001c080426840f000140360003003035a41d480440e07000e1181280c0900c408004c21030039140c0720b00c044100c20394140003405441c01c900741c4036488206000e09041c20048400411060511030f02c03d440e131059218003202d076265100c20310b14200e44c20403200d00e4800d420042c410701900c4058042c45000395803000780141440c80b01809408002c3c3d090300c81d036030041103205103003003078400c0c500800340204450b450001e143098215200810500c0540c0c0082d01030140403124500c1502c1c0c89003101c10950083d900098203442e1191320704101006d002c912000041d144081c82906140c1d0380c0103042c1d070ba10407144084050506080c00c100c0145803038000e0203401040225640f9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 398823507 1250 398822257 398822267
    0x1206040f080a0216060306030b01090525110601030b0105030606061201140f0409060b040b040b0307050f1c0813060f0e0d240b03060703020c0325020a090f0c030203010f0303 76
    0x710720b46801074a24110702114280d01a08150b4030110000e620f0b034600b00240703da809000c1e030150085000500c20b030302c1c102e083d4828502c050002d010a2810048071951a030b8030400c4081c040f50b102100fa40c2c21540e41e03050001c1c1c08074082c000e1520a0041c000401d00914042c01168140001102c4600190786045807181e0500c040c1402e01d60003c5400c40b1503e01541c40d8800c0c16011441003400082c0b625903007061000312000310404500070742c9048024181e656000424904a400032104000c4d0b80a00001164a034200c403c800e5440100182e812004c1010719805490b1038000c031040002c403036030340c2c2d48115950307116841404045128120f001d905030030035843d809922401403c03848566500e616107411140b48000b00c069180d5501c94081c54a85018401650001d801d40b80542c20034020066450700c034858004400341c0030400e1f0071485950190078000c0c440f081d17001060b1038540c41d44ca407044006000c0307802c0c070350072110314042c0c506040c10301034425139060310407200380400345ea411070380c003602c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 398824757 1250 398823507 398823517
    0xf08011506020d0c111f030e0c01110a0b0a06080d0c05010b031504120c2003011a0604050909100507050304060b0405072007080304061e0203210402010c150b1206040f08 74
    0x14225200c5181044100d1100300c180f85080c1c00387d94000b60019072146214104117003a6032a40c100980d511007001d100c800040c65904607a0041c1590b0b1a980341c050031840149150f60003103805001c3c40130300020f0b05800400141c030042c050fa0003482507400354001c143d10341c4559120f020b040d060b5100801c0100d0a0003540104c42045400c100d20820103989a0a041000050038451000025480d04070182000c1c001c960080308482e08402640c1d40e010002012800b890013040d016082540004416a05c200148842c0e81e103242007c0085040480008100e07078401c5400703884490034100d83d0811820701d4441d1501c00d502319680c0c0316850481104d00c4072400b810b64101d0f0705600c540000410660f106000510042c403c0e030321046000c40c040191380c50b0000d04080c064040d50028000b07001030300010011036075031000e0101c01415950300c900c0140c0b600d5149000292801d1550910501d0104881d40f1180c00c40c00200e504100340241d01107115543c4a04541c0240844d489440f90000a03050f200585 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 398826007 1250 398824757 398824759
    0x6020304061d1c17070e1306081006270f15080709140c0d02070f0803180601050307080307061a0d050307030909020301060f0e01090f08011506020d0c11 67
    0x40b510300b82c402c204076080051490219076076000141c0030700c07030007224044601c3d0b503240604011a0280c02c2400c100e46000000b4070380340c14400504241107040da5402450310300e89062490410299484200710b41c3c2e05c8043c10710178410a844c141c004074021076080c0e801c2c94200307002007427500721441c1061528041c010540f880d1840316100c80c0c45660751145400d00001402da0b1100400c00c16103840c2002d030039540361001b0445074504030340034000811200740445050708580940503945039403500d0311004038075003201d010703142020101c1405049034660001c00c112182000440e5580d0762120f04140e01e44585114001c040e520400c41100011b0740f90b000145010201034050400801c2c80300891044100381c00b04aa05806c00921103040640142078080941580582141558140f0402400010000c0a10418446820b8040c220b580c8a1a40b00014210102e1411080c5a480085901a00718003c100f07541101c00000802c5c21840003a00c402502004d540c1c000c4400420b4440711800c0c105140c5503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 398827257 1250 398826007 398826011
    0x90e010b121303050d0920060a0c0314130e060103141608310b0a0606080103151e0204050405160e060307020a291608010611031b060603070e10030602030406 69
    0x5030001c40c1512540c600c06000da20b0001c001d0b00070147d6500c04646015103a8810001803241c21003850340640000c1c4070550604250b4031070f141d001910007550007141002d09020200d800c022414424000300140101000c1e2428000450b050780c3c1d01c2e000715021105240d0701c941141d00f40742d1591003110519000039840406241018400d10781060403000714103200b142d4040c00309103400b048604924280c3c1b25a5000307042002a0400c0f1005180c01d038180300150a0400e20645101d0160703041e48a481020150320300002290000220708001c0d412621031a07200350320f400c001848040700f8400c800c2994001c0d5659070710500341c103001c03c10103400c0170f0401340851003090f00c1403000a4129402410710f020240480c103070700c940308620300c84c2500f00514401c28010892000b0040c0741c1c00090990540b00e0324244210315000340c203856403540c0152000c5019240c16070802810012001c1281405100c3c280c094440702c1e900c0d114040e0414100740d8824408403152103080001c10744070380c06150014411000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 398828507 1250 398827257 398827267
    0x20d0c0804090608030a0908030405130507050c0f160812090d0c09050408090f0628110303010e0901050610020307020603072106050306010527060a0b0406090e010b12130305 76
    0x2d030221031030754200154a6100240f6990015080a4148000d0107501c00a41c901030501c404260841f19900903a0b040d180c44801003980c060203001a14038055204040b03440c001c0d02d0b000e140b0350b40c010451041c41c545070701c0480885e488a000c180d0445412001003d03a103880384510074090366120710f41084d07521000c000d80128139200c00e40100c60081d070040c2c0c070140e162038040b802c1201c41c0c10701c03e80a07032045604204045051200c5168030220b4018208001c4500c48503072010b40e00003100404450003030200100100d014400402d003603002d00b00c1c050080103640c0c2c030842403000c060189240a00903900030701c0103800500d482c01c02503900c81914600301404a09940040d455405840c0304041c01d10303210902442036040401106004080c00c6581800711081c105480206581c56510741520700c400d0300c00210070b070f01c544005800038669200c07096074441d03450b040106103d115000b160185402100002001d251030000d4441181107408101072544910482c110f003100d50030b5007241481800d01c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 398829757 1250 398828507 398828519
    0x80a02010c0e0301060807032901090f06050402030403020c010c2102030d050901060305070e041112010e0c04110d1109060304080406030606050403230109120c15050411150f030a1b0c03020d0c0804 86
    0x51027034004c202c8443c1c00b00c0c18000222081090380c49603040203004500c14030420002c66030000c0c0d11443c5005c2800c103142c40503001d08052040070354a10003c0040700c040c0c01d4500c0034035400001061100340351807040025841c0c0544850070f840d16444090190761010006100e40710b41440d034690042d11800840c91842890342c040340308002e482c8400302059540c2c400a5512120078461840c00c100221001c210320340f16181c3c06203d07406070b44108040c0c147c0d203400c01d059100e6040101c40c814440105082d850f49418a4801066442401480002800c0040000e40c460064050f501580da004038000c1a020f0048013207507004a900120b84025901c07803002c140841d071110400500c03030045643e001c2e004000790512544c2c6204030300103e082c141c5004104004205028810b8440400c11650181100040c2d441c85a450060760b80c009103005002045c460791484561000d00950203504644051aa4103041a141f00c0e8400c2c60180158000c0210b003541584110140e903051845104035a003000e032a15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 398831007 1250 398829757 398829833
    0x3030f12090b0108060702390406030c0305190b07030b0d0f05101508030d2409020904050601020610030b09070929190308090d080a02010c0e030106080703 68
    0x19010348408030b00c040180068041441056071003210380c0000c1104074081012860610000c02d0100140283e0303001e1084400002600c40204aa000304284111912818603002c2040144811070340ca20520034015032440270f000032500640c1d0001d2920015680c0d100059020b40003680d1810b5000038213003e40000944064000c1034043d00400003040b842400600b288115040c500d00d00710b00400042c42000302000c00801c503282034110031408107012911782c240441480e09200e42c0c10151050b00d001045003801e80c3c0c0900903051381124140800d403600401a0784803402645c4189072421450401d00200b20101c040507003094080302284c83c800d9840461600b140d141d0035402d501d40406204001d41544000990f0042180c11100f1960724034440b00c000034621301c148130081c0f060202264401950381c50003500000e0640154080c0c1d911109500c00034000c007540c0b07690300007060442100036540d04052141100b40c4036160003e204050568070780c01d00d014070410034400781e4400900d9680c4100c503c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 398832257 1250 398831007 398831021
    0x120d0605061218010605031009050708030f070b07050306061210081207050601080303091018020a14010201050c0306030d080406020f070b09061f090513050303101a0405060403030f12 80
    0x3042c41603820b1420701200744920005049210f681040c0050040c2c0c3c1d004200000404605a000940d0010b589803040c14118160301142032808046140c641d00040c40004085107480f03a060003105a40b80c080644481c002912075982080c0144150054017100004044c0c01002c690407403880350342d071002c6845ca880401c62010300b0801003c6102e00402c50100107080c05810101c003d5030652404d03164044c1e403102074034900407010b926503404888101d000c405e144a11900682100d40151311005d83c45038250030291501c0c0150f01e4100040c500c0f44952041c1ca02960005000c1e100713200c42c0390301c1203502560103813080d0350340740d0f007081b41c4100d400000c001404c0d0b01e8460042c590840c505003011a08201008060a0344c501c10612480302e0301c480c0c4da2180081c0c6841c00703000641510b0381082c0455000407040d00420a110010501140c03044c2c2c03002c00b2040707a224212820f2650070421000c0c81c81c0c00b0710300c50a908a2011f00003800040d00680000c22412064a40b001c8c0e6191003032001030070340c0c90f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 398833507 1250 398832257 398832277
    0x103120201060605031609230a0f05031504030e10080405060709051c0303022101080709090b0f1f080102090f04060308040b160507030b06040c0c0c05060309120c0d02070512120d060506 81
    0x20818032310394182003130b100103801040c41c0641c0c0f04a172840c0c5008292105000c0340e1030041b0711400800541054090800b0b101d50f010050401e2401151402025010380c0f001d0341e090701d280c0b00f81e00029800174800e601c142c09981d00500380741c101c0c0e8601403244914806066003101850f400b44461001100c01113404140d940c440701d103200302540750407901414014a6000812002d045c0715204003c15040c1c41400d4000e04070840c0d43d40240d440306126543c600102c0ca000c06800f103c100d000607013000540190546a030116203c22010021408101c2128842d220050100a041c0004c10124a0b20000f03011041c9442d00b582a90040a40d900350070101541c00403546840c0b11020b0220601740780c45100000326290130070011000c42c58075481205556441410f202d203000000040041d68103019070ba64865a020b4070945900c0d940640e261201c10508400005204110380024145040b5500780044800c400c054684980d03404c41c081015403001c4140d0f488251140000500f03619a04014041c0e514 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 398834757 1250 398833507 398833559
    0x90c12040f06050702061e0402010509120c0a0506040807170a020d1208150f0d060209120a11061c0b0d21180503030d051306060e0103120201060605031609 68
    0x410380b40060031214041c0c010000c5510000400a9081101a40c585241c84080300030041c0e07501d41c40102e90a04c42e00743c1c0726811540c00f10b50f00060758400182c61580c4030007102c41c0109541c4030300034003005015600c42e07410590b001d0b82007004003190081390b04480c1245442a20780d902c002e1340220340501c1c6801821504100f141602c0d150680d8044243c1d1340242882d4010303101d807040500002c2d00b010140044501c150440d070341210410026a04883c1701c144040c154400c012821a62691030f908924000c0d140f140c4096406d402520f000c00440d28071251285c440c02c802401300b1400e10042a402c0c12583e041051815450003241d182c190600710200d900c041c5840445440c01c0060540010303100703031010780406503000d00840d174000c000e68400203418000040c456544d01291f8a458089580160000d4500400410142404c01ca0a81a2070040c0741d2031440ec07590384822400c2710440c0c843c038030001d041072002ca17600d41d0850100c600028040d01d8030740201603c50303440844103000072455001d220 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 398836007 1250 398834757 398834783
    0x50d08010f060915030f200901120e031611031204080c01031407120902040c030209120c0901031e0507181109060f07080f0c2d0c090c1204 61
    0x554400c1e4240c02400c0a03180612900d0310741090b80c8901401040b224091644400c8043d4111480303500a42010500481071015220050701140c1c0941c8035444050000f03900d4001c020394046507005000640c4504001107180c95040e19200c05c0c640a412411035207544d0300c094158403030717408003c11280d002144001ca642e580c178003400d640c50320310803e8803181407604140c032403540b11a8803070299900c00b00605000e1046900000c2ca17100401600c08001c0d03215141200001c0f90305d074140c0c00785c82c488100799003040701110554010340d034660f0406d415603480101c030130040c80010028444661651205004c59031110b0f100c0e0f131058100720a9801008185009041025801c003807802002103001650b5011031509001e00c010914920907107080004a03440040d402c01005009421030f6044451509107940b19030501c4a01c80d180d1034888207190980070a0b11706c06140030400300c3e01e503140d9003104008201000c1c003981402041c2c5001001208905403d0008000100c13040c42e4007446148510f45c140100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 398837257 1250 398836007 398836019
    0x31401050610021c0e0d08040909021008130213020c1e06070f12151805011e120b090c0a0b070b010e0105090103200d061a060f09040e0703050d0801 65
    0x10b072807031010501154000314031403110348002c0c009005111800e1030301501e11000c6a01050620a40d842d000342169070000c0c000407144510b50004400764801c44e81c242400103540822110b40c001500d64500e03a20b00030b40820700600c0c008210a00364804030402505041103d50181d05000e080000c0d100c041e0f904c04900f03404428180015548020b203814150107000078000000c22400141d40b5003004981d450300220310b03038459000444010034540d00c00d42e2182d030300440035a018040a20940050010005030b2004403801d00003000e00341c5420107004c003a0a81a511410402d010240c0b41d03150b00c3c060f01c03219004944512203c44040c041031103d155540c3e0a42c50807821090050b4010418640c4400061050703544030308003281140d070008250001c004a00301c1ca004079141e01e09860b40e2002c965079020040154a4020071903402595009108882400c801d111aa20032007042c0444284100102c921600e05580b10000420043c421039035480c4d2682c0d1854500a2010107400116642070010000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 398838507 1250 398837257 398837269
    0xb010207030b1f0603020f0901030e070302271012020918070b21060d0206071a07030e010b03010501052409100804120201090b04120e130204050f0102150f040203070314010506 77
    0x2d140131301e1704600c1c0001c5a5507480c0180100c028807030401d40c030b130480400501820004140a0341d0002c0804005400f2025102c0d10040705038000c41c4003001d120000f5400d001c111400b20101c41d0300c081c10050841c040d1b03003004050500100b111480d1070021130480303584042000080050030303440380240e03507c41c540400300801c0031211810849586909007000a02c3d180c42da00503060303d60584200740c40320901c0ca0a481071103690584071004400140c00c1000076941a0000001f201411008100c8421401c0c03d05099403800d020381600543c102800c29928408004800d4200c60b915031041d007441170310000546128101c03034040c8006107100041c0010301032245401d0308000340b140001c2040e40c3d000d50341c286400c10028005003010105c04038145c612801504600d00482c0020b1034101550b00d5050408001d40103400380c00c1c012004045014095400080d60034854800c0294446e030aa0764401310094201c4010000c903014018054000001031ba100c1024441c980c000c0004610307407a00e4824406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 398839757 1250 398838507 398838509
    0x16090f020301050604090c1202120f0105010503070807051c02130620100b0a2411010b030601050d0c050904060501051c0f02091b21010603020309030d0b010207030b1f 73
    0x20144100010020340e560341e0708407402ca502000020843c0b44001c402500c0140c8070102c400e0071180000f5040900d200800350481c070411038a807110b59241d899400440e000e002c2241d0b040d01007003892003c40d06c3c05020350301400300c00000d540540c5951042c080070206036040314803d195100041c20302400780d00d800c040711000003488200054015044140e15554071070425101c09641981c40c6980020740d12010010006000c0d100f280c1c08040507e032000100e21691009110000b03545081043d01032031040c02080c240910080080c1190b90818007081060781c0b18100031100d000e604030000800e42c0350700011501c50390240b400001c0035031420b802c2c404881c0d43c030410b02d000502ca8408090010344000401e01c0101d4041e43c02000700c0c0e0703d034014422084402200089080c4011526443c0c26014080003480d80c11080008440399a8035401076007a0b0000380d80b6401c80360001d104416176000190b02203040f1150502c1102c00460382c3c0d8950b03c00ca0001a1101d10342c494004014900302021408048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 398841007 1250 398839757 398839781
    0xd02130c12110a05030103030e06040302040221091c050c010212070804030e010305040206030c0309070504061e0e06180403140703030f1b050912010603050f0a030f0e060403060c0507051609 83
    0x3d2070711401c01c034014228441400003c06210b10b1542c0e110058603050203840280d07074064002c5541c1e4418540d0040016221040361907030a0128000903411000030031400d2a012041005000b4204401c8065840b50080700521615640c28072400c3c942c218410885401407202e034a6114050400d81002012801c2caa4070b12414181085c1c140300c0141c5503d400c403a84450079008098480c3c444c481800d060101d580d01150b03100e4142040414008228401c030700360032464100e12050b06aa40d441c484124208a074410360021241802c154079424854003254001c0c401d1601640c0341c40781c8180e2120b00d400c4000181c002075990f00c0100d01d030301c40fa48030700205640070107d02041d601d00c101009040344207804103a0b014009140741d41d01e40b10070940002000d1a440350940c0c201c94140c1d2086941c8030f0540030103900048002c8035000c0290300803040300c009464080c200b03615060558403400e02504171114a8000c2020400ca02c10114030280118040d941030245100642443c141c408400d41e0040c0c6501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 398842257 1250 398841007 398841041
    0xa1410020a0504211406060a05040902031518010504032f0a20040504081305060307020607031a060304050703030e0625020307180e010c0c050303060d02130c12 70
    0x11007000da00300081d40d0484405030300c02444900c2115445841d00c9000344001d042804c0d01c00c019000207004981c8510694040c0c4401c82c10300c0d035034010442511411040a9099041680080c040c10140c4041c1c0d5400540001d02401152211031402d0031a2021501540080d031691500d1480b5135200040401191b007000c2c0c08041c1c1040f000341070340ca4042c411002462284c03c07a12007003504102403105662190010420010b5240a0070301c0503107980015440607d11341e100201117824175252003582d00034034007540108407d654404c4264000c0c50315030b003650508001e03110114800d039a84001944500e03c1400070b031410b0740c51803901820004000d201144a500140519804155100c02c2003204500490200010000c2400401d00f060903c0d00f040e18070f840c00e01401540807116802508001d04c00d040200042105010200c40302e00368113400401c590010000319000e403401c41c03810030419000608501105a0001b8000102c42c4191600c00c0401d134000546040340c80300340b043c61601000e08400d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 398843507 1250 398842257 398842267
    0x6061507020913060f02040e06130606091e030204020c0d03060e0c09010507110a081509010c0e0d0201030b061605120f0318070513090203010b010c020a0b070201030e0a141002 77
    0x1c0e0502c1c00050030010070102c101c803910144a4180c01c040c8050020480c215034558a41010083c1440d08641007805481c20794074084400095120385011901c255440d42d82641c14822050780100f0a6101142c070307500e400b0404800b5998903c0101020708814006008009550343c02074155030300d591006250001d00003c00c0300342901c9004031010240c0c00d1030200c0d62110185001c800c03141f850f10105803c02c505110208202c00000340d403485280b80c15000c00511354a03111400e0903140d07281040000507104245401e411700300701052101c4144141400b1480624210110b1441e401001a041c1000699400d84041c08020b01c00c0c020583c10400d80645010030700c0307902058500c0080d280010001500304000b2580c2c03028410a0044c2030010300111051075208032520281040c1a400d81c400d52034090500c186d50701032940c10000342d5024200c002c0fa00c1c40d0423825034541e0000f0f28140d040c15101c07810800300e21001c1c0b01491a1501c02e00c61205c7c1c0703000b80004039103481c0c012000318117520310401ca = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 398844757 1250 398843507 398843509
    0x507021f1409031009030c0302060a151a190305150a2315030c071a060d0303020903070e09030c390105070803070908060907030b0609040204090203030c0606150702 72
    0x760019000103052850b0b8a0315010046807410f00d81c003608003000c6181c00c4d181410503a1242c42e0044041c0030754221209502c409000408039100341034400e0072116260307000c004507022070160130234420a410034541005400d070076100840040007010b03000079644a040100c45081d11443d070008140980d0280c20780d5040c20006001422480c502140203600d907108003041c0d45d980182540032200d01068152607045c500d42e942401d800c85032040f1440b80001801840ca0214034192521842c802400001c0c0c840c9a502c0641c02540308810440c0c00d8085d0704008102d803480902d141d070051000c10f00440d91001307020501401c1000e42151400380594107505454038000700010076072086820800c21071144d1100c0010382e12403080d410002e0100d400031040107400c44c0c0080722a0101c801e210152100ca0380d88140540e00d800c440d0100401c10015103002c0303502d90900041d01a440740c805403001035103a2180e0000b03455a044200e02e00c01592106c0308215840c00c00329102c070f602c0894806414140300a41d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 398846007 1250 398844757 398844767
    0x9080a0506180a081602040c210906150609050a060305101509030213020705160506070303020c030c030408070603151401050c01090c0f030b1003080a121104060507021f 74
    0x14042c0b480d114201d680c280324140d0188401d2003019401280b1644c0e0703040c401907090100c4404501070b40b0031454104148a041c1c003072441403003034900300840341d40c4109120410900803c00c1207015141e0554588642014904144007400074090701e85034040c2c200d1400c01001400c0e811031704504205030506040c0006c1440083c1002c00f51204e00100d90040702c140441200c0790040c0394400b81d0700090007010400700c095154020300040b80203000750303240c8000d42119020040d00d03a2003100d030051010002d43c400f11b8480d6019002c660192020741c2d06d40b024661503549035811607000a512500080c0b8100f0000b80c040c4100c1c001030a42e000030f91440343c83c009650128110154240d0306001d400074800000a5080d03125410017036000800c90540c0781ca940002660701d02c030380403c0315154407010124040d180d40321000380481e030340000c120f0310700f01c030410049030a415000b4501c0e040684483e4040400000d440190010b012240d94a9403909100e004000007141d040e542075080801380007100c025a81c1c06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 398847257 1250 398846007 398846011
    0x6010f05150a0c0203030f0309190506060f18040303050717060307050603041509081c0519090c03050609010507120b15090d0510020a2601030312060305060f010609080a0506 76
    0x904619071102c8003190181c84000314550001d5042c000007420b05003480c0e62801030f40c0612544811203698000345c030910b03014101200c1010b00b8039400800003e005207000c500c205403423080945814401c2c80001c039055044442510110042500c0d1010046465070140044017044030802072460b8905180b0042a100d040e5805454011000000010280078021103112541c00b6402000c20041005051452003a001300b01c100140018003a09003001c9002c03030184030b01480514150740294121140041c006020600f000c4480100303070600040803071020700c22a4403440680001140c5440c11800013043c00400040031102c4500d0604c2681e029124040010801d030704206415580307031780d1a000222810b00c004030040c494461030001455058694001e0541c20355240c5461940384030079240444c03a0585103821a50700e0806c08010004a44684104507100c01c07a44030008226444c1c1e00d40d07500f0494111600010150717048010440c09a01c88880d0005003090320142405006550320641c0b90040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 398848507 1250 398847257 398847289
    0xf0b0d0809060a0504050d050a0c2c060102071a070303140717060f0d05071806150305071704050f070503010501180f020c0706080a060f030c0905090c2106010f05 71
    0x803d442040354014422640a014010410700d1800403615000e50b803464061021200b130076483d44000388003034582612025183e01d900f80429018074003902c0c9414080d00a00c2141140304a0500262064942a1603003184c9806840140d80f50a02d050240640d4040c07041c0540085a1400b00306c1d2030b96001e0342d05010003c00070f2050310591689000a510301d41c0c09641d20340c0c0000811144c3c01045000902c900440b102d10b42d0302c05904440031403003400c44d9420701c2905c42c018426600000311070b100ba4000c9034000c0581c1400040d04d240382000c64540341c1d049501300c8260380883d00c02080301504221030001004210020310066042a481c050038030000405403143d640c650510b820098010f406880d40003401108403021581c0e2000c1c0144603010540340f54448919199011582c82c81400c0001c0c26030f5001503060100d80d2502c0b008400501000380720113014042c034a05079420340d03104401c03294201ca980801000d00303501900c15034100724041c0d20404200720050001c003c01e0726915082619010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 398849757 1250 398848507 398848519
    0x60f0405090c09090d0305061c02120a08030406090209060f0604231306261f0b040f020301090e03040f26030a0206040c060507050c1e040e010f0b0d0809 67
    0x11400850752914901080c403a41c446840e10400090700710000300e008010082d42c0e010311503a00c0e0b42c8240106001c002c800c2c9040502c10700701000143c14410380030440381b80400101da91000380ca440b0800290000e8404440c010744480c004415441c0603003000341c200714100e03071070703041404c2d403200140480c400e510544d4005001c1041008200016501c988444070b005003003110b071000300f43c203484006c0c0300320700035860244c903041841c1410300c42c0501c5070000e805c00b5200502850315410b0203c0180401c8100882d80316840e10440f000e01c0d202c900620110f03014812003d40c5035410014000c0a4400c1c000d080c8046e94000c0c40f08100005207148002d040382d0941c103018041c080c4000c1001300c0800c0944007a00c262000003000c0c11001c0c0d00140e130034800e074018901001080d440c0d00080750030b032045040103403680d4002803180d281803900c01030405c021002d001080002d0b01004000ca07094030b51411000116135034805c0c5c010b030908158001c86285810848a8101d85900c665980d000c900030068a140100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 398851007 1250 398849757 398849761
    0x312150d0212030408060a051b12011806090c020607030501060c0203070320030a0c060e01050415030e07090c05030f060409030f0305070203040f081e0d051804090602161101020303060f0405 83
    0x2e40c0600480d0060044002614402d140c10440300c07010700f005468038180113070701c400e1810051400d4002c1e10070102c40f01500000d6a464101c59442c42c40d80e41600707904035681c031080044c680e13141d03200e0030390390810399000307440c03545084d11014044440590110060103144450400182d50200303009050300d91140e16242088501200c080310140407956598241c840d0321181c4040c0403028800c0c0044503550780c1d9602004521000445031805103124504503012651030704203280303000e508816001c50700e10003101d608554500c01d007000c0c0c85807290400c01056001003403003891080c0c0500a40d0045003a1414000c0d0710f82aa80205000304419040041564810110300001d20078412100200080104000c0f0a900d5402040d00c4040d101603218282ca0101c042981010004c21300c009020810b44560341007a0400130102d02030b80062003915441503540f240440000e82500c00b81c0116440d9200e103c03980701d154a003500c0d06002c205121810b55005008220752a6a00c8003128410746044d60702050380c1e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 398852257 1250 398851007 398851039
    0xd02070f0b030a0b210106050618040c020a02062b020c0727091101110c013c0221161103030c0109120e010c0f0f031b050312150d02 58
    0x184031039161284c1c05040704103400401c440052402400c8045d920082114966810030840b00d44116517410b40e00d0b68801429a1551900358015005d44c3c007a401520f14405050340000c000758006140c00f900021605030300c100c4500c401e05590103501c040d0500f103203071034182040c55648010b940700e0a10022104c00c800044e11140d100311005202101c001401001c2d10703840c3c10206c11000c00348850001349424021550024002a461401c2106848041d99840f41d40320792280f400c030288144050410825100b0a441c10041441404140540c003034600981c3e81008940382e440c40c41801c912004041c88000c51101400c9404185036a000e00040c2c800440c00000c00d04500528801000c0c0d54a000803400c240318941440752104c0381c403607036000002c0351650015a40c04003510005803a10784001039941c0003035071030170742002d2617030003420300001c0008160a4a00c20170b09801007141c250300080340c0000440b21442d02140c00051520011800c0c002c00b00209583e820701d0300000c1d1042c000c80803034a202e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 398853507 1250 398852257 398852261
    0x90c02030712120c05031306180803090d1b050d0807031b03060519061403040201020109020a0303020703170306030a03121104230406030203190611030405010e0d02070f0b030a 77
    0x5250b0080000499900388900900340700501c22691101d81e013400b005030700032071044040b24400c4d040c017800b91030768844a41300d14004105010b00c00a103420b10001503c0071804c00e00145108001c0007004040401d0138500c0240304001407481090060b4603c1c5200d000a00c000c1400c60141c0340034641440707540e84444085019007500d07003071400e00c01001b0302120340180e490307080b4400703030340003070b41e1142c40c440e40c414011000c110240300700340c006a0182403421203440341500440d0440c0c014800414004600d40018070100856032046001d6070103084100700300310300300c2c400d6625000071a41060440c64060080707525480000c20007400c1020032500710292403007651000d100800301c2c0c40c103e1f40b5070340c1320940d540d0b0b07500078a54103c034240d58030900011740d442e203406402c1c20350360302902801d804030602c40c001d40404404503045840541b101100e0f174141466034040d600c9103000b0000400c90020002c9280c0c1401c0d601e2500c18115005040b09000010380340c44503030101d58a800003580c0e26618000c02c0c0c40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 398854757 1250 398853507 398853517
    0x402131e0509010e061602120918010e0901050c040f120302211b010603111c06090809010e0306041112010b041a09010b03040f02090601030f09060515090c04090c0203 73
    0x1298601d48414003498100552003c1c4002c1411412595a904d441d00c0c04204040482036507001a400000345e01100000500a440000b40150001484041d00268240030b250260881105015244104013000c8402d01070650040d501414003031030079082c031000040b04005d80c010742d4103c1420850b540304040c420803287c400b04909891a1903100641000c02d07010341d100c8a044500910614030b182031940301031085108880d40040501c9c00b1300405c4082c401d20304e00000080e100400d90b840c0101c045420b43c01342842c542d200388569981c44c0010000940815510348419000707a12038020000003030080420640c150b00115407102141c6140e94003203015280074052560414248000d22140c44810508040f03401800c4614600903030700c84c1201021408121000f0300032000c206400c1015040501000f50044010302d804682c642c240982007090320256801203e0b0305968008100c03103442c0b850000c1c003803a0021103031030f07120b400c044000d064580078600601410543e50402c04200c2402042211 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 398856007 1250 398854757 398854811
    0xc0c041a0909010c0923090601020a06020301080d090801090c03061503020415080d170a110d05151302121f051305010905010906050607170f040305060402030d08040213 74
    0x10301c95260414116001e070034408000300100700443e40c0802d10181025450400301e00280f00305091441d07030010407a0703a00e4090f040c1da040d400303802c07000404902e5034001180030381075081c01410300841c0e4000040144440e85d00084072a458848810000b50f40c0c00314a900b200d030011808910000c40e402e0540a80c0910b0f40001d6010b85441036000360454a841d040044a40300ba0560f0000507030244150781c07a103040e052101314030a1003c00500c41d0b004a0344105049505100e21904004070b001c0e0301c0c0e04840c41070b00d04502c10700076801c00845529003100402d005103c40030742035040c00c40b0803084100d00e0f1809482200e080010805c96810001945600c800038180181a942c0c0480418200c0c00141001e0181c0d28400d402c1a0010031000c540d4000c6404948010b46040d181048649510b4040c5a5201c110b84c800242046840381030b0850401902c00b650055001d021035080901c1054908a00340000f103050000f00f00c00c000240e550b42030344d03050808488902145080340304440000050071a0851 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 398857257 1250 398856007 398856019
    0x30307080c0f040906051f0f0c0c18091214121b03070503040c0602061519050303030a0b1206071b050712030906031409060a1a0319030909020c0c041a 66
    0x842c0151350300000d00702c5400b42d8014942d4000f80940c021038168146101c1c010404180c03a0940c4144110041040c8a01420031010480e0711810055018003c1c102460311880c2c549004005000f0011492204500181442c0d1400c0e202300c6112a014014095020b03244594203002404100001145803040b00c2c0c3d100a0313a561703140049024000d5001900d003541c0e14420340714080f903a14000180903001d00e1080d01c48680e009444802c2020100004460412255440c0070004041c2c600700301450083c10b101c200401d8818111051100b54840040790380040e50194040c0588146c102d5500c07003441c00300380121503600e210307401e01e02c1c94500254400001043c801083d04203144d8842c3c0d9007070558005035414005200381d000d010314903003000c0d01e050790305410400104540465984c84001d8484500b950400c44100c102d0000c1c1c1803c0c1200d1000c9541e43e10420818101680404003001800720341f542103040c00000003113180d40d009206000f80c0a141c0c1ca021481c55401d5020040d00480002001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 398858507 1250 398857257 398857259
    0x102100504240905060105093310050f090f03070b131a03090c191212020705030f071401030f0504050c0f04090809090c07140d0807030e030307080c0f04 67
    0x3411104030310790355142e586400e0010b8050070711014010041e0380c5400c1001845640d080a080040454002d050510341c01c040c02d00021000c013907101840d80741d014000401801044034010310103180c000103403901c1000000c101c030400c022400c005407030341068140da0041d01132a849000c2864003030290040b01c00c0110100300844000d91800c0700c0d4040e640c01003c900c83c041c04003110540350703000560703a42d4401d400402e03200355581012400a50f115115500c406060307580c94010401110460405440484200d00c0347c4a00d0741d01004014021714007a0b004058100d41c0d020705907101d80761030140d0801c940c060350942815a109402120704038030380000401043c109441c2040e038691500d205180200c43c0e46004401c92300c3c00784580090f090304040c0c2507282c4a119000c2010844000340100ea49040510400303011848134407031a442010110010250b4070b69400014100801c0200103d00301801c0904100c141e100100903241c00007240d0518000c00d0301c648026052500404106020700c00c00824 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 398859757 1250 398858507 398858513
    0xc1505071704140a0305210d020a020114090a03170a11160203102003060a0305161a2a1f0b010311030903040612020f0427060807050f0102100504 64
    0x100070012220b44000c1c4108030f010782010302c9184003107403202038134503000051503100000300501c40c2d95900192007201c500e00380e00030302842c00303e82108480f07600503903564800162561039004c5458004400100038070440b044e59900414207002c03d0034110040c485071303022468820a5411002e100d86000140d0358982810440040c0e41d40800c071401d900c2445a800c6009141c841c1d44240c001039802020705a00f082c040c0030313441030990300c0078018540010650000002182007031120444405180350046095071910100c107526143c42503100e1182802084104105903c0201d401d1809128000780c2c552403981c41000344c01c00103544414100304020026151034500b4944c04004450340988040201450096091940340000c03180040030703a00412084c09824040d001401c3d0b40000701401603d042e81e425640c4280e078116501060407034560711841c0c0f23444580149072104044042da01040502d251a00d41a0340780f0040c407805001d02d4a80e6400381183c2d10a001402405610180030712150074246 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 398861007 1250 398859757 398859803
    0x1003061a07150501080c10110a060b090117030d0c031409071a0403050706110703080f0301030309050118090b030c0603011401020d05040b03010608280b1c0c150507 72
    0xc0c000c8408a4440a111001460b5403185034144d805900003400040640d40c28000c0c1c6c600c02c2500e8805210f250003415600004c1006104001442044d02207104e2401509010384882d06030010203650341c41c1045040701002c00810349105002c03140300803500300e801110a030300500d0500d0701020700303101c031308100113013850f00040c66421540b418510881ea142d284081e07481a0080303020040181d008442c0800c102e6200d00e45907051160b218042e240c64940d26078035885580d0000d4011004040017000400905030071078200b500405080c208580a814040420740d803c8031140030b07406403143c4d1200c0101c1c41f500d0400c20100500f4024042da0b46c1c84d6152140c800b54904040c1080f401031103282c1d00301c55414170400595017101c1e145a050750459081510944048100514121100742c3e00c00300c454800d007441841020308a8280000180e600101d024410143c080301c52146800c80e6069100d030014100c090442c080322202203174130b604001d030f40100301c40d82d2250001c05890a40240000b018000d091 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 398862257 1250 398861007 398861017
    0xe04030c0c050a0b07060c03021204031706010804030806190909060608061008030406081506040e07080c03060a1734080a08030a09170a02070303120b0303091003061a 73
    0x1c007900ea003000e41d40d4003000301c19030003800362000d80c1c2e1041c00040001010703604041c41640403400c001d82402250a00005840402c58069000400014805200c0a21a00342a800c20000c0c40c1015142ca0a9200603000341d801601d4903001e840111100f0a5030769030007500c03030040c03d501d103030900100020303043ca18047d1015000342c0c2a11b0150f01d01164542d42c44560940880780400c02450505141078415140807200500c015851030110742c01344140d548a100510103482c1181000c0d50354100740d18010070005008002c01d58505081040c0642c2ea03958a505038200d504252000e00103104024840703003071409001501d249520140d5508603c60788100c0020030050850303800440c283d40ea244030650f034801c15100a0b290721401c20100c4c21400c515001601c02c0750150701260f102c44090749a82040d60702500120700180c02c000c40a0040560040c0d000075110403a010621032030302200300003a101d100d050506071007401d01445600002e1f01039084100104168460a01140ea00b004400210750007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 398863507 1250 398862257 398862263
    0xc14040b040504170304050c0a0306021c060b1b0304050d0524160c02031f0507090915050f12010e0309041b080106081306052a04180b0a0e04030c 64
    0x40a400034020308151040390700c19a040004801c07141c4075201c600405074000f074410340c2e00c0e000382c2402001a032240e03450300e402503114240060b03940c1b04134030460414440d1a000807440c2424081c04000f8541d01e1402d8608640b640c00a41502090452015266204550029402c4000c4000b000107020011070340c0e0b4860522405221100c001e41105a20ba212045031403c05c061060300201d1940c5224540c0b0716070180c0701404075040f000b016100d03a10440701751400c0c0e20180380c56270100404258005a100000c05840d18140f116141801980014050320302509016100b9070801e1201580c03680010241111104000c20442103010b0f408c54480d0b01a1000c280181c3c1400840d07007810509403200c2c1c10300d00b007a9480e9451a42022022103520901078a0343c000d10319060078905c0413032024864a030003200a1224a81035001701d682150344080c2180340052600b03410702040100c1d24140e44580c2c6130088c010740000d0a03403455170009412958540020301c1c5050b03540108020542c00243c02841e81c2c6c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 398864757 1250 398863507 398863511
    0x1c1107120206010b1e07020405090d030b0a05090f100b070c060906050f19051c0504110411030a0f0f050406050f0109051306020c030409150e0c04230301090c1404 71
    0x15003200580e9112000c1c400c1408010080000d00300600030943d00070b010700c158100c91442d00003207400260558105840f826465000840e24081e2142c1500c1360513410001920f1500b844c41c03510b0005000342d03800030310080c94150f910000a41040c80f9085500180c8000820261224030307504051525001ca8000c980103d031500d0b00114240c0d029900b551000c0a1030410149020072400001942c140c000f10400c0030300c1010b00c078034040030490424543e18030071901c0303001955103000c0c10b01004c2002407811180c003440c64581b254140058240859a01509040d00490070301441e128020082c02012080d14565160100b403004218858210602816520b04800079a0b40c031001200103c450580d207206403440d9112491300094103c3d00904400d2403400c00f600c0c1001d69860800701611440800030540118500d0180800d4042990150300040e16a0381207003014108403444808038818a480c03070b49920a108040501e036001d4000c3c000f40f40d17111803080402aa51400403280566010076603126234 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 398866007 1250 398864757 398864783
    0x3140c03060c0702012304090906050a2f070f03050405090901060608070f2109150212010605030c2701120506030d08060319050c010e12060c1c1107 65
    0x31034002500e41c064102c405406181400da903005680c00c10907541c0b1000600400013282564200c0700c000b40000b00038040011031080628a00b55040711002040d04440e0341c900743c044860701440f120150724a1415041010711800c1000003200c1500410900500390241e40c0000400c056108000d80103c0d81c003030341e60700f0040c1c40e42889a07003139801a004036000a002940020141c502c40c4003001000d40381801c5c5038190303680101c494105810204071400c0c0081c0c40b0009182000030070000d02c408201c1e001c204506046603c40d250300e6000040c42500104040070000c07d0b2010080340444814a140c0d04411080800c901d060314030b0090060141404110f009144401112007030150a1041030300602900442c481c8a41c1650b10043c0500600d80622429181d03808c0004079662511b5204c1c026401004440c203208001002100701110850080d10741680c55440d142001031b44c1f6800c04840710300c0340d844040c0d0601540c1940c1c00c00d07525009450801c003140340140e54510081c20401d0180e62115592 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 398867257 1250 398866007 398866009
    0x30b12030a0804110d140708071a160201032403050705010c08160303020918010918030f03050712140604050a0b090c0d0b0a0311041b27030c03140c 65
    0x80c0900003410010a0101000500085207942284075400c0000c142003171381c41403031b218420384440010143c0f040381e20022003801000d504000520040002d00f010103c20450440d0792500380c06400c1c103032146550407002d800210780c042c0d08220f24032007440c2d0890000003000e130300056403210b8a10007940d4500501c80b0120780b0754402c0303141032a1a608014100d1820f0f90681c1c4a20084c19141c80581c20558240304007400c81e5151807030741301e0304001100e03081040d50501c000d20040b181c191041c402400041002c00380065001580c0703210713007407440c00e00103910b80d55002e05580c910503090200400b039161a0300700c0c014001d0f03003030395a019540c280c40401056a42c07a041c001140c02c00208154410403020000d484030302098000e020414004101003442d452520108400b244150401c0f1002c11003515035007400d0601e44103003030180002d05e4000c62840d055103809062a050a5141039078802e004c1c121203078054403c0c0010000359070124610030300680d41d0800c8050320340028001000c40c02045096051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 398868507 1250 398867257 398867263
    0x4050a110f1e1203040e07020c18060603100506030c04080c042304050703061103040303150506030a2004080a12140910120e2103010f03170c0d030b12 66
    0x94060207010b40b2803040880d82140001906001e003564030600c0042c441c0100b40092020341300030300c0d0781c0c2501d0b01181000d081c041d003410900322036140500381000c41101002080080150029030a07a0030380da590301ca0058921480000d0b420040c0c1003a40081800312050070301004008480350001520341c403240325810403040c2c0b078000010500c1c49840700c0507022100c0d40643c14a070000e10030011551800c0d0380b99103d8083d00d645040c0307422200700c080304000c1810303098064100c1c0725681c00c04240078070f420503000411360700024040a81c01950340d2104c904003001c1d1442c0070b07000036040341c0254581d81d40e442c2c0d10f580d583c81214103c50580b042d580c0761141c00c3c00740b080798145120031403a403414511001c0c18480c017900e40d405058100b201e010519105800d0070310800b01000d02c0e81014044103000b940308001241c501c084801e9007140c0410040002d41800d182c20015240e01c118244800b03100f404019049001d04a09041107002d4004000002c45e0103522048241c041541d280c074000710744c9956151 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 398869757 1250 398868507 398868529
    0x303130810150b040e06130e061e16030f1104090906150b092205070806011d030303150f131e143106060801140709150306090504050a11 60
    0x1074403003c144001d016052000c1029035000c04090940d40d0b102d0b03074048120b001c0d100b5908852225801c10300c28040040d0f4428101820701c02555109031050409101c200694014501e80204040d510b10300d5861002c2250041000140e40903000c5807211b407614560401480451b80440c0c080b46090700880ba4654102101c13811600d44000c3e250600e0031a1040c850080c034400111030006400344000300044c01c061080b540941c0d500c1d40c42d03200505d0090f001400215000c484a18035030101804209241d8000003140e900ca03c04030f00c510340a40f13125000c54410015613200c10b034418030001c0040c2c202446940320011102600c4000303007503202c0c0122142d0483e100b400546c4402c0150400103804076603907480c400d030b0304a0100c96180040c0d4401300a013501004401e811150300351509010040220240141403010640c030300d00030024100440054074140f150b10804080d02e080710590802903000c3c0d88558000c241d0f07a90148000c2c40c03d441d00545601c040310003140c0841c0208110800d500303054500c2c0c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 398871007 1250 398869757 398869769
    0xb0f0418060810091a150108150d030c0f0b01080a05011a090103060902130501120c0503010b0102030910051e0901030e0601051309140109050304080f1207080306030313081015 77
    0x8580f042d180506030303000c0c205085058820503c0403962000f411064540f80e4491281b058050071181800000106502d8004d4411075106c03510760140341c0796076a0016011611917160500181001d640e16044001c030f4010b410140040e5030034400000c44000c00f18501102c0c0748200000c1012601d40701d260340142d640c0e80880c0350810305100040c000180140e000c6c006250000705a001501d0951100c4002e44109070494075182810b612200e08100010140c1c0010704021070003404120102c40000303590740a0700354240d218107400740c405505240184115401c11031002041c0c40444425000000b080d444000c00d580024030348200d210b100c1c0b8000c01c0d1681640d80c000c0c41d81410720308001c00b29001c2d02c02980241c500d548820752814080000344a4284554880c00185440384d26200c1060b04000d40c07400c20302e0598200310442d0303c1028070302007203861f5281c0c03040b401606c3e500c500c1c0c0401d1039401139485078203c1d942a0407003c01c0305040090032001180203110180b0040d008e0788100224201039100305 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 398872257 1250 398871007 398871013
    0x1110c0f0d081b1c060801150905090307020d0f050a052a150c0f03072108070813110d061d0313090f02070b100e150102250b0f04180608 60
    0x90b08100f000c4000340000004030440f60760b000003003c1d40000702c440079403149400340e542d403d5266031480b510992400400c0003500c100000d25003008856228800d0b400004d02c0f8001e8010034508100800e00c014249039002421142d001c152450580d40d81c0340c43d040368520f0707884690408034a040801a4a10b2600d1001e80420348441e070b80c031403105598000c20844c42d0b40e1f00030020141c19844041010300301c064020007400f40601880b50241c0c407260700d40c07041d810800082d4420028a290001241c0b5040321800b60010095011428040702d2589a610b03410b6201c500401c004080c000907400100d010b03c44000710908402003900a00e50341e1040025604414800e16810414014103500401c5100c10284c5c0240c50005141e480c0307061024100d499042500e00443c091107421284604268801164042d04031540310220020303645036507458071403040c040001284120b07140d491111500900140e40169117600c040499143d0300e81040c00f0340b4002038400e00310a0003440c4d05024180440c1c07860006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 398873507 1250 398872257 398872291
    0x230301090510051809070b0a020a060f060f0e040503090406060522080a02041a0a0303091a040e04080a02010f0203091b1c030f030b1003051f0e0a0e01110c0f0d08 71
    0x3481c80d80c005c00101860181d203d000405c00e5104000740182400b070350162401050300d00d012022a00f411764081c40b92450400305004c0c0342c60070060502503a0102124003002d40e81d91610364558410401000d0700141014800280650454040e040e90201940d20403401c1da21080c156441070f84902c200c00c51940104685005404c242d401420914106805040400000f00104200038003680c011000558852800c2150004410410340320007040494a0310f014603290301070301040009000a4092030001481071030b02e0b4001d41c8000e00d1042c4c1c24405646034507111281075140d07030059012800d2800300100048880c54034112503403e80e00c849030014881c4942d030714100c0e11184000404010315031f8800030f6140940e602c0b51094071000050b42c001c80d442c03a05031031114107021012080c03020302141301824040c0c150f000080a500404a00001074043c0c84907004602501016100042e0b80d100041c00313100d000c4021030140090080c0d10100d41d03200c0da1086e801c54501008640c40e85020180080b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 398874757 1250 398873507 398873539
    0x609070504090204020c0a0503071208060303040302120c1302130f080d051b06090a060608010b0f01050903150411011e09030303110409020c01140601020c010c060c23030109051005 79
    0xc04000b002d0b0020788018103162000c42d0552400030b21110070707101544045012402c000000383c10354038000013071400d039581d814414003080d901d02440c00001e1003102d1038200d94204d4071003000b40c0710070000700900701841d03d04248000002036102c005600105144110042000001030945908031907038a0002d01c8a881d50b0403044a66410580b00c5a04038541118022000003003003060f10302481442028120713558540c40d01904030750b41035105103641d0b414158405010b0f510a000e02c4d00b5a0310a0816540c0c1d4025000021305021001500810550341142440240031400756265081c2d50280ca07000e0f4080c00174001490b1802110100700000b400d40c06050001911030380000c588401c2c800c005030700b455101e41d108820303a0880d00d010381c03c80e992041d90202c0303074881c0350784076810080c01e0004d07113017580c0300900090842c0929040500b085880c0c039140d6000d14810410803603010078050780002400046024503415520a1140c2ea0902d410200841c801c083c0e074421a40c00c070380c00144980742001c1114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 398876007 1250 398874757 398874761
    0xc060504050d20030607170f011d100b0406050c01051308180402310b1903051503010207030c03030b0625051203100303090e040309121b06031d0609070504 68
    0xb07080f01c06101407458451a1410000c0c0e0340508900c0c0c075882e001040b045035030341080c04000c4c03c041c000105100100448280c031341412490005d01b8603074450b540c2d103800060321100350070707488011400740004001130a954400041c004040b4188024020b03500c134400912000f009000010300301f901d0812102080852000c2c2005034008042c101608003051402860150816800307a000c0580340d491001844181c00004000908903500d41c09080400d890b0030309030340944824a09050568440107c0d1540000c0c00d0302012806005000395070b1525a843e000b007800d070301140d0444c086410b1103580748440c98220140c581005100303410344c00e504941c4401440c202d40c0c2f004182d0341c0380a030401200c02919540c000314415203009a25440b503a1440c0383c010900400b40d480902854030721828000002d50028403c8116400281e1681249500342411039442c07100b03172603e10141e048030380e0000702e09070550003c5a02940c425a410181c1e0b20b0a00241d4a502084522079590340203c403080c001d074074003a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 398877257 1250 398876007 398876033
    0x5030601060e04060b0c0d1214010b03040501150b030a020a02072408070c170702130e010b1c0f0311120406091503020a0f050307051606060e07091a03060d0515040c060504050d 77
    0x5140045a0130749d4080343c06032003510a0308000e4080000108200c01e111090040c080c2c2c001d134079844c03600f00034688501e4454500000c3c0c0784002458000074102e4105100700701400203010450000c0916240c2c8824032a20b4222411a50010948840001d044280103424012010307403c848100c111180c0601e0b00d5450f6408910102d912810600c40c1809a5145100300842c14035540c00010381e142210301008041e100d100140c0c8403107800c0c2601f100c0060b00c4d03d0009524190f05007000e01200c90005d4409091078410440c4050040000c180094816400f103000d1080760042501c00025400c600012402c2e446901405404941520080660a40b140000f941c0c440c0b440d10b051801c1c552707100341508000818040a8818a45030903051102c1c000c148441e6800c440b05013802140e20380b40140004441c2e0301c0b80508014114044005074071602e8000c01d2064142c0e106c8141d0341c80b80001c1c6090300d01c90310282c400b030b29060310300e000106030706000d0304c112026100d00404418000905503500c40c41e03c0d42d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 398878507 1250 398877257 398877287
    0xa0906020d1b03050903130e090c03150406050c160b060402090d08070209010b04050904080d090f0311070506030c090f04110307050a120b15031005030601060e04060b0c0d 75
    0x108110078034a191152140c081030001002081c416818018001029260054030418190f04104005422880c981400030101c6840c5c00c440c44c001c2d41c400d10400d0510b04d01c01201a010700803581e11076421320401d0f110b070f4030540c45180108081d8503401c84c040c0032406200c403150340522854160002144000310000d0b84400c00038809445c03d820140842c0500507030300001c07100b07448080b590404501d04510480e014181c001d1000c0c0c1081c1c038210005090150160010380070140014840c80403c007550029610f0030f8100c01d080d0003408852400070700305181410042d8090089000c00701d41c030325005040380d001d18215210079040158001c2040501c066250b1207950041d84e034040c144035000c0d82400780d4840c2403161181c0d501c4001542001c0c04606004c0644c50800e481c1064150f02030740d64042c40320503604503980c07658507550b0301203845459220540016a051140e07100003d5503a520029100c40e160094070705004040d07441e01525840c0c0182c00048010f500b0242035a15543e00c214403103200250 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 398879757 1250 398878507 398878511
    0x7020405090a23011407210b0613052d1905030a03030b0907031401150c230c03030403110105130b0a0c11180705160203011b03060602060106080a0906 66
    0x102c1e03903959009440c000340400700940e040400e1045070f400303109144030190410076440c803900c0c03d076600400360f24815907103440b01241c060501d076150419a00c030b8031109201034405e84c1d40b44842c910601e03812400d8491203114600e10400300c2c030300030f0701314044660f00d40d80042200000300001c3c2c2001700c2c1208015141240c00d0040c1400100da681c10414a1090341c06500d0000d02c40c1c17400e005018502c0740080c1520309042c1080309540311080f203003c203203044442501840780040d6031000100d0741210a8040a040d1038850304245004801d0055028000c00b070388001c96075507401e138205241e147d000d07911010300410001002240f80394003500003420242c100741c10b461007039522448804041c2e04000121000101011404810404c0413842c58583d09402c89142d054442d12a50100c0d04450080c01c4104000c1d0110fa941d20340050841c140d007403183d004000740540107884c0414000407110a64420000e41800000140c1c9270001c1b07000f0b410b94010307640d00300b82c0741d03101100704003d0086007008a445607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 398881007 1250 398879757 398879773
    0xd09021e1e011412100509040f110103020702030f0f0c1909050606070807061a09160e011101060303050d180302030d022104050607031b21060801021315140702040509 73
    0x2104607000300a2204d20469801075400c01034010400803c464101c940034207c25800d0001103808002034401140c0e00c80124061441d181c40120080c2c01019802034052040041107480c2500204008200c2903802e82101d216214040030800d0804800070b00b001e002085100c24000c101f51a001a680300a001e086a840c03c001503403625500d07840807000780e9030315594496248a407400c04c580075070040401c0315040305c030382041e542c4140c4040b04682c3c0202403040e190b402e005564043c00c00020004e040b04000c100d41c66407030402230001c0d0322114424040038a000c1c81811594000e400410010b600342d4019400d02c0c40206204c1700035401410400c1c05e0342078a004101522208649003032059106078068999818900c6c4082c094801c550909445540d620424044059001d94510003940c4681c14501200314414070306001400c00382c2051007e03500003c1c114050301c0a2207440022608184542411062400e50446071903400c1da8903001c00c684e0802105015280a40049030401c01ca401030340e60344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 398882257 1250 398881007 398881037
    0x212090f040f020717180f090105010c050a0b101403030a0203070f0609021504090506182a0a0507150203090706081e01030302060a1808030601080c040b0d09021e1e01 73
    0xa00d10300040c05100350000101c60003013100340c400030f049482d007d80340040045404400a84024414010607041112000c0d6040910008104041c5115005400c602c0b907801c0180d9106102c070750700d0241200c1c08588c84200c00c078034207000040340c07071000090740a0740c1403100c1c55031100300d001b03d00c1001790350302501c5070002c0000d0b9940101800e15280c03100440e5580d5880c110701c030401d440005000521071035102c4060500d106440d02e03501d43c003008400b400e2400505032420116566107607405260164004254400c0d2660040010003010780611008800480414540c80582c80300710f44184190300700201c1045000e00880803160000c00c14800441402e40040301951421000d90090300180d0107542400350844052190818503580d040b020030201c12241c0324a601c40c480039003e103040100d0b0200003540e8080800c00d84014221050b25103503101c54107200311019007503403d003d9104030b8141000005c13604401c46070101104002d0500380705100ca204825080a502e1005e0b03c1c18410821035000e19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 398883507 1250 398882257 398882273
    0x909020d0b09150a0611030d02161e050d03050c0c0102070605012301090b0703020712080307020706031e1a150c010606020601031e030c0f080a0212090f040f0207 71
    0x1205001140041c0294250003044440100501000c0b90801007080120700d07601c54850301000d46030030f41400050808024449480c0d0320030000c420510910104460603c000200d90b9411454000c07020319690041d12468130b0840c0c0206840180b455119001c0750300c81070b009400a07603112100010325400c10503d05122800d90b03200300c034129145681c600046c0b2165060760300114103102d494000405608851001034142001070040f140604000714482c01014070800242002c0e007105500e0b10b4880e98036241a15140d0000e0f40d1807005405a00710110301c1a10030300c03926020410b00091950704030650851100100b00301d0f202502140c50325101e5130080e499810007081c00c480408102951220112002030071203c0d035802c8007045400201c010404908035060f0701001c50402641c1720b2810280346029500e50150f410001e1160640000302028041ca03071001d041c03140b5040d026900d250000c542443c4441c41120782c86a407280701014000f03000c0c01c00e6070044112003100503005150034140d8450000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 398884757 1250 398883507 398883517
    0x8090a0b090405090102131802160c030501050606130b0705160b071a0106080720011409100608060a020a0908122104020d020d02040f1b0e0d05070306020a090902 71
    0x4030325080041d050065080501c07030300d03a005040d003008505149501e0101c00380c07034001d07204000448110b2841e115059189078100c800c13000340341c6003140003a401d40c5000d980d074201c98032003515036520f000c0009140c0c1c1000c204a40a492a0704031002010b401d18060340c1040c0c02030300040e222486840340003000390091400400290145d0000740d0344031001454aa5540100540e10742080340040d001004111340254107190420000d0400c081d1090100c0c618610307a410b404446003040d82445d0750896202c000811882c002c07134400c42602d626010204464069a1720792240802a6104100044c00b9007916400380c050341030940b600e6040c040d51001903d14000318800c40307000c6c504c800155046540403200c4840c11311154480780910b07501c0c0640002e013207000c502101a020380c80041c4040c0c00c5545a6010384e4052190440401490343d002002d9980c00f48000c42850205112030301000c0329280400100441690110050038010704542d07564000e50804044103050040c0ca52000c90809a07030700241c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 398886007 1250 398884757 398884769
    0x1090c0e011503020f0306040207080c06280c080645010e070c02011b050a230a20030f06010b0a0207060807020a0b071413050a0503060f07080408090a 66
    0x10050703504140981c191200000900b005141c81081813648940168007900d6009504850041c0c0315805410101003034460300780a0100350095000300540011002c1d095541041e8060240038486130f0280004102c62705408044045501d1200040b410714020010b10b40954440c0e00000342a80c004090380c442b041003030213a464a03152200c2a004a154880c08180140030100e0317081d0355401c04c8100540522460719000c0d04102c08488060382602010f0808080c107030380002200c0145009044c5030aa0318080c00745001403c4480420803a4000001203c82d00e49030445641e4020031003841d00448445415040c183c0c05014040003405e550009200481c001d01004856999030380641d02c00a05258558000c0c0c81070103a80028000400d03800561490050703481074201041d0b1329450b5040e80d00c800100074804c40b040d400a28082c008032002c92920441b0702c00e0303038050741c0c154480c010192925412582565451702a0300001e0300b441c800e114503500140500301952600a105000c0b8000a41d80c1d0021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 398887257 1250 398886007 398886029
    0xf11040303120b04090f08130f06050304020a08281509050307060506090c04060c0303060b0f0a02160b030f10050405130519080d111c0504120305011d070201090c 71
    0x1220300102c25005043d1000e50841c0c0402805900d6911410344041843e400740c074106001c199800c11449643c11003000e406140d203080910340d901c11340200903601c200d4003240550440d100011f20020009038202207200f04807950380721a05000a030383c0107100c1103041541c00c202034000040010040303100c1e800c20203001310f01070b690398202c5003040d000741e0304054030250281101c08100801141240c00740c0d020750f201454601c02840090a00300c0141c00103030800d413000b50303001074400465011500242949a1603400b07841d40c074940d1025605000740a80301d404600401000002e00000030400c0d46544056446042c02100d91104003040496004450f840400040e030348040c0c050020810281310f6040072450301c41074200c1c40395201c0295004241c4860380850b11a00c028007000c0f1f880060703500d41140c1d202914100c0405010b54000381c481650242c92010303019101640941c400c2c09000c0c140c0e60b8000142c43c03c42800c590301e44810302c0c014251421135607901a0b803000a8640d03192540106109604 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 398888507 1250 398887257 398887277
    0x1e06050a0e030a2018060a1502010e121905090f0105070309090f05150306150f18040506010914010f1406070f0b0103060f0e0c0d0f020d08030109050601030b130f11040303 75
    0x3c2c05000d0058105454050b4a101c0412a8a0b90f854107c501a2402040c07a181c03440c0074100d05074090a08801042aa40620301c0c00c0c6400c41407600c06002e03004c8090a200d024011a46800e50b103a02c500602180c0020004204003a1940a4002402d4032842464095031059881942504865005448510044c2c80d1000e103c580010142007400103039003100504154100421700700d0220003425501406001100400a0195141c241407405015000c1103400b05150070b1414030345441e82406035400c4249040c200c0c4403a0207981058506a40f02071440051460406840800d094a01840c04da0300c00e00c1048004000740b04884c01503440340c8102c41d1a0b44a50441c07074a0403c3d5201441c03a025131703616010042c00d0000c00092200c200400a845004c4200360324100001512a00c030006500300d402c000c103e104006207a4015812204645410004d94071003000440507110b410b8020f0343d100e41301c41003019050b0b40346c1d403240d04031111401d0700160030107505140c112540c1140d0300540101b41d043c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 398889757 1250 398888507 398888509
    0x408120a03060b0301061b140d270303050a11070b04081e011107080c01020d0e03070302010c020a1a070c1203020d0605060f03130510050406061e06050a0e030a20 71
    0x10361405080c3c000c007144e06540c1808001008401501c00503184c8403030114016003801551402d1305103401c100c6041da10080f00c0c6400250180c2004080c08c001190300084483c1c2041005110200b07032503141e0746940c50070701e1101049030410400244181d050107880b074005810b00c00030008000a1451030094001aa0700d01e80c400d000064500c0c0700324003a41000a01c0c00031104000485180325408003055460390118030f82d280c02802640882c1d0070710381c60808000f504140c00805040d60318460340c000d2110921886040717842d00712089004141110046910300008000002141d01403501d140445510b241c0744c44480c0d024804401b1000841d80c0000c80101010311802868041c1c0b1050b50300c580340040f844424402c512000b40003e4164240c4540042000000d028403c0c0d1700d101004107100a0415042c4000105100d2081c440422078000d42c20400d1130088202c40101e41040d141c0d64107200411500391182100141700b0fa9240c066103044000040f0014420b0342080b0060100c020400703d088 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 398891007 1250 398889757 398889761
    0x50301050f270613050102040b03010e040b071706060901031509020415020a020d02060307051314040617100b21010e0105010f15050a200105060108070309050c0d080408120a03 77
    0x1070300b0084803440750410201c840b40014945802c03941039413840482e101c05081a60080c001c0390005411040004000205807030031a0b5118001c900541c0800c900c0e8480c880e06507208210348111006059001c80092507130320304540a00906101810301181d0018040702110544e0003e4222031140c907070200303040c403c2140d80c1003c95069800c900007420ba1124580000744294000f510080c42414000002541207121740185c804100462100850380381e11190081c0100c0354006445002e285440d5001400102c42d003003c002881c80704014200801041c000c01004c1c3c100004850b40114241d20030201c030085c0c2c000b00d941c5910200000041c103012403103043c0d0035148180e20070481004075140a010f4081940f442000c9405039007002940d82520500546414592002c00000400e4485501c40c010a06402c582d01c02c0b00f09989404072a5150300080d01156242c40740a40907030300480c1c0104d29800c203041002c3d8500c1c09824041e00303040c1e64804541c50030007101c10310251410007243c0d40d980c403a014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 398892257 1250 398891007 398891041
    0xf03010c02010903030605300c090108070312080f06040506011b0c0821040b220803030708010b03100b07050313151b030e06030615040f210c0e040c050301050f 70
    0x4c4459820300c0c3c1004854041660b201c0b00d082c4140c001e00c20714168210010030022569880c04ad0400d66a0740c2d580c4017242e20b0f5403461109480c0c1ca140c210816110030f00c14042c451117030b44171452064594564405000091a00408031418019110107110700080d8111f00b0b41c0f11648503201c24010203040003166814104280207101000da060418600b4056001c0c041e5800d40b881d4450301600c3e402070f0008101180c00b444051815941c0c031303020200f0200b03008401103203d20b2803510b40b1043e69030390b060701103040d220842d072001106009080510060400100511000d13004804030380c109640ca146110120003e0b501000141c400b0803070600701b054000021a42141d0410207407044211039840280c00c03441e8145500b44240000000225140d5607002442661400724603c0d640312501c0740e0074151010614022303c1051202c11000e0003410722a00400c5010651008012241350302d003d4903801003080c080d100300c2d031500d00c41c0000300d019202403180b2445040c94000c00d039801e04028500410249007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 398893507 1250 398892257 398892259
    0x9011b0f0c2306030402090609070c0b07110c030c03030406050f0d0501080a140a03020d0f051b061909050a030f1101050709140904031d010212130303021e15060f03010c02010903030605 81
    0x5101704000740e510410140c0c0c5c0000251608002a80d40e240112401c050200006101c80141d0051042440d40681d22071403040b6150100c80711590510200340e50380007202c00c2039601d5841000140f103450721600c00740ca0010320503182c1e10304101c0020740c6c000c10741d00240c0002c1e20751341c0003080d4401406910942d046003140400c024004c1800b144c0c40003503d8030781e540003402c00d0050102614603040c1c840d03011610003040702c414109148080310b0031182c4418080d55590140220402c0c040300620303003480381d5078003280c0c0500100385d0010181d80a40b00120045218010302514500148401f0002e02501d4882c000650341e4410030742c100058002c90000000685005140d1a02000002500300b01c1d08054441c0e000205480c004c071080c0100e24002400710110340c0c9010100320100e92118101da08800e0303e21a07001e4800d5400345087c800c050f4114040d848401d035002d501c6040740d802d80103260a401c01030140102154134013441c01719080d51480c000c1000142e41d038070020000d15504d489480041e01e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 398894757 1250 398893507 398893519
    0x207060b090f15041802030114041b0602030d050603071212031d0d031d0a050105043c0501060b030903030f0a0b130515100504170309011b0f0c23 64
    0x1414840000d0883c00f66800d1809076070b40e490300003150600055084c0780a0740c000c1c000d01c0920341d0038040c4081058199000c40790040b98004c511415001c0d000008151006c5600a43c18107031010a041c020341409004603800d40079601d408034440500c0700144c00400e020700c0300354609801c03100f00107040b1032a0001e4840c801d43c903000364403120034010407004080541d6242c0400c2d03201500c1c82d00e07040810752281640462158480303000c200001034110300c2c07042d4019415040c0c03140c010190307480610498040c0c00c8a2210b05808540c00b8a52a0681d8002e01c0c0284000505c03a0348401d460074041d4001d0314114820750003c401c002c11840c1c603a401581c03180c01d0071410702915a011000c5840e0992268081c2c7c80c0d5a00c500004091215441c0360040c50680107080000413020180c0140c1194090700420026044020011207840b60000c115400d281d01a074030404a0030140c50741080160001608485048034109404045001e14411101502c211422883c0c603401d07648090308084400030480e400740d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 398896007 1250 398894757 398894761
    0xb060a05150c0d1d0f01020c0405090703020a0509090627162405030c0d090c0321021902060703050d0507110c0d050a0803130f1212090c03080a09090207060b090f 71
    0xc000305502c0515136400351a4800d040402d40c1c010f0381080f44242c86030703070800c0c03500d410408a0324002400d0022203000f40c03220f202c10ba0b225400c0c00050281224492126803015000c690150b84404a0b840c010b40d100341f60480500074505054102540482c100c0d2040301c1c0d00034180590700700f0a00c100500d030318490000000c070f00f08050141160200618841c03401c0c0c80402e080c103030030300b4503004942216806104040101d07200e00e042d00621950301640c41010542201401440e400011002800f4051308100100100c2c43d07401c201c450b9100000480401200b4400c0c0b40380d54449004090144c01503440e03585003410010481e900d0039007065543c0b4031420020f00c440c0e0109901150812000ba00013685543c0c0380e90380552240050003189000f805010410090020b000100c50205a000c040c0d03034a100e035032110104100169010018090300405a20300700300000340c00600140644501d030b04190280b1641c440078842260001002a200162a100b031413005152005500307902940152081c0c1d154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 398897257 1250 398896007 398896037
    0x61206060a1401090305030c0307050c0a0b070b04080d05070905011814090703020903070b130b07030e010806010909060311040c050406050403030c06020d02041205070e01050d0b060a05150c0d 84
    0x64415100c2c044802c1c0648603040441e07413155600c1e40185401008583c1c2e5040c14a540c0b035580e0384900d80584041c0120409004a854031001c114100e07842041c1060170005c036a1181c40702d1a001030811034091004000c0c01d0b0109400c1e020791803040540f6103a84031414076020015044214004072400340c550303209000d10a4140c24108400c0c0350342c00f616054015035602100b0360091049524256041c81400c1e000a10346820000504035580201201c09099644189500071801001c5004022994a00440d4660751003258940d500c000d051504048440d600c801c19030403510150800c0d110301151151220f418202802403d000480c540740207450300c5e150440090147c0102c0c00300504105c10b04610606001540d01079070300d0406c4040003195520755a88400c840180300d82800c9401d40a101e0001070441454418a412920060641030741062035540f602c00b00007004044031703480420072074040b03565182d01d24403496a130003032094603540300c41803415a1701d08036030504400200300c0060000129 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 398898507 1250 398897257 398897269
    0x10504020a090c1b05120f0c0d09060f030c090e070f080f070e120124030201020d020708030306041d061305100e0712230106090b0402093607030506120606 68
    0xc0480513403141c445401c100d24100d42020000300c00c9818520000c03590030515000174009144001452080302d180074001c00302500e01c0c201511440d0049900740b0002445180241c203c0c007032521941c40c04140d080d031291498800c40310180e800c400001c5c4400300c1d50303810582044d04c0703903000f80c1d920940d441c0394900b0180003042c406001a000c1c0c0079001d00f80d284c1088110940241036400b851502c09190074640103481540c4480512050f4018400c0850b5030400c1c0b4004142e03d42034810b940c02462842d91104103000203030190b030100c4101c4801c07840c1041003404003400348c07d0007120140b0703010120800f141000d074a003080f80500c3d09511403501604001100b4000b80c1a4101e400412001c9000d820700c2c2044c100142100c43c05143d0001ca490480562010652000382521519001007040c845520240012400f4140e0407a410098681c0c400c10840c005c2110900c3c7d8030b008104000301d910120320203c13007512003540c0c200046a12030051006525040b049200e1903140603005100c1841c01c41c0c00100c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 398899757 1250 398898507 398898527
    0x90b0105040f1208070b04050a02090c18100903050a11011106070906120b10080402010f030b0a14030a120905040515030a020d0c05030703030503011a030403020d0806040b040e010504020a090c 84
    0xa10f030701c884000c8000c10110800366510140c009003100c10f41d18003400c02c113480da062440120700c00c41400300050b4041035030105032102ea441000401e00307014004400d00c004260414400014030003062000030000701c2c00c008020005110301600c080c80b18a2100160040540284410311074000b14104408107a101d03008038100c400303a180840900c031070007880c40c0003000070b4103815030002012a40c0d059060303001451140a24401e03130700c0071014080c60000310300721241450101c1e070150381010b04000c0e220800800c2d220105008098404d0b5101d01d580790791545018032041d00110303005000c104038038585442000d91281e180303000150803040b068001382d110406500b0091150400e03603194000d10582411030030181602404460322680c803410b024040e80c100340304244006401d4110426600c0da10825203000b164140c005041c0c0d00c0c4104815290314000400958101c1c1d40c0e01da2510b0340390b0f42c601441d01e080c580e4400000d4242800d00601022021a802c00a5140d0800c04948070141d81b122941fa = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 398901007 1250 398899757 398899769
    0x20f1e030105010f1208030c130602031207030c020d26071101140c09131116020f0a1a0711030a080403051908090f01030603020d110a0609050d03110a120504090b0105040f 75
    0x10381d0b07980da040c0c0d001c9400d0003007000d01189850300227404510140c0000050020030400d020803503c91b0b07030305a412002d403607075680e403c0c0041c0c01c40c6819000c00d60180300a4a840444000352240c500c140401c051a480303001c40383d000000301c0501e500241610284a00122880c01914244c1540b81c01500b083e030500c40c01003480c1c02240c0c0c04401091851156124409512101d00d5181c0d407800000c1840080700101c4034168490240001019820701d00b90790318904403014800181740b4240b0910300c42040b50840101500c1207804402c1202d500d43c0e05101103105a8480d0030945e80380c0e8210b040c0503262180c03280c00f80f007400c0901180c141c0410190000e4500d100c0080b80e100a0203008180101c01600720396200070b4101c03403040340e0f000802070318100c12300300200d0a0360b90003409961940112180b41e014401c55803c860703021411804244220503008041030000e0880d071032082655244401c0c42d10324422000040c40119080c80281c1e558010b81010190920b8082c0c113003400c0940504454859110346 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 398902257 1250 398901007 398901023
    0x141f0b0906160b06010905030601030b04080304021f051315080402040b28033c1703090607081305150a09140a02030d0311090409020f1e030105010f12 66
    0xe14000e40c0c5210403600500940b08905494503114a002503294405482141c0440e0010340c2c085108c1c00c0c002103540c101c80d000400050a9103845d10744101c0b6503c040c0c0103a80004121000710040d09620045880341c10f803d130380301d0366038441c440c1c41506003000d070340c02c81102c101d03500d51540541c41e4000909500310f50101d5000500f6840940002e03c88194000039080220103545004c00e0302e401d1040c03007030490380946402c418038000c8050950101803a071600d60003604260184031012000c01891003012441501d0000c1141c1b070f001e5464841341c00840d0059081e40c0320204000505900200854000015800c0c0d500c54a10300da462036180ca1040d01800e074040031400009018454a401400360316811400c0401010b1114504070b84a0000d900280d001c3d01c111118416118031a22480160030236502a0341e041a00c10010070019011a41c02a80d21000e940000c04441d0303100c10000400c90144101c2c0300d000300071041418207607241640000401100d040080004445000410f800c4035800710f44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 398903507 1250 398902257 398902267
    0x19150b031b040f2f03010503060411040207020d14160b07030c080d0606020a031d010c060c0e031009061b02070605130317030f0a0510060e01110f01141f0b 68
    0x2c20000d10007884000551414000000300c00304050440b0020030f000d01881110f04000340f070481e000c2d03100130311489806501c40b80005001c03034600b004d00c007072070a8004c0c8094502042e0387c0010300c10603403407801030303810320200001011481002c11440b4400c2e046280c120140300c0c41c28460000a00501c40c0180900c10011070703140800248030103d95141990603002c0101940b111030003075440c0c801d20012000310700800f5a00c569036001e003585c060520016956811030001c0342c1d5501020344040d00e292001d04c50b6036100409999414024100340f070080510010354855a8100801600d0800c20300c18140d00710208940c074810360100700d00c800d450b01c1e410600d50f41c0d00407802c0300c4801d003100d0340080d082e100b41609802000d8502c800450048284581210a5466201d040b00c110f071402d5440b00f00b80ea0b034081040010034001d90410039186014140014492401c803281c60a0181c1030f600c07081940d6449a90541d501600c0401070b401842c1319907103080e030000190741c0f20038014840c0900883d80ca40451 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 398904757 1250 398903507 398903509
    0x150a090615290a05090a0905010303091a040821090d060506150403110108070c080406021c050a09050411040302090112050706020f0304060305041502130602010c0c15020a09030519150b031b 83
    0x206c400024481c445d03082106607504d080007442881c80d800703058a40c1001007644510444248141c03800c0c3c9203540060301c00354241e0f84841100f10350300c00c4a041204030600020041d0b998104406141c070f8081c64002c181031a14004000c0d005280845c0402c410806100c1400440c807440e070000d81c030400a007481c44058464800030745500c00c000000801c040c0c0c2c001030202d0750343c0e40802c3d6051405d40c2070400030354008607884241d445015984520000900404d010069440d10b900007950300a0040d21071480c00d07031039030003040f00038609801c2a10703286030340a510720801100300b01403c004d001c24400b03400106800d00840e40c4a104510420003011b483d200420103010345010b4000c03200c0881d0600319a240181c44841c40d403840c2c1d5204442c09540f0349180700c40198061562260701550004092180e0b4803c405102c0080d0030812402c010020200c0c008070008404200000020f000380c1c01c030800c42c40071441d02c40752000070140e0310446141060040c0c440354800140c07011216440100504000540d08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 398906007 1250 398904757 398904769
    0xc050d020a0e010305010902101d0405041103010e03070c08070e28020c06070f0f0909181704140d121209060501060f020601090e150a090615290a0509 66
    0x18020072100b4101c0030000041100c154070000000e032080e9911039810840c4071040e285500c10004101f08000d0b500c1885501d4030305580419030003445a2803110208075684082803c48100c6003008101b584002143e600f031140d480502401400702100038980e05091a6241140d0080608200421303128a407203007501d001c0c1e000300100003800102e411921900d50a44903550b5500c00c1e925140401d12420101d50190310407409240d0a61164032449120b51904c5031031001040c1c103036000010074100d4413070180000e001003040f103c841c41542c3c885031120700b4100c07043c16444e00a800b00744180c0c1521545800603c0c0d001401c08402e00500b000c11050340c94402000c040c18911400400b10f40c0390000116240d9085403804400400d15801c4584d01d86c2c0703500b400e004450891780340b0162075204103034030720700500d5a0101c0303540005031540116045038a80c0d900c000380c40510074014483c4400f03a805004962038444084d0340d203008605c1d1004401081c14030600c49100e903402c00d004001000511039a10707210341d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 398907257 1250 398906007 398906009
    0xa022506090f062403031e0c120c03090e01050102070302100509040f0608071208030a110c0106030305040905091504080d090503030a0504170a091e081506010e030a0c050d020a 77
    0x2c0150402a012245050b01c001c080901c3c4102d640d0ba00e618900980d04204400003054952648a518030008a409520745041c403c0040c40300b0041120341c5080061945104005035440941f10384400c2581803078058001c550a07005505482c035500010410741c1ea0005041c0e00701d83d01030300c01400d1002c07003482c101c2d010310901030482d411505100700d100311080305601000c1100c014005451459445030b5644180744d45044d0064842d0b0820300214800400a5225034090040b1202151805011028550030340300f903540158007049000c981040898054020320703501c02c4000024160883e28840c0d8141501d0004c0d10190807504003184500b1030600d10341c030032300c800d40d0041d04480c0c84e803600c620400c1c068070049801702d0b11504901071950ba030004140580300c01c10701e10303121814000d084c000c1d00320481030054403d010381d6016010024102c981401850740844525503040950700d0240c0015181c40c0d00c02e01498000c0d48081015008a0518000481503420843d080c0d01035000500001e0200f02d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 398908507 1250 398907257 398907263
    0x151104080d020706020c24030a06050312040914060102210f13050a090212040b04031704060c090501140f070f0b0c070606120209011214120d050a02250609 68
    0x19004210750440d400140620403108940c0c21241202c004806100d50441c120414070310210f80c2030556034205034190091a444100d02200150455480000038608602c00d4944405500009814050f2207000d004980c040d03258540240900c3c02c2102c0001d5070f6007c00e8180a034401118001c0c44c68a442000450322400301c80c403160307916006000c100c185414480c0c4030782c0e84a0002070381d000070046c40b02e0091318074000544a0005559903207403600c1c2200200100b04a081140380a40004440a07050078540164054200002c201000b090b016121072240c0d004039050201c181c44050007802410210f540b05204841880d85030340395441c1094442036120303402820110f400b400c001a00072003c0240040c0c1d401214144425540e030002c2000303a01d5603510194110420f100140480261100e130030351003d100b9016105111411000c55041124901c01c510300c00d480001c1c5003184907070b1401050742120007450118a45407901c0690600202c00ca04100c010600c441c80660a201e042d81c0980e2100e50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 398909757 1250 398908507 398908513
    0xf08041e021906030b0a03031b0512030f060f1e273c01090b0609040c020303070f0228050a0b0106030b120a030806060d180b09010c0c15110408 63
    0x4044003074903000b403e000e03140010b4641580807180b03281c640340500c11039070952264070100c071070164040290200c00c0c0341030f00c8510072494081c104002c05001140700d4408581040500c1c01e0010812203800c028104242c4150001d48013842e650351180200f02c14a06e04803003406801c0c081d00c40914000340c2d1111041003051018082001072804410128804510258100d5401c5410901041c52000d04401c900d032000522006112444259020f045c2c2c0b074000801c801d0038960107400140581e00c1d10302a4034016000401070008007901320618000c0740c01c844c000b80c02e10414880c0c03c0009c0d4000351548030001400c21964034203004080c444050134903002840403a103903071142000340c0508a07541c4010300900424400032085900855840b1515526549010030b5442d114200681a00305102241c0019a00d00d0648503101103a41d4600001d4800c2120003001e00d005a44039084680b641e28120521503007041400001e41510700c90220000d041c540026044403e20b40d0052500542d0010f01541c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 398911007 1250 398909757 398909779
    0x10e07090803030c0408010525050f0f0c01060e0112051b01030212010602060709150e1203090303160c0503010615030504110904080c071415070215030106110d0f08041e02 75
    0xd00c440005c100b80c07529030000b0300c007680308c1864406140400e04d440c040f1510076003402c4100036208030b00a02c404561182000c1c28510a1920415558041c05170203110342e64943e030400151803602c980d20300400c0751000300030111141d0b0b1145510f40700f8600f104034150580c9038071220079038043d03415108414049c8140031115030b11248041e640c0d03001900d445020440322580068010010000b818210506030360b0141080080c200340034000e4808181082c560000f8000c3c4081c6407400c002514040c845440040640e8601c0e0400c20f01030500c90b00b0a40c000c0e41404c400344800090f44070002d81c803680c60f1138006040d56841c10481c5003402d4100e54039903c40b502d0824001881040d0000d80003c070081c2054421117603075440c0354000c0ca2040f0110a81040800221103c1c1c8015000500442070000e0151007000040c1800e0510325802600a41c000c034035650070507180d415040108903555004c5003403181300700b10003040c0a4801e0000510042c180c5d030701c001001084950120345800441c0e070241c1581200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 398912257 1250 398911007 398911021
    0x60d03081b070b0a0501080a03050d050618090c190803090d2405060f01080f010b0a1101020c06090d080420030c0312031f050904020d141204050a050d0308010e0709080303 75
    0x1143c182c0c1c2c20464103050070000b0908100c0400c07000740d0300c0e40c10b8440c2440d200d10442c0300b1000d840024116603102c0d40600029401d04000f904c1c0702d00c80c0c800503010f401b445504004000c5501c51065100740708540b14030007448440d00002c219a28080202c448500040c11480e2946600c0554010800e1030805e444082071800170710b400850045008684450311051048011515000220341c14142c000ca0a40100080e08030710004118030b181e989071040e420718841c01804d0a9078052707130004207258041c00030001980c1082c00f284d104603059140072407042c00e182c0c42c5c03112034a0f80d10070600784d007494030044045550340070480e0f42501e900203815101c4100420110b01000d4000311400c001c6a1800c030400c0122924031508441036032001410030943d51156000c2c0204220a05402c8a01c0d0700034520b5007180c004104400c00000344070245c00da43e21030806e03080c842c01e54415444235010b070030f103000c160000a401c0b00c401410b5402d4680d980e540c581d100c040850311440c444c0d000d2211800000b0a000007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 398913507 1250 398912257 398912273
    0x260f0a0c050108060d020306190b09150a0501020a080f0d020d0e070e01050f09042915190b090d0c1e0302030f030c030a030506031509010c0206070206060d03081b07 72
    0x80701c00980301c14440381e54442c140801c038a50324000a505400040006102110200505015007031010740083e108181c080421402030040c3c4000000348580c00d90650301c2d00d403440707000d006824207102030045442d032562100210701403100c403c2414040402c048802d100f681d03068035004519448240040700c1109603254840c03c1c540102c1c4001d40028001241504102445018002028001940302d036113030b403100f112150346201400c0b441500d080801c0420010007a400303003e0111a84002458410070040000c90001d242c0e0b4082c20b000c0100e410070901c44420140c4030ac502c0c0a440f20030041041d031810104c1c59140303401c1205800b0480d00f900410502c01c80220b801c2d02d100707904032000c007581a062540d8034055044100f840c2d6200300840c214140c42508030035008a000b070212100c40051040058011808482004403695189498800264100070f801d810281c680003070030850a082001c118403a42c1440701034113001d04100030800a240ca444240c0403c02d603107018a80360400ca01c0c003294 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 398914757 1250 398913507 398913509
    0x604170d0c0e0a3c05040e0607110d0c030e040608060a06210b070507060207150c0f0305160c1406070c0b010b0f03040b041e080c01060b0301260f0a0c 66
    0x200440110300045034050181011841c44c2d00110740c4a400c00364041c030320f842e04514545029030180d52419002981d0780301c50044914007525000036090340d1400b440e000340300d42c0c0c0e5106d41e0007542c1c0c4403000c2d03880844c0e00901e200151030307054504510b0314041040814054403040e40440301c58850001000800c0c1066030250301920b20701c4910b41b500050a0314195042c3d0352404003d000081c4d00780108200501950043c410079115200140c10301e06652501c041c05030b501d004100724951200c200d0f800d0513500110461041142d41400c010b0341c01c01c0c00c2d0402d0340c1e4944600890a02c41410424400d0200c4400a14000c840d2601151410b20b0030030401040c0640d84c00e000c41d900d4406400114500a00c0c0d0b0648800c0c0c02c901400038110303981c64542c2c0c60310080103070094601640038801400381c07042d03114040c900301c4d014503407503561445110301040c02c4600a500042c10940300b0300c01400302c0042030351501c03100e81c83d002440780710401d9604218180503151010440d9841003082e44400c100103041940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 398916007 1250 398914757 398914759
    0x309110d031d0102070e0a0207020310020d020301030b0604021201060e040624020f1f02090f03030d0501140409050604110a050a06081603020c0d211a03010e030901020604170d0c0e 79
    0x84800c0b941c0b001660f585c2d00a01549404024140016021b0301080e4040c1c80c010740018100da1000c000c0c0c1210704120b0340a240c040144503000001031092118883c1302c5a0011816a800c5107130014490030740b01600410701a010400281c403041040603600c5402140241082c00d20001400e250100d000800342103080d4030700c2c09801400d108604c20080840c04003020500400c001c8208414514900020741c48801a1540280e2140d0350030340d143c90400207041c032591000c60020340c035410700d0513500105500c040c81c28800c81c00c00c000c44000500c08100e1503001a804070b040740c203001c12200011417540c2550005500040391200000c2d0540d0b020400a000c2c04a2146a20054030940d108405a00c40d0b190401d020b680944c400c004086d129002d2074802600c0510070ba045021050034080954484140b4100c0c0740d03901c1c001c103103d94a420711400221542000045203004603440000c0d4980a0003003000e00151342000d1034618130300049045810b00041d02800704003482692801402c1d6000c0c46c0740321 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 398917257 1250 398916007 398916047
    0xb0c130f05090a20030408070b010806150f0d08090f0d2406030809010809010f020406050403050f071d07120c1d0d0213020c0a060e0102070b0c07120309110d03 70
    0x100e02c1e180302e0352060000e13895000204540c480c000da41074200c00c1c1c1c03001e0b20890b64050704000843c04038502c01c1e141070190203584003801075810b069404080007941560303071a1044407244000d400a40d141d100659025500680381503d0740344550025007040c12842116401104140c0400c04118074807005c0580d00740340900c1c000030007003100e440008136401800001d1800c2410030041000c0d6011707030420f03a404050a000400c42140e5001000b082e60400c0d4441c0020400100b006e00800a042c040e8003030f02070711a0014080c3c68030700800d0031105d10228011001c42074204004c0340709203100310b085880e209941d000034050304214440090121040020710554110307010314103400c0b8a050011548440c3d0001c00b040d03d052000c0c07241c80000e502c0304961038420300c100e031040c0e000a4540d00030550a0b0f01742d040010b84035491810000c8200340c0040400022140800000e000510786c84240c214007803103468005039400b103501d84200101580d4150b00e03030260b000701c5014101035025501c2c5158441751908 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 398918507 1250 398917257 398917261
    0x2601052b0f0308100602070311060717030601120e060106031107050601140a0602010b090f150d0b01030b06010801030c1a0f0c160605070201050301090e03091f03060f0e040b0c130f0509 81
    0x8207013090705003401400d005800c200400c00118080c1d54041811410061081c1e18014081c0d0341d054196403030302034002d580000441042119a0404a601d024603816101800100c290f166480e8960805025002c1410b40d540714070407880344008150342806500004a6910713503114003007466840000c001d003e1082c0e000c8040410440e10600500340e084001130b05002044d111484511000c0308000c0030041210710f00202442c0d1540c1d0544070a0000d405051381002e0f03135045091400d075031000181401e060040300b400400008402043c5c080807100c01d0342d02c04c03103040042c0c860000140306662100c00750340c10103c0c61042c0502c0100700620024004110914070640c1d0740c13026103080c05007403406800f02e40c0c1440104000f000941019207868454401d8a150100f1000050007203080e180318007018060261022030703542c2c1c05100380300150120880002b64203141c5896101c84010090004040311400000f103004c07a05801d043d218034011126810518545031410050b5000c084c1c0b0a2500c00c0c2c41442c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 398919757 1250 398918507 398918521
    0x4052b14011b03020c03070327030f05160501080a021c0608010b0f1c0204111905070b0912071103070305030a030b1504030c03081c14072601052b0f0308 67
    0x1017162070080103080a141001111b49094400000301800c04000c48840090b12035444c1036030142c1009544a000318490b10f10007410011310300b511707944001c10701c0701e1502810300150782c000a01c190b00000804016980c1d420100b401030f400e0300d128036001280c0e42003030f002042e040d0301904981a00c1100b40e9441890403c110300308120104081c0d4468800e90401c0c1046015041030b80010900c2000b50f0043c62511154029100090014180000c0050804541d03581041200180160400d502c1d900510f1051300407803000c2a10f2281c560000d012040da903041c1c1160340c40910981e0020341d04241980c1c0c8030070f102e45001e400750044102840c03150828040d0785070144400c5040c2c40031b0380d81040201302624255950a00d0b40d60000e1100640005054444403820140b4010703140c084032500181202800d180c04007030101c2a81c00b9800300320b06014050f141d214124503001c141101c000701c400204070301806100b03110606024060403200004102c1c500b0901006061000c01c1c0341c032958803003a0380c0d90317011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 398920863 1106 398919757 398919761
    0xa0f090e0a06030b0f0702030a0f03090b040b011d041211101a0108090a051506180c03090c0612060906150c0c01030f0204052b14011b03 60
    0x2607020f02c100409a03040c0703030304941c3c1050f502590703041481d4080c0d12400362265010802032401d152a0f40b0074400e400c50142c081c0c1051804882d0708103410188080c600c03d01038100020703440c03280300c030295005400300d41c030542d00443c0d80c2800e0344641008a5840c0400b0b54000c1c803500c40c51604e0040c8101a00c9031019014108130302503038500140e000074210140003004102960000c07242000840d20104205001c0c0c100b085030000d41e55a00710000c0c0b003100200d50050b15101004082082000d0326800850180c075650f070881d801d80c4482c1042040341e01c00e40281c440e040c141d000108446003004207485d500404002e1803072007241c03545c10202d640d0ba0004065007116034480c43c517409042d609846000c04400d1040c200358a05410100420300c1000840314080e030f05003e41303a8162400d9010110b0300c0e1910744c000c0b103103071459501c6581c06000c2e0806407606111000d1742c0c6090101240030b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 398741007 398920863 := by
  have h0 := BRFrame.cov_init 398741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 398741007 ≤ n) (h2 : n < 398920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
