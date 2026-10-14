-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1601
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:47:46.834763+00:00
-- url     : https://prove2.me/submissions/8bfd516a-a89a-4271-8fe4-170d8fb3914a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 287769784 ≤ n < 287949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 287771034 1250 287769784 287769787
    0x30506152d0a060e030c0604030302030f13030503030a020a0f18180906050703061503060b122a091e0a030b040c0911071a06010c02060306060c0a0602031e0912180402 73
    0x29194044d01a5004031200b6201b4010380c12070081515050090710f0650b0f816034001e41c2000034803026204076901c88120740000b4900341070000300044003000114400c4c1036182d000342e00c0300c070f840002070b02c00450f007070602d0280000081074800f00010120000704481d00500c45060103220a5a044000c00a4840113840f90b801e20080102e0300d50142c0100b400c42c2c46c03488003a50382c0203d100d8203d00300c802c1400b90050f8801d082103400d12540013520125003000034054a060003604443c3c02c0218070030400c0c2100340201c0c001c14881060b00d0300b0f1001880440c0c11500007080c913564540007803031011490100800001081d0089018130202d050440050480d50a082000452001c4e10b00c0171904600c0044466107a40010148a03003040c003071180c01100c4c1a114110000c14039802c000140c1c000404864202c203043c4003010100008000c1e284043d401600c00681c1c1c0e00f410440c003428a00c202080300040a248018030444000005084a400b400032140a407614080740101e50004400d2046c254403600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 287772284 1250 287771034 287771039
    0x120c030a020c0a11010906020307080a0309080c030307080609060604081203040503130803041505160221370b070305070306120b07030e0601151b0219030506152d0a 72
    0x134407013448902182601c03281e00e81e5a0b40c00c81241c0d644900740c801031500c4401c0c001c02034194081e1b00300900703540c4901c00803410441c81c1e46106145030002c8820740001800f800902010342481d1a28a4100c04256000c40c0703030078140311b03c5642d15040030504280340000000090140704003402603030b803101c1c0e202000120140d40d52405075602d4025000e80080c410600d60820880e0340542d04031800d480c1025100300c0010455000c100f030025061a0b03008200c107414032410150001840301d4200300b10300016150030509220030b10000c8644a000d051107001c0305880500c00704030ba060f60311b541700d81d0910b0003144954440750200c0140c0001e0384000b05401c0c48180e45000c00942907003061048070700750307001c01038202d81e60003903942d44000384210030b94489a400d00030f103c2882481410418804201b22000244a0b039011841c51005c94001d1502581d0081007442000424820a6081120500a1185218210005240064000c030351105111045201e4800d05007179104102e0740840c020304030b06c513559 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 287773534 1250 287772284 287772293
    0x813060f1b02301203010509060111160609031505071407060908070b0a2004050105390f0d05160203010902101e050f030103060e0f0102040f1406120c030a020c0a 71
    0x192103103410f103000340352244110052090681c1d04862004184140c1d45d00d400c001036034040c004810030540d41c051450880344950701c0c5450180280340c0c0d40d4907041c1980c61414241001c09070780c414180068240700500014540c022181408030300c514840954480380b44c0f42001c020603200d803000f00040340c0480c0e6a000d020b0250440380c850070900724140482c0d01c0404103946c21112989001401b900c040c0018816544038001804440358040c1d4a6625481e41810314100b031b0000b0901d103850030703800c0d0f0b1010703402da08144401500351035000000c10390740702c200740090030500548050085804c2503101c1034040d0f581c2500801a11341d0041c2c8a1510020000001410390042108003814944030384000c020b0640728508958860000f48a07907411a400c55941d50081e15610300402e13a54490f20303078071425005003031001b00000d0282c00c441000c080d15007440740d1b1030b00d0845101d50340300d000c1c1032190b005d40d1a02c00980c640d01c00501500036075a980c1d000d081c00c00038000d07020203645a2040b004080c0c01c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 287774784 1250 287773534 287773609
    0xe070b09011b032a020d110406030605040c1a181c08030f01210803060d02011707050c060c03060616060f06080c03070b09100f0e0d0813060f1b02 64
    0x14804e40320010403200030340003501c15246a4400079000500c5040c95008525841140b400c0d1000007400402e0300f0b03960341c1381e450546009850a0303628519008080205915001078110019040d0007903600b801030716030801841e060174542d42030042c040d45140440f010050001c9400059001c000c041c0c0300e00307005080040114090041c00c081080c243c0076440342d200d03440e0144540d590b10040c09071940d0fa9507403c2c004550740b640070483c144501c01401d10014916186510b115200c95690b084d10361078442d0703140f4a4210003030302e5111301140c00c0040c4245619185d0403030780e508040b51014a4481101d10705000202007a0180181c07071494201c010440c0c0c000420707403000c1c18004a04680710103440b03221240c200c0c070400d101281c1c02015100c401018500419011380049540d061103c0b590444501003062045003520032a0320b20000035881807001440b0403007070050266460004126940604060500c500900c1051041d8610501920071561001220b12203c242c809040186401c0d800201080c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 287776034 1250 287774784 287774807
    0x6090d0f23091206010f06120b09090a2f060a14030106090f050405070516150906020702030d02151b090307060804021309170d2a120e070b09011b03 65
    0x140b07401003c000460440041e09905841100c046803011600d0f010040d20044e40703100304080c44980340c0b034400e9030035652010380c2c034420885134015100da4400c1d03103040031405c2c0d202c03103020300c83c0d01c0790300d12000d20b50720032040b10032112100341da00a9803240d5400c0d0948421328400c11700c01c0309800000021a000364403000c1d410440301c41d0348442811a840382c003000199601102c0160004100327100d0f41003202d02807121840c2d014010080100009105407021043c1d68100d041550465000261003085040410100004480301c0c4064542203a080e1941080300c0da01914a17001c08000c2c0101c0410900300400302c0b00044401400c694020f036468402416041d400c0350240e00c1120b810790b4200c0c0b810094017a1682c1c2c00d6000c03640c016002081400c24950307422040d0003441055807200c018803961499550401c3e01c004505d1403076107201c80703054014084208008101843d5082030104032484100290050568481070391140d2103856040c0100e0304940c2c1000a1050780000c84031000505803c046103550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 287777284 1250 287776034 287776039
    0x1115070e040c170c0a050f0a0305040c06020109020907180503030301080604050c010504032f27151c020105070206030f150a03030c02040510080a060212060306090d0f2309 75
    0x84030341d01c0c803000d4400700b070740c003035505109403180000408491305107004008440460500c00d0038800007200c1c0c8002c0d500400d016501081d60341040c801444540b0203488010308944c4028040d10040d98089110118042c15501c184200754150a000c2c90207800c03040042e120107012252250394407040f055984505580a5078203001d41d070b0303c4900a5104008a800b0340f9041406408648144010034261581040d0404841b0064004610b80c9544070110701804401404061f10709680f0a0a140103a03a806040101e266889202081e8107071a00345440e0303000c2da450343d02d80310f07210040d00050313500b8070031310700c0c0250b0040c1c1c000100002ca61001702c1040c01390b401503586081c4189540d051001c490301c2e81c00094081041c00e0301400042c540754120542c02105807404014259030741003481e03d0300d41480403c079049600031549100b500c012200f210341c400021001004070303081500d100d6882d004495170030f0080040c02d10301286203600803100c91780c001140d0b101004840d15441019419604032408691 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 287778534 1250 287777284 287777291
    0x40e030c01150918080a020c0d03020120041202150f0c060a0e030406120513080a0504082b05031806070809150106090902070c1806050108010906060507031115070e04 73
    0x5004685129040f100b0300c138140030001880310381e107403540e281e00400c204004520400c849100c0c00d884031612400102e00c20b4001042001752802c40380c100f80c51130f079031400b03c0da04180130030840b0002c400d404030201ea80580301040301c50500311501d10f861060101052000c140011400d003020b000041c0c40348214903000c4104a003201c2c9000194883c400d41c80350302c0005169500d40080c414041c0c0c40590800c810ba856035129907081e03034549020b5000480c250b0301048000c0b504124015041c0150401d4500090362030790103000f1100000384810560010000b0000e0120000303d041c2060284052943da100d01110070038582404001c15500003103500042500070780142d050618800c1525038140c0f00203072154147c080c14035031140000e401002081ea50003c0303110300064140440000d050780c6954080d00451030f107060200150040f00c06034003c40550f80380c031404003c0c00758420240d480c078651628180c3e010a1042d48124900404003801404132402d2009000407242c1203ea1035012120607603051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 287779784 1250 287778534 287778539
    0x70b0103050610050306190b030f160503060606071103120403060510090507090e1b0f030609130c18020f281b0b040614090303070e090112030c02040e030c0115 70
    0xe2400f002e0f04c1040d8060b0b0002004c140304001e07140b4a40006000088005200d02150000a2410010242180b0380303400c452001d0b2340f128041161a005030109800600c403d08080d404a801e0b841050006040349030b815240c03204640d0184480b003201c02d0040320766a2a19140d051800082c0400c0e03801e42020300c804000000d81803114022184205000d880d0740103554500000c0c80704d40e203001048009040d141001103060245c611018200e0180c8841056449241480038000352440242403040f500c0c0c1d010350507000180c004034588007650700424003481300005a0707150801a000744540c03401c002d840420054802001c600302c1985c00480c0c01d400203e1150710383c60544000021410704000d02a1203188100410411506c3c40c7e04a03108410002e600c0181c40040c0b250040107444c1080150000000d020f03586500c1184c41c81020422100c1007055458800180850980400020180f11243d0103c10644d0303203d034082c10824059400b07607540d84034025500f030b00800d0300000c4a0100c10300388001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 287781034 1250 287779784 287779801
    0x305040e13021e0a05031504020a0b0903030409020d0906110c10060b09010503150916080f011503050405010603020301050901020a0809031306110f0d0503040b07030507051e0906070b01030506 84
    0x59840d002d40142c00c103082d54600c80280d899903000910f207150080050309002441e62000c10100441c2001d00c0d00d900e6607824548104401d5640070b5001c0a48030400303020b1014180e401101301e600701c0e86e99180c0140e41d1039003004100c0180180300d0000d0180d6103081100b052048070711008203208001e41c1d040c1c0e101e500b0f4440c030b0802100c40b113025031005405d0074800c2c642c00c1e5000e9070041d500312000301400e25050210b080068a04c0000f140c80c4010401020040380c2420b030030076403103500401c892440d0a059030500c1c405104650108081104141c2c54102003000c1c08001e600810145801400900040c83e02c10011070107513000d196101d00240044000401441c004419120344a28148480340c1661a20104541006014032120301c540154451054810000c01c803440d407584958603400d0301c0f8074050030184d90b80305008000000380b5007003400f0001c100e03920030101e070841e82d180d82e6810f40001c403c0d03051903c203005a0710300c213811100c0040c54809010341e4840780da04032482042110440d1f5240b800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 287782284 1250 287781034 287781061
    0x4031a16050d0603080c030405150708090d03110109030203030601020d090302030d030908120a0621030206010b030c130f0f1a0f07060b04051806011409010302060a030b0604030305040e 81
    0x820321803031210001908038a61040000781054154024080f9080b034903502e48040030780c04250400303890391002600300a030741400032410440300d400242c458140786041e01c0f10030081c8100c0e260300b4899641003001070f0400d40980e51828606c01400c0c0200881c1c8524039010790381c0c0d4020b840c820b01520803044214002881487d2403c1641e81c0540507040d6502540002e8002c0d241e081003c442c0d81d4428003c00e901c80b9011030000340b1a01d00d142010a005142040610003078104001442c10108480c000a002c2500042d01c0c40c1140d07400c200c455901c0d41e400c020410781c3d004080b6026074440d110f04000072641794105c048410f50725a150301d0140103a5444007000e402da1003200300a80001d09003c2405498408409000b1007400f50300d0104500f039400c40000d044640c01c0352440700e0007080407598190031404002850151683c0405104c04010b0100004c01141c4148402840340d400000d10102c01349c401d4020710070f4000b02500c0c8584842d220316002d09290814003880e001001d51134005803280072a080e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 287783534 1250 287782284 287782291
    0x708010e1605071401020403020d05060f06010302030f0f0403050c010207060e0d091503050a090b07020a031d031002030402040207020d0312050f0606070609020a05030303070c060e0318092203030204031a 89
    0x11140e92a02c1d03200da840c0b0042c42c21203130b848081554240702c0040542c40d155441960540315102900c0d09203420a280c0c5180790018106604051040c0304000034814030030440c40e00407040740ca005131183c0e11494100c030f130f40c401d4600381e880c5c40d400415410f04000842d00a0031303c040d0040d041d101c07402d514800458403549a0b2042d101107400b0b07000b06454480c003aa200c0c0303070070050b100c0300454503c0341038550150f04038007680d0b040010ba002c01040d00c2450781c080722a0400d060075824503000c414280001a560b558180d90107504658000f0105085645030390440300c103d40e000d0318907641118181006000e400040d101c505280d810000021948900c0d8440c0e94880e0000a0070319003464155213404d00144040c00d0308036000561088007103085d585c00c00c00303544a03580360b070303541c1240c4031940c900302c0b080e51014001640b072540f00707201e00313050400c03100b0300781c3c011180960b2114110b50f2510480c1a054a402d00c13204550b400c18000402407607030580080090720f008480356419000c0395408142401801c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 287784784 1250 287783534 287783537
    0x50105151b031303032a0c05101101060305030c0f010e06150d170a03060f03021008130c031b060e0d060c02120309100c08010b03010302100c0b0708010e16 68
    0x2003080841681c4500750640503803003007008690400440180010711004540c100790041403004c0b0f030b04000c1501840f0410015201c41a00511904940e524407a4110f658014184910781400c1d0b085c0d200c42c81140701c00343c0c01c4503210081c000c0036900e0910f0b54403984204003410060281001d483c1c603849050003004a10203643c4c0040140b980c60704075412507c0082008254440e00001c0b1003000300c0ea051016000d130360101c08a5995aa10074500a4100c4003540d108003040380a5000420160360740340e000041c06038035802d01d8a0603540307480c020801e810607918010005280c0c424003100703001541a02c9806280e55594035010f19407a0201503501e4050303503c42d030f54440c7c42c03508001d0004a15811140145156004440c0030980e4289100c505030000c40b886c0c5d01e6075000040c0c030020070140d4001c0d0003488800c8d04001d5107550500403690410303c0140030182c000c1102c061140347e6507104000f01805141c0182c000b0089007407826008000b09400e00c20f0742c00f41c018450101e0348000c2d100030b103800c40b40c40c01e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 287786034 1250 287784784 287784787
    0x42405040e041e080706050f0907030b010510050c0a030504140427020126061906020a061a04051e0c0901020c01080a110c0a05070e040c030201050c0717070905010515 73
    0x365a1946000b1510210b00c510220359110000009204c0302c000e060030750f100c0e150100c0d2514000608031840c210042294040c5d40c030411042010820851407581920026144e0305410203101d001034965200e0f11403195a64850500c800c010704d80c1c400040d005442d030050030400c18001c1c0d017013084240c0f8281101d0031a490b1801ca50f041d109400031200002c0343d4030604040d84000341d10b101260f155084a01e000e0700c28a80070080050314a006904800711018013154080e08c81d0601200960741d00c585a1300901095640301d5860080b0f1060b030345900803140c014001d001c01d02d0404400c0c1d0000d40c516801d8016681400d010170103a01c0d442054561041c4180e0080c2030360391051004449215020f440d520400d0303580d505c0401c0b2200fa51000b0501e01405400814500d4001d05c0c10a203030072019400392101800312801c1c0400515a0710800d004c0381d8091070305544907003034a10401d003405600d80c01030034058070424007045400c0380407410801701c4200703510811240e070781c03901804000c69403091040484c420 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 287787284 1250 287786034 287786041
    0x10f030b0a121a2401180f0b0705060a06080a0209100b033c15061201030f050615030715021507020c010e150304060c021f050a1b0c1412042405040e 65
    0x100fa0042c261401c6c461021a403d00c1d03030303019080c030301d9803494024500e4213400040850030b20004024088e00060310032400c02005251900c2c3e203031554000d46000b48541d03500d40210b950060710600c440f000d0002e01c02d891780c1c1c90a001c5c2c5031201c94a000e286800c0040c1c80c0380c162078515548030610f107104c600e00c444501415902c12100b500c00414a01e00c560703026809029554090711030352441c2d4080c501ca2614140600400d042c2589454001850440c422030480480d6035079440c041040d41c1141c0b580204a44071200102003a0308202e402c41e02d0590740f000c3c2d0820800d545a00003000c013440482030326940340d110740030030503c03070900700d100320410b81d104040000ca0002a4154010010041d00740b045e02c0c040e0f104004d44600c0d0405060100300065100c40c00d03c81c1c0300405101d101c1c017151040c0d6104c00c45104010b80505440e622800140400080c81009840008140420600b48000d440580e0ba01e649841e8038819003418141da0341113842901340e110581c1800781c0100e909a58108810a40c29034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 287788534 1250 287787284 287787287
    0x12290301200d0608010e01061a0307020705010806060904150501030f0c0e1e0a0b03160f02060402090a06120b04060b03120d0f1d0c030606010e010f030b0a121a2401 72
    0x1441160030040440d950600004c00050030b21940c603403083d10400110f0020300d01940c1c0140b081040e84250701101303041044c8503460350001600d404880080c00c102c07256030f0b54400042e020b4059885041c0e0014240010302990004e5040302c0020f8a400b41c070104107655610340e82500700c0d0f08221401001c200301202104c1280b40104101d030300f180c01c4d101c003005090078a4000c01e814034102d40c8214450f0134007009100d080b000a11003400d0b00041c1d851724104200c40c45e00b0082d034500000d40040d00078941100451105d5030b1541000c00a13090131115001705201518100f0f031071450443d025502039142c82243e20742403401103641e016031003000c1c00c03150820f85040070344030003480030b03191000445540311b4401b00c1940d20911904900031480020300004510803040c103007807040041030181004401c00000829a801c00640300b0700c070415142c000782c0700c41072070003140b072130f0196800007071040b56400aa5030400400015000030700c18903003001e0609440f0310110210b1608040303070080000b900814055502d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 287789784 1250 287788534 287788537
    0xf0c030501231201061502190314090d140f010b090c0a12020c0d0f030c0f0909020901120504050a140a020a06050906090a03080a0f05070506060103020306011229030120 74
    0x758003d100e800c804203100d1145007101c903240c0c000d511420240d0841c611458044c4074000007200f02060f503e0f0603641660b4002c04215000042d80d42400c004074101845841d001c0c012440e8503401610b00c0351350141580781c19503071400307403850312302e150700308810558036003040503843d8000d81c2c80d0200d95040c80402c0b0310582e030780a900700c51001410790903c0001e0244c0c0e0104812004504107480b0720000b44048000201500c0c0d0301031801c0140010314894a088540c0180e40e40c0448904410058a4040c1d035801281c400e102500300505a130f04010510091100c0800c0210b1180d12500709440e040520300d0310035407100310301c1f000607504c1031a01c442007180c10f0041c00142480c0800819803454a4100d00010381044515001910a01d5022640d0190290041c0e0b000ca07582d4191700b0302030b0404015649065070f511006000741d04064020011610306c0c1d006660001c24800c241d0424410b041001850009038182084902c4003415180c440e520345003010320907400380c0701c01c03010840c420142d503c2c94201030303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 287791034 1250 287789784 287789849
    0x50d0f0512281401060e06121e06090405100c03142406040503100c090320010806060a0807030b1512060906060a02030313021309060f0c030501 63
    0x6100c01008541c02214014445900c501003211450b0000e40b02d850650000d00840403042e0440e07807034001c1e480c541080a14190341140d0a03880d002407101c1c0400049030541c040d0040d580044254641401003100410f0001c0c400c0c8180308050160030361b505002c1051100c403e0701d02500e2500b08108085218000340c0001543c07502505000c41d400046e15014040e42000f111b403000355525110417400103101441c1191221601140c00608003814500040d84450400c8240181165900c8808028074010b901940096400c95600441100c1c041c50301d8404000301c0b40500c0c001240000000d00b00d16190341a20034607010b90b629110590344008065006012000541d640300001c8084000f544d1000320051803c0c8000702089140c5060600510500260203841c1303074400e42d0140420f20b10164000706581d44104001c20b003011200c854004100c0500c0c0d0002075040c03040c1010681004c1c0246074202c100c145080c02801c000b841494003084003194000e00641017140705420300c0c400012170180315040c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 287792284 1250 287791034 287791037
    0xa0501080a0b030a080d0209090a0b1309060b03121909030b0609070207080f030d0e03090d0b0709050307120537110d0b2a1207031d060a0612050d0f 65
    0xc0150b05448454440d041001b0040000d42c00050110103800d04002c003e820a440200910010034000c000441e41503100400803066a954100441400100d42003840c035070354040e050700c440c81c80e29046540581e100c54507800c4030f80184050380100070f02c00d0540360b00b1260001480720a54450b00100845504d02810310403c43c443c181e00418044010b008040158820700001d42d40c400d0f00b88090400d131100180509120340090118405a84410700d07040c002d1075001c0c00c0c10040303550380602641c0d82c0b48603030011034140c415044003254400748500451441c50080c4120341c6a2144200c4007001d0312007411a56066004500d4507400142c0c40d180d00008862168010040c50a58040840c510b44402c00040e81c29402c0c420a000b41c596040d180002c0c1703412015103641c4082890000f4005911450844010351000040090b544900c244c0c040c0721a08005007014218200342d0301500d80e64001590300c01d01c1c40e0300d412400151a1300488040210a6000c07014059503411044103491924043c1c4c8840f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 287793534 1250 287792284 287792293
    0x40b061f02100b0d0c060e0a140f040905070b1903050903030601020705040f0f1b0305010b0325050c100606081303091406040f0315051003020f121216050c0a0501080a0b03 75
    0x130001401c03c507509002c0d0009075a0141d03030f07034009010440324072850740c0140803000d84030032003010640310131980003550741003640c011803481290300c1e0aa2624480b60300c40389606030b010461107070400ca080590081182c40d56010b2110742c541004081c1c9910007580d4090141e400140104103904040d0003101c1f00c01121000040c1105096010005841c07a400c4c8000c40c2181d050503c00d10690180300b00c44c0506a08400c890540c540300d03c40d10103e4a03036462402c06d0380744407401110f41c40d1081007100c803c0340a003c250390b02a82240907400152041d4010480820100400100019840350080c02c0058256640305078640c640603200f10549840030405400000030031010403030841d0041c0c1c0e003005601c2459001ca040b8a0090440304030b410180c99500c1c6d2951500c401c2000d607035a260346047c201c2c801c031283c02c61764000140503441c1400d107802e94000d101c004101c44000c501c2207512111389a000d5801d6443c640401c0c82040602004c50041c1400b08801501060100030640e10005071407030040c00301c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 287794784 1250 287793534 287793559
    0x10b09090d0809031e07060c020a0b0406020d110d020a0f080c0403081c0e030307170408040e2502070503100e060f0901090f08091806010221040e040b061f02100b 71
    0x2510203c01c1800d0760035000002171b410f010407569201329040d501c50f61010781104006c0d5512000c50b44d1020700302420317030383c0c0104285c840f8008560080301d00c803200c1407907144d560001c0b1084202a41180c0c1070700d004a000b111200c0440360081c05098803500607040c190317180c03500316070b03412909411040c0880754403205500380d21844207080c814030940000f2200115105d242c0b04500034503103840240212205500c0106020000d0058400d48058031102c81d0614025a1010240c00da802c28140d4411518209418051122600400c600b001d450082e400e907900c0c800e407600440140d40c0b0061043c00c0c0d5034000780015006042185e030181d0000359050010415607402d894605035541170507010360302c40400207015043c0d071400300c0303074420388880035100c00300c2e103141440001c3c0d20b403150341c1080086101c11050600c00040239404070790207404a01c015241c039040c2420507507103809003110200e0140307a1000e4604e000c084032840f51080070030503a0040c000314020a8640d0040c240c3e40d14090780280c081840f5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 287796034 1250 287794784 287794807
    0x120c05010b090901060f06030b1324090510050f09150d17040e130b06010320030a061703030417090a09020a18050a1a090f03030c01050702010b09090d080903 69
    0x10b0390186840d20300204005040c040300701843c090952003041814a40b110740030480d15a03c0d503807011445082d200060300413824850f9418082c1c444241090741c052180b0215026070f0f243c2c00503000c0c1c16002008880651240203129844210b219280e40c082a02c2c0001004104902021041d640010b045030f0000c04869440a400c507400c0d034003043c54018041028411241c1040e80c0c20b502203010b040e1482c030f40c0d6094441c4550240e001c0c01050400d9222002d140101c540202c00740070558070a40ba6960b40e02d01074141e2802080310b4082d05919000c1210340c2e24801d031000044e280500e030403402060081410352000b003459441200c02ca90040c1e104c0070001040b020610140110390040c0c0c03620300300e95205005070041441c181d0030191003000082ca049c041d0901c20709103400000c8240002c166217000c1c03180090b40c0e0540038500030781d05100000340f6400300c190641109021789100d400901c20300803080300b0400c01e000300700c4110185500240000e407070135100f622a282c1003501f0f80700703a03803030103000d0b280 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 287797284 1250 287796034 287796049
    0xd060b030403090e06010c210e10080402040c0305090d03050402040b1c0506010503071a07050a050601080d14090d03030203130606140111030307050412050705030d0905040b040504120c05010b 84
    0x2002c0c0d01258843d4000c0080e036554005003a030141007482c1650031402659222006202c070702e180b9005404007808800101400f425400300c0c2100002c1560800082846000b415080201c80c102e0269082250282001c1e01a004450180440c9030140200d41c02d0350b5801c80040038010f0050360b01c41e40b1038110301c101d6215020039541c14942034a00003091070300d40c1003031442c21314180c0c03105000f60b012450401c40310f000050141c0858440031801c0d0754480c0035043c00d5203480e08030310010b085400307480700004039114001144040b07601d164035108802d009040e600324480c010801582e0308042d48400310700002e48039500956000004828240d00d06038641c454030115031003604001c0605c0b4544041a0b08c540e081540da4014440200c020751030343c64240ca000b072440c001d45c85800b502c2031b040d450b400100107042c080c0c00c0240802904480311881000e00c010002002d906c1494019858103460400e82e00b00340c01142d10440d001202d042d008402000704851082e80c0c00c8041d07445561782c0ca00c20303a1581c3d074001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 287798534 1250 287797284 287797291
    0xa020d0c0518061e030c190302030105090304080709020702011202031e1501031d1207080d0213090b0102030c060f0c070609080702090108071a1b010504030215150d080d060b03 77
    0x2c0b1440441c80c00c1c0b070511415003901001540040916000d810b080c0c0e6000603030500301c010136036115054501e074005ca1a84080540c00096055092908000d50b807800000604112016581195042503803092500102d21680601030300003004010149070b0f101c41a0011a0810100840c4146540241c01d141800742d40580304a45020004000340341c140d82c0c980201d00e0b00400c000110708030048040300d0b813540d8540042542c070f188100824406e00340619513003511003102c02c0800135549c4160380b40d0868205410b45c018640b14500d4458290420b502c00410749410f100100300510079034884600446034107000070700d419807082d020000d001c0010054012181607500ca0004bd58903401c1070b00c100568100160030007541d583c09940200400c552170070341c0090908982c0075869940d10b00d201c12988001c515111211150300707020031301003050f500042c180680b0700240032041c034641740d0380b00910034001d01e40001e82c2e1001c008200380380400d400070010400072054120000b1025550750f143e544a42007103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 287799784 1250 287798534 287798569
    0x5120403081005100f081803040e0606091216270b0a12080721090b030a0207020406120c211e0218180303070c080901030902030f030a1b050a020d0c05 66
    0x1285c0c03041c45d00f0035240d0750010100b074000070308200c1198145640e40500d124413801809141c01240c004e4075410300f2909400805441c50740d000e54040640707a07584413124100600c2c201c62000c00614440f9450880610300e8025100c41d0a20b84080140401743c10028541d581c071200702040002c1116850320344102061040e420300c0e8844100d03080c246126003180c8107110103100b0540360464403641c0301245409442c45041d070561a51980780c2d159000780240301d0020340083c90504081a0920285a0700d10900e10840c040c120854480c03000003e640710b0b04103400706040c08844114002000079005054000503a50b007032a900001d5000200070842c0c02260044035845c00c0240101d02a40140ea00211204a4025465428503540c01000c0c2c140d00300c4060140c50010074018066840ba801880d1401d400a0407600100030700700b52a0f403280d000643c6000820500a01480c116600a07410724106400401804141c4880d4081c80225446803034100c503410b4004c0f9001c25503951303021210080c012030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 287801034 1250 287799784 287799797
    0x901060806010b0f03010b070c0305060a050402130e1902010c0501050c09030f010203060d06110c0109050c120a020d06020309100e010911041521081908070512040308100510 76
    0xe1040c0039081c6103068000ba21441400c0000160b2950803a00301ea0458a161088503a58100c80c100028666840d400c02000ca014100c18032129414030341180b40564002c0f078444694585c46e0a0b00000c5822009492201d9088010680b4101c0c03803a00e09a01d101f4010304003054070451903900c0d40d0841c0c0040310781c1020600085040700080c141040038500801e0064021850350400d00b00080c0303180c040420080045841c0c80c25038900c4071254042d95031141d00b007030080c481c074115890b001d5103034950b84c5225401151200034180b0140400a040d50441da00070700503450744001c40e29504041d500023441010248108111400174400503c1448003403103040000103080f61203843c20905c268541c1c170006104509003403107030018018203101e040031601d80c0c52071000000b004059070101b0350480f0502030000070340480d6000c0134083c00d65013104c1c00d0040350358404c019a1001016a0107000ea00300340d1000b2252400000c0010703001d8404160006148600380e5440d03541c400001d0706201c402c4550034001042c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 287802284 1250 287801034 287801039
    0xc0602071b0e090312040602040816050f0409020109170c0a06020d1d010e130b0d0b01030c0605030417130e0924131113090b070801080111030411120105090106 70
    0x4207891600a09070218a0700201c0c00c000301010351300d002c0c43c03055890503410200800d081040c00c0d41102e0080540006135004082d1840e420b040c7c0e2400340c89007a005415001c8a2246440e003449a01e015550503114402501d062a5506200c4d0300010801d000d14414280036044580d982100070004103030660007006181d0b03000c03c000307041080d8020307452070803440c5964002c03d41c1c2c0c0015441186210a5503042d141ca000300d42c20070050016254440c0d084000150307500c3c20f0140b4030b00d07007605032409140c80c80a80e650b56002100c441c441142d01610480000158001c09600c0b50020b0142e002c180a001480b1625461034400480c0156008146c0c1e6100042c0903c2201c143d42c64090568074020103c00a032030b00d03a01094243d041858000c12554084000e21456a41c10b210040c8558603614100b080303513042c0c50292034000080d140c040110f0101e20000524000502810794103424a552041c00c0d41c070340782c0d0f480f840b07988004d03d0607034000751700000201c12090921840d4490b509413400410000e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 287803534 1250 287802284 287802323
    0x20a0b070302190308060603092a03010b06040f1802090a0b070b1018020a03020d0207030e010809060606180609030d2601080706080c0705010f020306040f0b0306160c060207 76
    0x24100829032141c000f41e0590080425003011034550312010a6540715604d81e00c0843d56810810f114603404941c90110307041e95030a02d06209503040c101c4040c4c000300060450318007006000e000d03a1190010110b0040300c1405030012001c0c000800302440840541004030100005200c800b460304501d04c001d402103840d80502020001050700300c142e03030503001c403028102400030f001030120030300c501032164000a8490702c2c94441c0c0c0c101d442c81d2261600464541427039103001400c1c1107450090318006800c000105140710400701e001401581e009040302c0c500441082c0400c1d09501c0e044e403940e4880e4045c4040c2140d500c051000c030181d02e0341c0e565011480030268113450340448904042d84561000d4070018048544005242c0c000d0b6041810840e14959800103014210321130050010555420141500760040ca284c0203980240340c100d5081c01200d1b02c0c10010011625446000f1b41c2c1648060040794014a100060280d201179510f066480031103c0e45a00003607030301909007204c2d007000e500440d14000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 287804784 1250 287803534 287803543
    0x80a080703200d08090c0307080a05010606021501060c03050f030414061e040605040203010e071719021309020112060e010306180b07080c0712050307031a100c0f020a0b070302 77
    0x200702070b01d080d000140107002d055079a1a24540c100d414011480b010400b607079020081120301c00c0d001401c880d1159101d801e074507240c150400c001c072074642c01c1c81801704e2660300201c0c98003038518442e12000e07541ea01e00001140d4220b00c0c610240c060103420040c03800d0130b410a20003184594043d152480d10440154011494004010403d0202d0181e080390504200c86003041d00c3c0e082504102c01107425102d5000007070061502419001c410701c01d0080020b1502003c02e8115504881d400644921000642079244030740c07a0080029400401e50044503204803040d8445c54005006240031821208409038000c212241c9400034024081d018004204001a82c082d0854240c0200540c0021004a81d5000b20b090b41c00350000c024001030341c002400e0940c84105480440f41c021602d529000600c40020b46250b00585030500001c1c20080c4090000040310319411034640050424154460888012181d0702c6182404a510040240181d400b40e91038502d124007501d0713041c0e14541d5401d1039181c081e103003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 287806034 1250 287804784 287804807
    0x90607140d121a0f13140a0e060f01090f060801151a073318050c0a0302220b0a081c030504020618040f06080721080306010f09080a080703 61
    0x50380e0801d0544180204809080041c0100580c3c440c4e1000d29401d00240700701c040e110544180c1403030503421078441501c0080f42409002207400c100500300c0309000032a254101100e980608503081e4004010340411030740040b01a100d503200c009540c0e41c0380c13800c1ca800d4528800040303030141900c0d10b0500014902a6881416a01101203580b804000d0fa40341d00d0310a20483c00d850107441070030310840d5001c4d42c046d6807180c500480c03142002209945880c1c041800120745003621a44201c81c0c0103411800c042c200041a01d030010180e01c015030070200301c220441448141090b1880d280d03c0704000300c4c2c64400801e8003600e0760074040c1034502c42c11811700c0c402640f88100d08041505100900000da1204c4003100c0b030743d00110300c030815805a041c02040250101040d01d0203054500100020111008a800d906894220300a04035507200810044601404c800019002c0c036020804030f842507020301144078440200381411922035640d003520b2800c1074404601a00c071f0f2103002880c001016030101a0046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 287807284 1250 287806034 287806067
    0x12060702070902041a0a0c12030f050703050415020c0a1506080d08010b0412020604030816050105060f0108161403070e012d12061806080d08010501020a08090607140d 73
    0x70680b6000002400e0301e4109170380c01e1460400500050780c90322448441404035040030502442207059034000303000b00b5111354064401c514160115441d02e119000e078501658000c11000907815440480c0700003175001c50000d03074062040003a110001021202e10020105000c030000681c81d00c0c2403029402c268503644441f007088841c2c401408444125800d807015161a004d47c0140c020041c408102d2602c52a040074003070340e0020500b900c05a4100c601c40107440d100d00000c5c0604d480701c00a00641c42d0340c640b049408030b0102d80006101070101c41e90100f480610745040544000440240c40703840d44180d995030005045000460540d5030001080c044240c4080a4920201403032808102c140c21806050010071a1001c40011000c50f56040324014000424628917142d20004101c0020145e51007681140e010306a4100c0c421350248407242e0403100c041c4c001c1c0c000e210300c40c1c1d540340703540e40100c0c103041c0d0098003402aa1301080305600b0b034040c0b0711001801840c0b003103110720019002c61100c7c00b2004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 287808534 1250 287807284 287807287
    0xf0a0e040605100b120a110c0c1203130b1c02070f0c0b09010c060c030908190318020d020607051609050105120a150e030c0d030b0913050c010806010e12060702070902 73
    0x144560103084903407008441d1056106070706c0362a11030b00500032840720400b44074408247d58003424408102c80390403003000c13103150058449203440e46440f8000c200d40117101da0420401007022034002e40c003c0130541c003507011711074002400d80245001c90b0400c070001e903185141e0504400400000c00d40b0360b40a01030342900c003401d00889500003000061034801c000c003016100e281ca9000a40a40c2261860b00d070b02c1607850b902d1380c41c0d1218a01044051411440001342082420301c00c52403800040072140e07802422444058006070240702c440d43c419007040341c40d84201c0703208030405a40f107500c44003d007070700076404901c551500080100640704d044225810b604031b0307060440041c3d000d50b07661044011800c130218580140a24050450240d907881084900032281c505840c143e0561000680303240c11981181e46032225800d0090a41c2380d50801403940d030103c09086490343c055000142e21800c1403501c1202d403890368000c038001360314804216005600900178001d20039010701408020702101352046 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 287809784 1250 287808534 287808539
    0x30f010b0301080a1e0203060106032304081602151602270412120608010509011b050f1b0109030c031d0102060c300a0b0105090303180f0a0e04060510 66
    0x450302d03103907507101c01001d84000d5564101c0005490599217904ca030001e058900642c1c1d14540500580410342c1d81d0303120b00f0815011540f400f00c02010303440c01550070844680c140001101c44d15083c501512041ea80001e044001c2c0c04a00428402002c041424041d940e40f42c2500d8818800e0f409080000c1c4103000c0200071020381d00ca07041a2031a039001c4d4010503000d80340300361790005a409071050300d12992a24100710b0082030100301508803034021140340f4002c22a03020181c680081404404010794000343c020030034200941c90b1f410150619002c4019420411442d090b41c42d821117400038011008910403900b03032018990010944e42c0d440740d00f00c084200480182c00002c2d10f40303000074814580070002141410107004101c2c0c3c500d4569022a5160b90981c2c01c00008000170a012a10014491b040504050495210b04156010841c0190040d030502c080c0c0090480040c407184180d64010348270031074602407903407500b091400401103001100860709280c1003071016284000c0030000301664a003401c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 287811034 1250 287809784 287809799
    0x10f05071b02150c010c030b0f030a02090a020c032109120c0c0d08090307030b0114150901030e2104051f08010b0c0106092a032703050906040308030f010b0301 70
    0x91101c1c0a904999146074074082c96a0200c1c24018100d810405600e49081c0c9507005030554001c078801001201c0d2500c214030305804055540494280094115142c000401da544031550003401030000f141c01a42c0c20300d00c2107440076103107010104401504050520070300880351800d214542c0c98000b4010254900440c0c4e10445540c0c440c042082c034001e122100d1418103001102c4180c44090710001e054500c1a80d0340d082000c031003102805401103489041c041d00c802480e001040d500500300c0c210b1000e0030100350b00010340050034514409422030064070000301c1d06601c100c0040ca0100d00080d01c103904d8500305400d100003c1c1303011840411401e0000394910070241c01c039106504540043e610035035198900e00d201409003400358803420006007014400c07074104408090014145154000810b900041d0010403000d0320414410000e205840c0c40b40c203c42c200300300c00b030001c446000381001403401c071282c004210164040e60050300c1d0101c2c0802400000d0740024107542c010f00c1001182415541402503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 287812284 1250 287811034 287811077
    0xa0f030e031804020912010213090203040c170a050a12031d0709150f0801020927010303050c1219091517040c050402120a0b04060f030803100e09010f0507 68
    0x741c04202c01d084020008a82d9a540403607a00c024054102c08180c0b5403103031042d002c1d4000b0303405c5d00e09030703507081c000450040c0943c800c4e2403056402000c4202c10500c1e2000c12080990558114103080c054840108041403041010180451041c4092039504a646030024120b450007030301020341c003401480c0d0075010400020031100ba200c000d000001e54000c801042c81105a641d800000310b4048044e002588a0066004d88030900c010759000d20100031030361000440d0741c400c104001413500c0d8800140040b91250003d03200c810080e001311450404c42880c0c2c0011a00003103c424208502d2010503511142d000740088010043e0020058000c03015040c0940307a5804002e0840800030404c00140c240050710205000500c4040d00840d592a06103103202c0203100c0071200e10006900b420851500ca0600d40700f03500c11120844d20120307115080d981c4500c0580e00c00750840c840c030400003402017082c0d4203030603200340107905c1c1c90000180c01c40f64501c04016503030004d220106200082c0d00000e4200c10002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 287813534 1250 287812284 287812297
    0x9080c0105120c1902060a050a0b060304030309050123011503110301060f1e0e150f090409080d14100b090f0105071a0c27061b070b0d020a0f030e03 65
    0xc507203402d1580d58200d103168a00a41d00d000c0c40c002c05407186420000d4001c00c10354046c4074001e5045c010360750707a50361000549031040109600204100009030110788207501052107148202c00219441c2c54211b010a601e2407031001e001c861021003801040340720312403004003403036900c03a003428403268006030201c3c20640070503c581d00078040d8180380000440d03c540c040307c070300200c03401242c0c5000303080900c0140306090124045000790510321301c0c003540e020710805603207034512406680380c0380c44448002e01000c0c02e0400300459800005016900603941c1714000c14407104502d01600c0101e1900030340601310884194804211602c0030488808a601d4031400350445d10020b00300160341b0320b800e140c241d614030103c141802d070180b101400c0c0491051000018400c07601281c2c01c14150400c0d02c06d90500001500070081da01c40703010012071001140200d41200b0072624481924801a40c0300140c2d01c03d680049018804103500003071450402d60054054030a40c02185003c00842c41a041c40035900e10446 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 287814784 1250 287813534 287813557
    0x90e10080c1509100e0901030c090e0f0d0309060902060a0206061323091e07050114040b030601030b030708070e0712050603060609100f080304060201061d04230d0c0309080c0105 78
    0x103102c680002ea000300402a1245c4000e80b1070812980d4034100402002c507a805619501814045000611000014503902c00d6191401409106013049010383c005c080b0940201c81054842000d8005a41c8160103030000061039006403000d0328085040105024410701014040e038500400c50a0044684141c20318003801500f6104c00742e11007140344da00c2d1002d2401010310050303015100e00c20480002c9481001c5881c2a2036200c040380c0a110005024061400744548181d400e000040c2290312a4200e021030082c0070b0140c441054840c260303036080c440542c10040d1146526400d20101a900c130b21000c21083c4004001c02243c1084000240c4401c409022180b00350410404100941ea000010340000e090f82c00603140150b640702021138130b0750480c1c41484055442c10500140d241503e06a401e421400e50114210550b02d96846032890801180042c0c000480d60050900700d000c1040342482e058a50340b40c121409807a4a0004d0007500c0b42c0d000700a00c2d40014400510507604032042d01c8802002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 287816034 1250 287814784 287814799
    0x20c060f07030c15150f060201021804020a0e1801260604061109030d02070312020f0303070f030f050106030902040608010e0a110d0f29070e04020a090e10080c1509 72
    0x460404403022450302c0d0380e10101e9464802c02c03443e1704225803d94011901c2c5260003401e4242d07503501c2a400c0340074104081d80034030f00400716030318940f40c298001c0240001d20b01b000d0fa9510150f0300030800080500c005140d07040244001400b00c20503160280412080c016035a5a855000c1c103160768440d070000e48028011911035103079040340c0440c4015524018806411126081d8003880000e503540b01c5444151204000d0a200c015110b2010840313680c1d00800500840c40c54440f10030844203c00c1400c1041d08040d82e03808045c096482134002c4034002c001e155804248801140100412a2519800881c19a00d01180c400701c60340e010603124440b581101040400c59000c02c040f40150321400c0b4001d00032100c0002e802c2c1044003241c00b0416103030100f00c20302c0b10301860080040c1202010384019000c204500c1045000d0f16068008102200311031914281c981d607102462080d255050798042401051504107010003c0c0401a6459100040b520301d140f08a0201f006e05183c400c5210b4540500f90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 287817284 1250 287816034 287816057
    0x3030b0a090507030207150c020c150d152303060604020705030f0d0c020f070302010e1e03010603120e04060b040504110c030304061d1f020c010b0406080c01020c060f0703 75
    0x5602414000801c1400d405000d9071074420300c0100203610100b02140e120000704024001e0440c00d100302c0048a40c6031b001410820b0301e002c200000d00305c02402900c1c6000c410842000380002e82d002d00d84045c4d06d2004010700903400c00405440414a0b001d40c64418400d08101c642c40750380025135141c10910544005a581d0a01c3c10105e0541c0710715000d810109100080d1540c00b5895a48040501ca43d15800c2e20481059002d05030f4503440c540c0f202034001440c0b0041d0750b100e4941501043c0f2910321b00100012825030f040007281c2516466802515000f9801c0c0d1801043c80c0c1000f0350040d807100844080052500b0403440c01460300490282500907952603040d25801c0d04440d0032200b07000007880481e5204c0c5002d2034078601901d6804e41030303910102015858801070100092110b125010100900f96129000f042c1d50002e4100e40d0060240759224102540b294449215510152400b10701030000d00e031403800060b00c1e29030108040c9014000c10000301e00240314501c06e46040b00e0380351070300301d03550031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 287818534 1250 287817284 287817289
    0x8090d0f090801061e08061504050604180506041704050307030f0206120f060f040c0806100306050a08030c07080a050a030c08091503040b0603030a02150405070f060503070801091803030b 82
    0x31000e03080310095600e440c0002c00c0c05c0c0c0543c3c502050f46180c06420705003045c1c41c0c0c84c00c50707190282500d4030140c080d003200e60051503107071541041e548058081c00002d0082005409100d951001e100c054076181c003e1800d01042c0b11840c80c1c4000d2440c0442021494a031130708021940d80d5505100c0500880d058012150441d61504100c900e44066174803805028140600c8105c40780034207039800c5204003400d0305c9085003400c140c05a51500c080980f10b0349510f698820a00644000d809594000c0540c0c584020609943d4440108041d00982c002940c40345160100c3d1071030f00001f60028a40340e403200d408000040c800140c0032070f0981d89443d00d4440700b403962034900300602410311142d03800a050000003440c0c461030800746226078001c0c4c0a0342500d488000c1417584a1183c02403850042e0000600c5140da032010a140503005231050041391015030343e940c44249a2041904400d0001d000003040c032004d20303800a000d6014080c014000c01c00c045500381c1c0f0451588c3c0c411030081c14952904010740040e03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 287819784 1250 287818534 287818547
    0x130c1211190809120c160e01030816060b061603080105030703080702010c11090c0a02100524030a020312031f0f03240c121d100902061b1b0108090d0f 66
    0x5020a400c080c0c0b61718201c0a03c5482d48411030300380301280c01044c800903404c0c0400055604aa800240c410714200c0050113a074515406480b046c0c40413a01c40c0d020301e02680b43c5100a0140d0300c180c462043c8a1021894001c114440607400b0134440d0344111024030101c1c10000898821580c242084a100481482c02c85012240d10140aa0040054080001070384044005000c0071489034255a00c01c2080c1c03e10404558041e03c8604c6000802030b01001c0c00c042201103425403900041c04c50f1041d02c01580081e241c000164078851001e4004800d11096024150b05609486c4080f02c000041c1c41c28a1406c58001b5103511026080442460b11042d42040c49a0109803c0402c88070a1244403c855000f500c6600760030000503c042c9003007100d486c01c101c10301240242c11401c002a04101c0d0b40411041c000d0051007100b603034000d80401040845c5800c1003d03504900d142c0c480074041c03415601c0040003c1c0700c40e0381da2107414040f0a20404c41541404680e4100c5100d0a01b00003600c00034440007100e50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 287821034 1250 287819784 287819803
    0x60c09010c0c03140a020901170a0204020a0912080733050a090f1b050607020105041206021210081203060918070803070302010b03010605010201020f1602130c1211190809 75
    0x2007804c0c0c0342c01c140a40008900e0100c1d5500030340d002d444599884a2081d002c9050001082464010950f190700525082d001001c803e0468601042843c2d180c21907c0782d00800080200c0e4000700029255080001c40030340501010003c48048180c02c0180c1068171400113a010001062595840000c82e007600c40e506c03d07142c55801c16000411260249070620400c006121007584034459040b0000302840e0000c2140c0c0f00c1641a954141411702d090300c607903550750600404441c819001d1005070303c10720400e04820b1003800100e0405504510780522641007403100c440d1900c2c142800c201300012038488049007600080391200c95000e00341c4004810f070900225810604e15230100095010615505402c400300512080300200195030b5100c00580c00c038410205543c1c0d03a020140a6545502a00000e402c1c15600180240c410380380d0300715402c003c5803601032204c004100540115403002026105031401c000c82c000c107103440e100147c139040c0d0901030464407200030445400d001600b4004107010010a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 287822284 1250 287821034 287821043
    0x10f0b010c26030a09110906060409050a11070309060f020c0f0d060e0d0908060606090a0312020c0a030b040b0a1116080904020c010b011202030708010512160308041403060c09010c0c03 81
    0xb03d13420950440c0c400362203e4a015581d00702d85400d40502c0c1c1c50000c0c43c0500a10004100c5807070103150101c07c80c05054018079451109a40c0c00ea4035400c4048071004104043c030030382d10440340504245002d020003503941c000358110340c040e030f240840c561079285040000341380403500c50550300230a14020000d0061520300812034081c5021007134841d43c000000905a0b802c0c40c003500e02da030751181c2c02d00100b0700421901035407182c05003408201003141c01c011854a005644140c440c5868144085806071510b0707030080750b91003035502c1003109104e800820340750416210070052101d00341c19041e00e855809012000071b04101a10040d20030418540102c480181000e0819901c8040c0303600101d008150bc1c20360180402e40303d940c0450311f44da1074400c481c070401e000c0d2218603169003011f082c45820055219103440300d2040004100c01d010075540b1040065118019043d9241d00340504581ca054003160080c0c003983c02141800244a44141501c0d118042840c11480345a0301d0f05040c0c0500845a00251 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 287823534 1250 287822284 287822287
    0x2010608061519061107090e10050709120b040b07051602060d090b0109090c06020d050d150b1216090308030a090f140609150609150102030f0d0e010f0b010c26 70
    0x135515803c6101400c103840c0ca00f060313038511540e038035801c025111100d890042c5030300400d400c04040c400d0b41d0700079900600d1900e030010102340c035626207000001d4028070640d90081c00008100c200140882c0036130341300f07032145001e504043c403c80c1010960750801c0c800920918001c1040480807000b0350018840039040b541c401c00c1035075a86c442c0c41c0141982c0750103071001703051908041001c5000050180420450350b681030301d0311a00040c1c41c4020701c110340144039004507140c800290700318001c02404900d605140f1aa49904106000307100c0440504001c00a0024103203040001c2a14401a40e90062000501081c018082c1c94803440c16120b0780d200414041e50341140780700c201c1c0000342c002d208171815011100728401641200750b610038125101940400c101000607000c020503e0382c28241d01040c011241000c5c4010b800c84c1940d00000301c114040740d524451001000f4090240c41d40148440b0300400039040c0350300000f0301d03902d42c2c110080d0440801c2c0700c9010302d010081b1400840c140c482407040d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 287824784 1250 287823534 287823539
    0x1f02100504031b060207050d0201020f120606160b0609091c1206030507081501120b0402060d0b03030307170109050702060609041104050a0203191a010f0201060806010605120702010608061519 84
    0x340001c0d04001b0080c0d03202d01c42d0300c4064481500510071203125000400c042400c10180d42e0445444500041a95800080c05d001c1c0242000041001e80341140c81031100184603e0403106014080c1001001210150f00a44480240182c0000701040350500c0d40723810558451000444400350086e80d1000741648201000062391510110b81010440d249004c03442e0740d81d076170f2500c61600a00c0390b080034012821100100d001850303d040207282e11461014003182c50111200003034219041100c02002040004000c0c4d00340d0118401541d0251040480030000390070720b401c0c001d5507084000c0c6500e01a0200001103410301c4942894480c2d003100041060040717180410a801c042e4100b036500c100c1510200843c07000c030140c6c074002e40e1604800400c04c0000c0d071124034011194000c034610300d0310a40d50b88000214419000340141340c0030340706644541d0340d581d0407040b85800c0c24200500150846e4500700c420f002210000c03c0d2507800c482c11300c00040c102e5424100042650107000e0001c40c2c00300500c21300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 287826034 1250 287824784 287824793
    0x1050d1d0d080907080709320106030e03070c05010318050304090f050c0703020a03050f04080709020304170c0703020f18240301020702330a0e1f02100504031b 70
    0xc146002001da0b0703041d145440f20403c0560352034060140000c10b40000c101448840d0300d130381c440e14005404001d890600c0024a03400504a00010000c481d0000600d005101e001d405000e10200c65815000031440e250130303520740b002d071220b940c010141095200e8030030250780e29202403070000b00e81d0014296a580c039600c080c40001002c4920307041c681e0905010006aa03240090165404140c158004d000d14902c959400c40b480d81c00b488907111a01018400812000420019400a891103080050b903a060606081c60141e41e8103443d100400410402d06c00e500c4000705110b0b0407280c0c191488030380760703e0500002d124803140c02d09046070301020b01c04100060080e000c03211100441e082040c4003030411142818280d1003058400307500041914052010070f0030780304020b600d20900710090020060a041e1410031944150440c5e00080c1c000c00310031031186000907100003124214007611131090021040652103c030314400b00d0f40426502d40c00102418001d95107100c0300140d035004011701d20514a003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 287827284 1250 287826034 287826043
    0x607020120011406060408250909080903010605060306030d0f0c060c0c230312060a050402040f06080105030a0b060103020a120e0f1006121209080303040b060405070e0f01050d1d 78
    0x500f01d00010580000c1405802d1440071a030555458002402021440c5210000c5080782c200542000841652002a81420520881c3d240e6445407041c550740b00310b0201010f080d41d8654020a201f00010014001d030f50f030700040c400e8030040039814400030100700c031001a220a0085c12001e000c441c185094680c2e802c0e40105040d2080344500d100000003103250705e042240c8407500d00064400da108102000340c40a20345401e50344440002d210340c421170740324004541030782c1040c2d0010307449102c1c9003000c0c01800d130854103013400b42c00d069008100c0c101240d00c90054001029043c82c4c1415130000e14512030500c501410f00c411000c405d02800481c0c0250515a568001c20b410300141c0d01404442e40030006a0b0700a1070308032078446202d044141c00700e480304c0340c0182ea8001510140300141c100064139640a00c00b951282d40100c20701d40480c038140060009030f8900508410400c400c1210700d001c0355076030a100c092025001c0c640141c030340d860784210310010241844002c1180c42d4404a8480c420030019 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 287828534 1250 287827284 287827301
    0x60b09010f02010908180a08010f32060108130f0c141c02010807120e03090f0102061b03100e040501051509040507030305130504020a1206080a030806060702012001 72
    0x280e81d0a206440900e08900300e50320020000d04900c820000040342e000013898204280d034008102268940d680c0600508451540400c80d6090303032114200369101d0b02500036030807035401800a001c170f00864950900d0040c5e800521103410300c020080880c05000c0c54043e0510069445204180304000d1403d0180c04400320784500c0d2410281c00d942110181480d113a90111503030350b80e0751008080d500742d005507541c000c0207000c0800c0000c20b04404025800900031645000d0f00d01d8061642d52000030b0038099103228064000c1d055511400c180004040701c4001e80780010400c40749282c4070303201e10300f0207000403813076601c0208035845010900060001c194412401088001e600d92003800303030b00040c4000341c0030844028105802c0039008001107405000103004007a000740000440d182c9540004089800400000001480300b2044050302c0c0703100c0c445d01c400303003440c070000b00304420950340e00400400009001d58000c0d80007181400031640500c0005400d4148100c0c4101450302c0000341c40d00030080c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 287829784 1250 287828534 287828537
    0xd0e15190c150f18050c090c07051603020108010509090316030e100206100509040b070e0604150507050607020613030c1a1e010f0e1812040b0a09050a0b2b060b0901 72
    0x104240441c245280308044025601ca006000380440c04020803207c510b000b4001d03401c2d96000c002c0301e40058420300240300f40081804c1004045401d5000050059005801c5507001e030600e00b0511005432030000c240c400c2c1c840c0420b1010782048030340c6012110240c600103255000024405200b0080f600860061701c200020000c00d0441903941c0100000b611096030003034203031204d4a02080d034052044244928213440502503600d46950303110100d03d8500400c800d2070008401046c00c13020000c0c2031101c00d81100c0340b48003c140c07604000701c6080001c115220001d0500081016400800001d100485104110482245203524040d181c00c1c0031440f01d12181d104e00d180d440004a5103403940350041c4142c81d40c140c4000790941d101c21812040c04031181001416105032413050500041301c9004002901d4400559500c0d5100f9020140c0426820b400c26889a4010681407007107190755810f4505943e800040c07020640928040030381018440540801218200000858840c890038001c1840e85401e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 287831034 1250 287829784 287829791
    0xa0204050405100f06050307090f03060e010b01021b0f04090503030a020c0d0f020706200a11010e0f0906061b0a06060317030402010e060d060806090d0e15190c150f 72
    0x3064094140f81101d4041c001c080c511048007405958851b00281d036205045003403d1400c140c4845556403401d800742d200300c1d000c0c0c0d114003c0c130a8411003030260102000081c0002c12140310300c031502485c0c28401002c80c5002e4180c44000680d1035880e600181e01841d0042c050705ea80b41045034124002c3c0d8004a040400e0384941070100060510800d41d0743c41198050380980126414518103c820b05810311190307140d00344010343e11124010502c10074014610030101000c19030341040c0050000548100034600c6040701d1982e4080540381d4040c0c10f0f911800840300c031592100c00b900b154144a090844050b040e210f00b0419404201031a80030700c099900071003030607030540d0b2030303844103600c43c0301c02c440007070001d10030b0070b56040f1a061600103000c1e50302c454440480c07141d4030743d000d03203203800c000302d410102d1903002c458030070000754112040300e00d280c600352500207482c1042d0443d40003a10595140241c680184031000e2441e500c41c030007040340e095001d1405032480500045910140600f590a150010f29 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 287832284 1250 287831034 287831041
    0xd0b010e0105100e060706020f19120911040534031103070c060906110a0804150b03030a05030601090b0a020105040c060f020c09090703020a030c150813020907170a0204050405 77
    0x80c07a55101c20440d0166482c4003c158804c000e0042982040c8021609550240603160003c070400000c2d042d020b0903984080b0310103900500041408a00c1e8030140ea449250070300200108044051070320b04604162030110303150321001c4000149003401c005032100f83c840200b52151100c1d05034030756601020310355001d005892080c40c901d1680e200a85036000807641c0615510001003641d04404d1000d4010507000070b807a5000c03c0c19940d903500c040c0c007400c0042c4035101080200500489101c2040e94541030402c40500b101001ca50f503445990000402e00c03101000140c8642e1240581c9400b5000c043c03c0980c5070311009001038041d0000307903812206410380c0c100c0481e000c0d100d039040c1000d40d48540e0050600c0d46a640034491552400703030040c41680210750010016032180c4803140006c40c846e034012031b01145000d0b030515980203642030351010840301a00b448001f071204c4e9a82910f00e90120384d11859501da01d08103680050f00707135104001800341d0900f0442e0200b520303030207401169400c0d10300380202d56 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 287833534 1250 287832284 287832289
    0x10312171323010b0307080609061f1a0a0201050a1407050a0e09181c090306020901020a0f08040812190302030709091404061103040b010501030e03090d0b010e0105 72
    0x84649004000694180000500d040049600261201c1c0a07410700445108061030800b00710300200042d1490380e4440c001072943d0b0504010140c0102000c030060032450800c09a41912100d000d4070040c46500c1d10050074070403003004803152005080c042c2d07121f601d0150508601015410000c04400594a0140040d804031450300400081c1d040d05102c0d50542e85d525031060b1761325040000c0040070003100c8442068952102c6d5419401440d111300c1c0b42c0380308105203000700d18029103400b050780880501415045065003000395070041d241d00807009a1a0602a00100c0c0380c208150400780c4061681d0390380700c003031050a0300104256034000c0144c070b8884041800450003480b46020056820804682d0310071424401e03400b8541000d003e10f400c0741e4407540c6503103500c1511078002c6110341c0d0710032146c01d00040041510032411641c940d070001601b03629242d1210610f4420510560b418140c44d030081e4004a0b00a10480701c0310240140002e068080d103041406460300240106d0950308034483c008151351 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 287834784 1250 287833534 287833547
    0x34140f04030c0e060f01120203070201060504060314120c0303010b1c050f040c081f02031005030a05010c1e0e0d0501060b07150c08090316080f04091505010f0207060e0607080a0503010312 82
    0x5c8040c0c58032602c405819410000942c0010324010031551389410105031035680b40180b4000710300540d040c820004030146130760300f0074150851440c008801000042403c075004400e80781107812000c0326a0b2150ba40f02000807400d2040d0284400081c580401c0002208001005a000382d0203203145000c0540c0f110a419940c16204180320182c1103000603101d1058019001150310038140815541c0d020380d10404285868100d24040303c0301d035103451512402a0f408286010b415410620010300d02c0741c01d010107031905200c1d4003094010307c040e00b100020300a003508004003c00c0d407521403aa9442030b5040c20b1044000300340658141c603050003800c1c02081c0c030a4000070b0240c11400e015516001c44010020002000701200710380340c20080c0300c1070f00b8900e10342003c0c00080450403004944c0c03400d85604544115055001107051064145082c0c03030161b030024070f80d401e49190b420300d801c0c8080181e000801078058408003c202c0d04000405108081e440009907040780e21840303800880da90345810640b40b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 287836034 1250 287834784 287834809
    0x9030906020c0a030609081e030f0603061003020405101505131d0c0705150f09010c020a2604030606140a060c05030910170103050634140f04030c0e06 66
    0x31800000c3d050001c01c41c3c2d0392104940500c0760003028039060050200403480840b1504030414000044200000072482801c89075000804401030600c42ca031640a03901c10a0130f601020340169034400004d0a00282d601c000c4000e08200300303003a0310b480c0c5084401001030b4818190010620703a078440c0020910148040c08440300c004001d504d442d580d8094003604583c0180ca41507038248540d081d0300d640c488e56420b6642c0505070303462030001e4a2030043c0149007964180c20b0b182003158012841c4501094618001400400c0d1365581207085080c0b0302d80c01ca01600640d00b020780310b6031901000045010366003d10071044074080d0350101080e40d84071002d0308d80c0b0b00c944001600136001042140b021b840d00c100548250f94441c100900c2c100b1500c42d0a03092480240c008860741e0f0700c401d0901200b6408010721041801c0104440c2d001cac049c05880e000442c02500d0810002e100c0007840f20022864024103654004802d030b4005511141e41e17042c00200005070344a100ca0900350340740403540c0d46c148171010440c1d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 287837284 1250 287836034 287836039
    0x180525080712110114040605030f010503030901020c010305100e0c070b0702070803090402030604110310091a01090e090a050d03050f01120f020904060e010c03020909090705150f040e07020109030906020c 89
    0x500701643d88912400ea105805200d04003d200200e0f1603a00100304003030005040142e54107900c070702e0b01d00c1031031400d110103070030980c442e41c020700443c612030383d00013140d014074a028a008119500c2e142140284c040d007a80099002240007410001c1c01036120018042c0c0d03d0280149401740e454081e8141d0f01c501c0f95000d040c5040c1c104000c2406142031075001560003241c05480018114401c918040343c680069503d200f012403d0141088204040e0044c4d501320340c0c00e030302111b404e1050140083c1c40e00d000c5210301c042d844030050000e8a4990144540310207143c2001c1590307855101c00100800800007203884111001e4000700128142e085d117001000e8041c0d100400b228682456003c000e04031074000e0084400300d860705050908400d0a010702c1c100140c59490158807130b107806c0100143c8d035100a21058140d400302204003c1c694a5141700310b60b00380c840700741541d690102c50002c0020f11480e00400240d400303500503c01d620f541544010412402955800355440d1a01340803601c900c50102582c0e0f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 287838534 1250 287837284 287837309
    0xf0303020d110c060406120c050406090509060a030b07091d04081b100204080d140705070302060f0904060e190e0601090f060e0f0f09060115031805250807 68
    0x18181c034020b10b15842c01405001c122050b842e8403c001440d954013a40000c000242c2610031480503400f6400380340c080f10007d007401d6050504061000305440344910a062240c0040400b244442e207964880704055038103c0c01302e410034039060502030000c4c0c48030300c220922548625000d45d16507805d030440c02c0c002c5034000d016510301900140c460700e004803410441c1d5014001c407803000502c00d480f1f01c0204018600080a00f144020f41e14000d0041ca0601a5070403860030100085000a00040b0b41e61045d01d50468825490740c0700c8000c0c180f440e0061007122034101b4034200c1e0205000703d05c1c02005d40300b050b6074006880d0589451401c03000f038400484912800d035000c14014400c03c0c100ba0480c2002244c4440005060740c0e41e40c0301d10201c00002d65207010010840d00921107502491003890ba0b011804a00420315945040e041519642f69860188109556440d00100b00341105d0950310729141c0240854494104034810748061181c1841034560581c40240d001424480c04100007049648640199 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 287839784 1250 287838534 287838553
    0x715050304050f06252a03051c02040509060d0308040b070c0c03060b0405091b0108040804050301050907051306060c1403070b0a050105041503150e011d0303100f030302 74
    0x9680640001e4000c551500503001d101140200811403184516080010201240081c9200b0402c88110390a05400c0202c80d108000c08503d40484520b5841c400d10340a0300200450300b001c950f03c1c040c800508004101560080d0302103103454000c1c1065540c102c840010030340798401046000280c410008011408080001d0301150101c040c259010440341800c0d2200e142c66510040034411a8100301c604035a074200c0c68480d4149481117a500c514407800a040f650f5146e1818401c1414200d01c117410451070324005010803165501b59001854040c0082c400c0d4240005115200c460900400d4010201d024010300740c0c20880c05094102d0f0742a840d02586255203446100c4050040014486644810000580020406140f4600c10740144100141a505003020401551864802100c010350040c0c0c041c40070400607604a510655445000902c55040b031300483d01400f0000d4070390f070000100c3d00d4501400c4138040001c6200700300b100c1d440300450391150300742c01f4501828040a00103038405c1158 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 287841034 1250 287839784 287839787
    0x60105040b0d240e030322080318160e0901050a020910031a0d0308041101021c05090406050a0906030209060405010e010605071e35090f0402090603040f0b07020715 72
    0x380d20004060760440800003d405a00c005075850360300c00d4420340c0c2c800010080000d01c41c03010401514145a800580c0d150991228401c07800b015140c2c0344410780740c55100d4421003040002c030b0f0b120481c01e5503e0002d0b50703850307480300c05600048600e021254209000501c0b80c0319184200c0b83c00d9000241034480b40c9081402c02c0703004101d00d203032000c58900050381240081c0d4030016980d24082c480c3d91181c035141352a05e001c0c0c200d9410141e200f4155841070011140f098440c101d081034004087c944142ca03100d00e00005800340001d50701040d0400d45491000c6105106600720105581c000d94500447d43c43d0f070b60600084072024481c400d40c0c0b804400040c454103220700300a00322207001e0503280e0021060302c042d089100410140499000a0210020020b0401c2d41031000f202c608007001203500a08080c00102c0c580b040040440c86000c10740f516078295a01d0382c3c1a03503815040600225180c0c07030280f030400d1420702c3d0240c003510040607440020321081d10020b281e5003500d5040e00c094141c2c3d00e01040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 287842284 1250 287841034 287841053
    0xf03020f161701061e060215040b31110f190312111c03050f041106030601090e010b031008030301180b0a12240c020c0d030908060405030705060105040b0d 68
    0xb84a202c035500d40c140016032080c080c000001001000d002082018a4250064500602000d401841503400c000300404210846140da40c400035400e2040c01c860160307a00e10707410305044000c406640410307524282c07e100e405400c2c41c5a00f40300340e506010880d003400401407106410200c0300c10000790350b9000c0c00010410811040055010f00b003042a40b83e203901611708020400621441d1154500c092030080303545400380c0c90f0007032506070096070103040c252078105440001c003138000e000d01e00000c0410026403198003403100602c030391564820a940c48081000d030301c1c1e00c02c1e60f0a064070020450046506500402105d0484403090821509400006074800c050300401c0c1515074810200c0d400002d1380500e0059003d0f40b180702e20740f610101100304800091300529682d8400d50a894012808201b58002501c0d4902c294103d656100d544001e15007203078a042c080e00840d00c24007405050204102c0004044c6c08001c0c030400942d0500c0c1c0e2a0010311003160000141946d002d0aa85115030102d00c0a40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 287843534 1250 287842284 287842319
    0x10f1e1406040302030304090209010306060903081905130801060e0105030303270c06040e0a29040b040207020a122a060e0a08070609230303030c180a030f03020f16 72
    0xc010500b015aa500001d0554120342d011580068000074031034010f41e8180b003148060000b13030500c40441d80c110740790600d6501411031403540503035800318000781c058040c00603103100b00c01e005032204507580c0f20500f15000c0c10040c80355040c80e112540011450f858048103880c4140c030345103811342100c14102400d105840070100c40d02c8550048072002d00c1c10307880b40e0000344050500080c400b01c05042001100040b20005654001707802c0e640e0b10499485802410074020015003180c02140310911103000030024440d18800a50050f0035441c0040c1940c1c0c60b00003462101d010f036450b07001d51541014211315544205041c071308c0f0301a84120500c070302401400035401000001d0b10110381346890745d84041c580039150300110042036144100b0841c4c80c0c90780f0641c1c003982c0380035a0092064a000e01c0400c1e60703400068101c2c62082c802080c0d45110605080e6040b80380c240c010101c3da9815540c5c2040d241060b0aa6816030040c002c0da00380c5003240a00107206150031031a007505401140c50030f07141038034144a58 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 287844784 1250 287843534 287843539
    0x92412040f05030324030114060d020604080a050606130207020a0302010f050d110c0c06090303040501081305100f05090c0a0e09030904060b1207020d0c06020708040b03040b010f1e14 80
    0xc1c20400d011800800155128001c98034000d0724100848000095003084919603d11070303030416205040c5002c1045060380c11001c2960b0f5503d00304c1141c40025240e0081d0780000700c0ca0b106103403915007132000028189000d2913041e20030000c083c0004001000f070303110b0150060b42209440d40c00f00015407184c2c074411214a8149452410800d603108204155001080e1f0708030303031603004a64a1500c0c4801e01264200b640c044500070319100d804408a6140c7c052445141e040c03044041c001964000179181d40003030107a000341501c05200700103189800a00d400c000840c030061601002441e019800035141c1c0341c0450044c03107045064036120422103403040050181406010510640d481a1110301501000c0d00140303032400d40320600c1410000e1300213801480c0208561090150b00d80346500502600c07019904094056503130b41d1503080402c40c600c80c582c000fa0303900c1300001c20002480060759865041e11610381c0f40782200c079a1144080100000f2a10214030035aa2210400c1000791348203000440c120f02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 287846034 1250 287844784 287844803
    0xa0f080c09010c0f0b09060105090a02041406090d151e0c02100b12070f05040f02040e010909051c031d0628110a08071205250903021509241204 63
    0x91703611498443c8041d00c1c0d58041e03511840c0180034a10f000f440b03207540300d00c1151046050614011645c00303115400305405004140000b4840003d0701c400700341605143c0c000034055a42c0b21f69020441c010401d50b120010b031002400308101d0880780034014034819000a138010480307000580d070050010300404003202d03072207501150420603164090142000070254031302c00d5540945840180300541e11103003808400248100001d000741c02c0a010a10f065a55100c03001030403420710700c1e080d45828141500030110181181d0741c0004903038150032030360300250300a6400c900b0140e004d030403595490060300c103000714402c0480702c4064503240c9200158000c0113510003040505801e07078455450f500c04050700c80001c60010410a102d034006102e0f1980641d0f13024200a285000016460789030040401c0d00c507905401001c8040d02880b0b030701038501a40c1c0003454000901642180c0f249103a10507000039014408062008003840351895184055544445d1403520300010143d110000c640002c1003181c20540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 287847284 1250 287846034 287846063
    0xb071104060f09060314060709120f08030a0615030605101101021c090210090e0f09030d0501080d1407110906060408010c0206071707020d05090a12080a0f080c09010c 73
    0x1941c42c02d072801030080000000700d2a0031800d140d0700c3c05ca40c0c41c1c00614582c5c04a070501203081e0f40004144102c8202d071000b0310741d0300f04914200103a0f0402d600042c01c5e401e8040309106d0b5560259006a0031034041f0650b10741201d409400585c2907420910490340c0c032084210510300a58059400c0396401d0b840800014507100c006105103615056900400800540d2aa03803601142404260300c003221040741002c0381020b180c24099401c03040014220402100d1250200ea00c3c180100103441090320220424481503031036909082c0d903020001c02003400540105025603000c5e01c8181160a8079400001442c004003900c014000300c07030b00140c50190015420000015044030030711468826240d02e602400c118208100004d0030810001001104480c003601480f44c1181c0006403000c840903036060858a80040b24002880d40d01c055100305031010500700202c00300041540148461512130b228081c666402803001c545411045075190b58050003081010029030182443d0080148228126007841d03c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 287848534 1250 287847284 287847299
    0x30a0608010e061008070f0605160f030e031b09150d0803041514010e16020c060408030d051008070303030504170705010e0105090c030c0111030d0e0d020d090b07110406 74
    0x1084980600702c81e41114043c0021940c1c000519002080c8120003407003ca41004403e40080e40740344901014404c001901b00042c03281d884c00c00d4111600314000c03000d001c40506000d441001d4a0304c0c050701c01d01690415a48a02e00c0c1d00040d41ca4403400ba04a6a5a545120344066494135002016038007547c0c04884000060808004500c00d030312900c1c1040364109003400c0c4100350b4624880800c006c10710040103200c0701050744003050344522009001118541d07448016420603410190f82900030b0340c00280450812000801089001c0c000b1004001d1692840d0b99030401c0d01080c080d803003554000d0350701000030a100342c001940050040b070201c0c003210408504401680c0c000030048400340d454000a0003422801e1240035808843d01000e010042070340d000180e12040c031b00301a6418404590300340c013244501042500e03550f185244040001d101a440d1095031101000400401807180c00051140703607104a400e50111240f02e8041414280e503960398104482c2c007980d1140d0082d99581c0d00203003a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 287849784 1250 287848534 287848541
    0xb07080409110c1006050f041e0204120b180601031217010603090506060901050603060409030917070503061b040603021b12030a0c0323090a0507090b130c08010902030a060801 77
    0x1030000c00b103507580c3e440d10b000030141840601004482c040d0316005c070030041910f0303500c49182c032420112030016004001c4080b140440e020031018000451000c100850b0190034410009603040c043d0030840800d9607a008411200e012410306103a603a00300f500100000b85c80b219050304120003a0400040d9070101c820004c4401c1030076804000001d407100305040500c10248980c541000c000d40f9525501d606040c04214540710140c5910b005039503c51200091500c9100401b01a1a040b40311102c2800402c11181d1380720f07405c1c018584a4010000400c1a00c00710008560305450711039405802c1c20b02d40030060b03001350051604c031a4410108003420070088801c0c13082950290b00901001d44034140000000c044850131440b41090502e8400750400380441441c98900110490202c5070965640382e403054245000703000000d002d440396030302c0480c800b0421307080030300b02c04030079900c1c03035018003124030464151081c1003c1c03600403a080f103006118080c5103400642c1d210482100210301a5621500d01d13003107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 287851034 1250 287849784 287849801
    0xa050c0a0c090606030209101206031a010311010c0302150402040605060a0801060306080c01020a26030412031406100305091e0102030f13023d0c0203010b0402130b07080409 76
    0x400c03084000b4802540d0900c902d4002c1d01c0346141c00c505022150022803022600c42c0240000d1061924000810b0140b80d00268080c5502ca0940d042c04045c020300e05801410030300044504084581b490502944a4a0303101c50054150b402000c01000d10f130b420a000400c00350069811549600010449460310320040c420388059a1312240036625140c8020304440c0c5640004501d5040807580c00c0c0141c1c0c0c00500a032031a6000f041141600b000b1001d40c0382c0b0b880c090315041003100400300400c020b1040071502d80b070381082140c0341403155148940281c1c06840c806c56005600030200320403005600e1283d40101c0e030018005e8200e5452207000c118000b00d060300d6001c01c18150390000100003c00c0c08251985401c000c40c0c00208900040944c0014190076400d062400c924101a01c050070031425250302e0041214440360b0302007407003900c020040440890445c241d000c0d40c2400a18801030803d442244e00c1d0b90000c040b5029128281450451654085501a03814000c1032101007026401403040d43d81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 287852284 1250 287851034 287851043
    0x10050108030702090106140405040f02040f030c080f060408030f0a091709040e060705270d06060e0601080f011401120c08040506090109030806131409010b0109050402040f0b0a050c0a 80
    0x2160b0025204000710804140c0109007000524402d0444046403841620180c8174111004248011581c000300d00030302403a8040d024207400d0440020034088510030100548500c2d0f03003600c01c410030300180c40f6594002603c000300f101c68100000354010100c0d0703079500d4110700400070204041000e07846080341c1060099003242d081c6000034a4402e50303c2c05101c2d0329500c0c1d0313211014150304e10742250003034040d000c0c82d000541943c01d146034811141884490351221820000c1a42c1d15104040c107121004100034000d02138440000804280158060603083c0d216500310000a641c1c2d0f800e008115120340c208900413414065003003036510b04140540160345540701c641da2072201c0c40c6000d05003179107061405008032506925100e003030004640e00002aa03070060302541e5100341c601079100c01000030301081e0750207001c241202050100c440819044080310402c00d0b41c1d414405600d0310200412031155100301c0c0c00c2c1e80345d2201b080020340390781e02c01f4244850302030801d40c0c02c1c60b07071f850945401c21054080858 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 287853534 1250 287852284 287852287
    0x4061d060904090c1403010e100b1c080d0b040e0a060f061a0304020f010c080711010918060501020d140301030f0201050c0618060c0702031f15060201021b010b01050a08091005010803 80
    0x100e44500795540840c071004070003d0056103230000c0c046440d4103c00200300461500c9154020079078541e05244045603d40e40d6640600701e006041c49007054020780c1c0161401c5080c9500c4a60520b011300440050030103a0025145500d455501c4030010185801140314064444600040130581c0482c0d0000700c802d00d640107542d07407030284108400d4001042130917045c007008440300340128034044251480d540d030141d044e5140400140041ea2201c1c000d84c45034201645103034000d401004550040800c41e80f080c3c00700c1e01840642402070380c0580f0742401035100c03840180010004154000a003044160060510f40d2400359000343c400c3c1840400c482403040600d00c442c0f0492000c02c100034541d400f003509210a4108009640003a0b211501c00d80b8604c1c1461401006070701d1013519903c4080b001500101d00381c188c03942c41e0b1020b4040d40081011440d07041c4503500480d2148418040c400a5240594a540c82c082c81c081d02592140000307051107590f44502c1992004401c014420540030300403040086 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 287854784 1250 287853534 287853539
    0x8190c2a020f22050903090904060e0f030f2a0d0c05100203060607080901020c040203070c02010e0409241b050304021905010e0f030c0a0b040f080304061d060904090c 73
    0x10401d9402104040d000d22585503001284400d0002c20443c00c01c0411008a000c0c0c40e610300700c03459406003c0013540c0c00b281400c02c1c0400c01082d5032040098001e241c0239503104044e000c1204d80c481c040d003085000707120380400c02c0c02c080e81c4071801210460809070300c103a42d014003d441218500009000c010000c1841215002e040c08001c01030008040c44c02d036000c0d8990300c1e000c00030071241e00a40c20003c10480d0b020a0001c0c0903030080c0041000700001070000c40d00d170701d0101c40003007200d02c81c560180d02044e0010355681c03580c10140100549650445021070308101206e074007158203802004040f108580d25140480a0040310301c241030210074940e502074170307420140100038280030031038040601d003401c3d604104410f981141807030064800441b003209034506440007090a00d4441030049a1001d0500d10101c1c0c00c400103800390080d00c185d04a68104240c844000b141d807482a8000c101c04a00c0d003c100c0300c50810540702c140c0d541400500a5130418003032034045016201241411100440c1c4220107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 287856034 1250 287854784 287854789
    0x10c0204110f1e04081509010f09080a03140609040f0c0f0f0f05040e1507030914030a02010b1c0209040215030a0c0e0105130b0d090218041208190c2a02 67
    0x981c2c1c82c66070079040c503610b042e01d00170a181d074035020042c258a03840607880c0055020203003984051804007048009000c80f100070716040c034103a40f05200c1c0c5400b09241142508820301158007040c0308100107815481e003502c40b0f0315503400c6a64001c0040700c02e00380305103020070030f4185840d490b0000c145801d2007a40312030a00c84035200000e031607017001c0d00641c9031030307003031240e012000504100926400061203c3c54403504421000380c5000800038042c9031f10406288031245000004045104440d070003000040c1d410390811008809070429520f80709910074120f0003600d844260319800c0f61000700a0980c0e124401050800d40d0000c4401c90f04540d65141450782139904004c1035081c040c82460540d1405640b40e6807010b5500c40d07401040460715012915000c0034446521201205800502000548410002040c2c01c480200e9088801c00300340d619503607034540078162541c00b4415521000d01c0e00004c24461034014600c118410040080d4030b40222010100440c2d07003c7c6a07251071244804240c0c0c617006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 287857284 1250 287856034 287856067
    0x302040b06030402221b0e0f010809120a05070b042301060f120206130305070f090c0906081e090f0610141002160902120f06030c010c0204110f 63
    0x2003150090908004100069076450309001c41701c0816200415110101030483c402400b040110024085100900040c02d0740c00c61070780b41d454034040700d401ca80d4244e410011520340c03e041d82c0c04c01003503028100344000200048068103503485145001400c101c111748804480780402d86040d03682e82c80d160211141000c01e4480c28608082c440020f019007440c0490440b608907180c4030b0180d15000d021480421552240111580e903001c83d02440c00c02501c030304103241c13910b03954441c6407003944020b800040c07421142c1c024050148039944410940070b142c0078045d215440001d010541078211021103141c950110b0300030350b0040091038020050801d4000700c0c14540b01000e40300004000c3c0c1c280040040c6400d83c0c00d002c4031042c00f80c550308100202d0392410b0f40740c15030352900d03081e140c50690008505076055034058821802540010f41e55502e40d6034030108000c0c1e040d5191900f5400c0304414500550103082000d404610207040012078021051a104080d04000381691044600169041d8a900c402c034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 287858534 1250 287857284 287857301
    0x806060102061512070504020a03052a0702061612050418020301081b03070305061303030615410a03320403170403031d150f0411060c01020301030204 66
    0x1c089a0520505940514210030b0509104d103100030b10044802000b07001c45801003030702400954403040005000380207031504460078040c8024000e0706500d4820b03801c1c50304254140c42a81240341c020150244119640302c04032509405070440c0010f00050703601d49002203c80c03859503c003038450f400d00c201d100020403d82031440516005000501084002288001007480e40040300101624050040b03800c2110325400070f00140500820054603147d4a402c0c0329070240310399003c000554484d0a421480c4001540550002e00d040c500014804500009000b102c007004d041c070501e14518041d00c20b58482c038108440700840d000700710b07000381d03941500500340594049407000c242a401106ca2064021380c1a00c20740c1140d5415010070181070003049520f1810840c5010750b076071441c060802a024140c5a0500c0d48456131000304032844a1011031900b92045800c00718002d0780e00c0d842d018a80d150b0010300700703550340e080c02c1401741616581c100060080d5040c0034005600c0f50b1550040008580040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 287859784 1250 287858534 287858537
    0x3090306060b0f03060603130f0c05030709020301030803060d0c08030406020a0b2d07030213120c080d0504060c1104051305010501060c080a030f1d1b10020307021309061508060601 79
    0x240040f048020051041e0380c1c0c000e030107851440c1c6a0b5030700418020240032004020b0b041c1c0240074509000d118010314a001659010b40440b00711031f03610120f20b000c9200912019101d101e041c000304013180b4040c0c00b50a00036004846c0d03132501c682c40e1034042d801c66000d9440500980e00c2180310204009905041c9940b16074040708100c400f480c8201202c0864640000041c07004090b0400130b0303511400fa0f0f05071400b903000b00e000421001e407030f25503142c0b001200701c905a030780e2000075400044008001072001e544081541c1e40c182040e141003001c1d228662005c030b0842e61801c118030a00344079103551080700d204101c44202107032300541c50f040c0b4a08407081030b0065401c0144c1c03041c50f4400700399400c04a43c00f41080d0300d030010702e00d6802101f80c0000c0c00800c0034404003200c250744400081e40002070940146501d0f0700340800200020f010002029001c040300400758005104070310140ca003000a180424000d200c021074850a00d40c0c42800f1581d101c040d40c000103071518024411100c04025103039101d0001e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 287861034 1250 287859784 287859787
    0xc020706030e190816120302040302041527020c120403170c03030705160b160e030105060d081e0703020307030f020a170918101d0403050d200703090306060b 69
    0x200380c25070303070f4900d001003e8442c000004510b00038426000c0d80c0c03156590000c8a2091030203e481c0010040d40c4144010380c443d600340088510003110441c01e142c12214294520070070070302030703a01e8230340b285403550b841c2140c00c1e60034054010800024020824615000308481341d8450440c41d0081c90015600b00d8030000c20001d00050408031000401c9075040042030a000d0b46071840d030a04072100301c1d00032400078201140e0906000da0502010184040c50003991503101c0707480094010302d400c0320012030704150f00400352880c040100d00e2080090038800380006019240103070b51521420300f5840340f00300314010303031002900e001459404800c1c0010303038107a0300c003901120b1100d4440407003003c1030b000c0c24080030800241d000c205a4501c60450160f4680d5000d4551500d4000510900c0e030b04507101c0c204010f408a20f001102d000844107440c0305542c140c4031749041000f150303a007000924203172040141d280e1050082070003119000001e441c10b07520035030320170015504500d041016109160f2103030300301680 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 287862284 1250 287861034 287861053
    0xb0601270b090f041e0f0e0601030f0507150804021e03061f08160801140f0a05060a030c15020714210c18070206060904020a0302040e0708010c020706030e 68
    0x10194410411180300d07800032a10b9000c00030000302103450100b4840d510500e0b241000501c0c0044040c4041c800343e4800c41001071240019006058170000c00641d03445402c01401400003071004544200b0302c900031001c50304100c0e1221030748080b80002c80035207804149940c0c200700c01c518100000c3c1c04a06510740b0424010b4a84001090baa0f090142031247c0c00a80c40000e40b003a03501081500008015401c01c0b98652400308549000c22030003406060425400c0c0540d45402c00c001140a50159030a5410812103075144242800140b0019140e681e129111000010200300c42888400c060050402c580c40c0b01c0f07103201c201074540002c55004540c0500c222880ba081541d0b500c80c03107540c15114503105007042907452640340c10401e1030000c3c0c035070003100b6118403d5400a481507482c481e44c565021101242c44040400000010131900254080c401d201c05000508090700400d492010079030456050503129103c15095954880c4800016400600204401945401761004940e40e40024220203035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 287863534 1250 287862284 287862347
    0xc0309060901150510140d090203190b190603080d0b090a09030e100908100b0a1406090609011b20010c080f03070915020a061a090a11160b0601 63
    0x903c40e114691142d0000c03008210001e000d0880c220900c02044025641e500701c5c440c0f204020241006c09030b000740300e810208205144840c828040e80f90b04044020742c070b41d5074007100141960306040180903e5845007070000020315218060603c2518490011a4007132901c42881a0710702d000780400324a07805e124107407021075000501d40c4c41c242d40c140c41482d060005003130140c8101c4015130283e1014071403071020311303183e007440d9202c4101c59204996031b50600ea651458040401d07001d45c0044d5001d042042212118a070110040c081309406040461801075140f9440e465800400b4054035154000601803079942012114440c40600900f080c0380710842585802d0b0540c05448850081844004040f07281a402000d10740000c011615910100c00d0310b5200007500d81504003002c607581410100d80b10381d0444038480710900f003e4050110481c6680b42008900585120042840e074414200004001140e039440303901a05402400071001c01e0400c80c0c00181381c2041641d0780410001c44401c1c404800303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 287864784 1250 287863534 287863571
    0x90e010e010330080a0b1c0302010606090807050f0d0b0a140c070b0f090c13091101030501060203090d110406090e06060f010503042a06031d010b0d0b0c120c0309060901 74
    0x10f6040d141400d4607554103040b00c402414400b044591240780058100b5095048100000350b451003039000340180c0f40c0d600e60a50300080c1d64020791100740c001c1182840b09042c101d40300c1e5151a4001c000a004e85442d40710344003072030b00c20340317000c10400c0d00e4481d00256800080380c5c2c950040c400d0f6104920300304503900c40d01030044024040400b04c400010201c0c11f04801040300311840f6000522251221003001220f10040020070403c079003080c0010701d451615806841218105c41ea02c0e009140b90082040c1004078800320070a049481c001442c0303003400300d40c6039445164050b000c540b07000a44070780003080c41c40c42c0c0000280320502c20034030302403a04c0131640c2c05070980303400680c4680c40610340d504176a505201189800b644c5903002da03c414001998550503009407400910508240300d41410003407070b01e03090303617100c00081c1e0300000d055141e0800034850740c050340d43c40742488019504001419003956490b03042694044030154011003408400d00702808650303006101c6100030407041c0201914010034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 287866034 1250 287864784 287864873
    0x9040605010504051c05010207061404030801090902330c010204060207050621040602040308032706160e0102030f04030f20100c1e051c050f030a05040201090e010e0103 74
    0xd117000001e03202e007004400d405440c00e1907403028061184040e20302c00051118000c480540001d4600b0700001846861881082e003107035005004101044c00880c29001d5400d0341000006e40d02071401c0b104c820600e401806407561032889400560307910b2a15200901c0d0489541082e813155404011609030824921000d0013466a0100c51a8842d0f6545c00d044000303000d258000b5003060000070402081100c3c1c02140044010b410701c0340e10318032075007620050703440e0411120304242c4000c020003814094050080000f0000c0140b040700d00d49071115038003840a8005900c1290030400d07149000701080201084110001ca6850030580054135801c0013030701455000818000307014032200200140a06840c00072403080c902c461044110907035180499494902e410b03a400b10703402c948480e2034024441d40c00c83c3c4585000c0f003007079030a5032207410100c0001e0030040c1089052140d03a10340007807a0054814264007d06c4950080c0d50715600d0340c2040400742c610350787c2241c019440400340e0b410321200c403040c203600c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 287867284 1250 287866034 287866069
    0x30c090a0605030130030e1504030c032907082e030b060118060327110907030905030405210a140c2d01110f070503010c02010c17091c02030904060501050405 69
    0x1f201100600482c20038681b1007182c8240c3c5c07500040220074081002c0c03c0350100c81c45440b0001c0c18a042898140b429081d0b00000c0203240405808144a284034101c0a43c00c10b5141107a11100040807441c000700d010810b07400c4110b50a404001c20074045c0042000f58850f9080c00c3c9910602409602c9030040389030ba010700d00605940b004820055076901a1000c04001c16401b21030b0035140b030303003072003044846c1480d482813042e95010002000207110b4001c41038140e610600950801d400d25040000460f20b4101c090350395080482101c00405081041c0c500450045581e180c0b01106a1a010304040d144410030b0700500780890004500d100c1120311520030100c00b110030310000b40450040341c013039500c40c010600360b00c02c6107140e410850000c0b80b44003c880b000c030000c01c144a488030043e801c0c1c07002094a6800700e0303041211900400c100c06a40c81c0c3c82141c40003601d940e110512104447c0040301e11910006a00c0454030700c9a0707041911030400501001d0910504140c601800955440b964610004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 287868534 1250 287867284 287867297
    0xc0d0210080a06050913060f06060c02040f02090612070906020a0f0b060d060c0302130e010510110c10031b0809060c07081201080a03120e060408030c090a060503013003 74
    0x40c0a1042e03030b4071034809060300400740f41c900e0034000e04403a4007240b40a001c1d9203841c0b40950b06110300b1818840e41303044030000d490f680074014040e0204030003011481400001e00d0f808100a804075501e484c000c24401c4880c03010b080076400c0c440c00090100c040307a000f000a55000c07040140100e20328680724254183d10441b07c050a507908404102c1d40e505054008002c68184460502ea588c0c040d0003600e045015850451400e030ba803001c40c990000020b2240503006104c4800c1c4550342841500701241c440c140d10116800c0000400101d0707914042c081c640300000e07580310981410380c036a00a14004003901803812079018140000000d4451401030011107601c200010700c0c9040041001c2510245220198900f000b9a541c128407900d40c602c100f001c030b0010f2450810410444694481e48103106598002000c0c140d40704d60b15454198009810080507020034001c0c00c129550710362070f00024002c0c90303841503201d52401512440c1082d03046061005034445021110030382040012140a6075058501700b0f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 287869784 1250 287868534 287868541
    0x109080c1207050606040222080601090b030a0f02090705040b040306020405090a09030915200106080f0307080d0906020d020c100b010507021e0a030803180d0e030307030809031303140c0d021008 85
    0xe84003d204010b003c8c0c5800c00210006103031034021500324100d45241d4004d100b19a800d804050711070642c000014690180d4510400160030080084c96002c01f650911518082e1114004c80b9244c025a00496145800050511150a264685039002454500300348500050350ba4040d103450068000d0445100300030341c00321060ba12489080d4a000340c655821001d0141201c2110f000e01075074000c0010520850740c00400f15080001201ca0300d40d0403107102e03410900c641c403844002c0c01035940c040d607d081c0c0900c04413a01c0c1c86107100808561142200410020368599501d406076022076086c2418480300340710745400350b140ca0261400e801c80e44d0310406d0400d0b400e800003c0f594840f580000d00702000200c00c01950300d069004514400d000c02d01110340c4000c2c451002c541340d51528801d00c0d05504240701d0800000e0144120a42003844401928140755000a00500c941d103d41d00543d913a0031200b50724441c00030140000001c00c0820b4030f00a641180d40c0c0c010546e0395003110703001410000541d002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 287871034 1250 287869784 287869807
    0x61d0406050d031101240306050702031c0506011211041716030f1a040c0b16050f010f0e0d0c02060c010e060f09010c0e01230c0109080c12070506060402 67
    0x3005814000c10840c10741e041800e0090080e0a0007403010710940c6402e54281c41c80c0315040c01e000381174210010f00111a821541c03040c0c0903140180140342584014040f0011780c040210301007890300c00c20708000800d840c10300c000602c1d43e4401c007150140f107807412032265443e14000d01100c090390720709d000d0440c500026038807292914466031254a140c008a81e4088200305844096010307140c010094034215821150060b4403e0106481c02001e02600714000c104036002000a021a0f9002080003658218241c8410b82407906c840c176a43d006035500d882507030041685101d1915107005060080038179080680003c1d1640d0311304d490182c071602d0701048c00401401b00750414280d00540c00103840c018200b007010043c112000f80c88040d04c5508100a40345a24070941001e200310784d0503510711050030f0048685819011215030401c004104c00c02c01215041400d0240074440b52084103003503503610707425120314200300c0044403405c01c03120100302110210781d00013000c4d038010b1012500141e9030143d8041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 287872284 1250 287871034 287871041
    0xb07030c020d11090c030606030a110d060605130b090604141c08040905070e01080705030a240303180b040302040b060910020105060112091e081c0603020102010f06061d04 75
    0x4000394440c1082c000c1d0001c211900800c55001002500c0000c502d807205a103080040c082126100d400903c180001110740d061504011441d406d41c682d20361601a4181141d0280e0b500c5070010720114600152070b00400115042410040506010b03075800d040c0100c0000d0300301e109074403540007692440c201c480115a0754100141c501c552103202c0c901340030b5407851300c00e88a402a200d843c080f2843c11000850680c020682c00510840503507400e800e5a44205050309c482e00003500f82c0f01c0f01d9035a09162400203812410589051303012100404403149545401001190341c9014113401c4080c281d4108402e543c46000e84098a50440e40411807151034408a0214054020503640c8501c1c58241c1d00c4a054065100324042c0030282c0e81c50741c4498060921800352400204005c0c42c0010508102d0060f07a01d004d0383c1c20b030b0076204c0c086e91031410320702c8400d1749561030800c40380d07600d00f9070f848104004640c0c0902c0703200a02c140104052026500c3c10303501401001c2c00640c0c2c03040c0d0802d04003100e2103e43c0c542c0e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 287873534 1250 287872284 287872307
    0xe240114150a0f0f140a110c03030a0e0a050301060b0d0b060909130309090e0a0f11040e030d06151d030106030b0a060e1302091f05090c0c0d0305100b0703 68
    0x125210300c44448000c15600c040d80c0e915003c01d20030b5144c000c4d0f1a218080581c2c9401c02020178a140c400e807010115100200810000c1c52070141c400864503036038041c401400724220741d6541c8414413805904126094941f648454880c0c0c0c507200c2c041005410810a031580341e0f507002000034074040c980003c030340903118142095034040000b0041000120301401d40d482d15a01070750f03400c8811a29100f010003142d8190b0700804080d40b1041010000800000581010501c00c804902440b540700010400769940740e14003403e0b40e00045a503a0b020302140c400d040c010143c406c46251007514041c801340102c0b4894a006400b003502e000e00b05c200b03803000d402020066601916030906441d001d000c020003030456001c1c001a202041d03000c41c0341c0b0071050144000ca10303001050b50f0600e4a6464510800e14200154030341442ea0a00c070018507036450352011440f4540210441ea61442e51002c82c90806045100c405c003450b2411041c054a094425858020380c1d81000e4a15601d4880342002c2e9074118428 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 287874784 1250 287873534 287873569
    0xc030b0910141503121c09020406060207080d0c020f06161208070e030106080c19030b0a270506060103020310081e01050f13020d02040608100e240114 66
    0x1c40e0110000e06815840c82203c0898100b450209208101034540c0449420000884800e1200c0307009540403c0510312441070702c240004031242c0c2a80490282d94060b031050001d40c00c10030040103480b200340901000444546028a41c04803da03000440282c168490240100c01c04a2070548609409041d40d5140750801141c21015100c8500200f015408407095800102c2551401c40c26040c140111030507112800041d06840e0941010b200514910084c00011958405400004105004200741c0030350250040400c805000c45602e580c140358011190400b540303a0025180403030000f02e03040d608003000b460096601d45401001141c1e5030000e401c1410140144002107119442581c1c042d80c1903e007000c0240320036501c1c0c1407024560300044500c0d11003010403201c000d0040c41c08000c20b4509500c02840096200e1b1925401442c00c0410340034156400c1e5180d01a0745008010040031208803440200c05400ea940045003241002041c441d03503c0c0d003200110102c1d4540c0e1800d0301c003c1c038035018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 287876034 1250 287874784 287874791
    0xf0c070609050a050c030f1b0418030c031403061008070302191205010819030309170a1115012105150403020d030e010c05040302060c0106090f0e06010506070c030b0910 74
    0x1424590b8942d50740c440f00b111148510000185c960601180c4003070003030301000140c5600e5019040b008540107180309140c0d072043c0d82e07000d049502c0d0f40440b00300e84054020750365140c00c000035180182101e1240006030030603031002d104120250b80c40b90074003c4002900d207080c60300c80c0c0b1810802d40c0640141420800c914401403201205283d000840980a0000340c00c10301c80760b640c509070726899212003002041c8000304cd25a03100400c3c025040510540d100b05038001c040d80700e0800143e40354005258420004401a5018159400030011410741c0c81221000c0034540d454100542c100b220582d09071041548ad07104454244482071100c01d5800010880d0000c140c42e192400a403900302c2030042101080c64400d151040640500c18bc0c1c510f000c0e59240c8170702d0103042d40c0805c069900f200250421564840b800400c106941d8003800717985840070031300880c9880c1c0000c001030406c10141c010758002c8005200001c040b4010903d0b01085a801036001006c60b2035849000303003050083e0f682d0540ca41d06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 287877284 1250 287876034 287876051
    0x2312010615030f05091207031e09030302010f27060207021c0b0709050102030a081825050f1309080d050f1503060f01031b170c01020717060f0c0706 65
    0xc10200c1d044020729140c2c0c0c00c00c02c014000504101300d075416940d5101030b5000000322810301c41c150700244a00c9000b4148104030007204019002885000c00c4d0010019486507070800801d5024040c400c5925800c00041c01b9070040152011018102001d40c4c0824000c031180d41000c1c0846581156035154028021b002402c0b0490280a4010041542184d80b200300500103000c0354410b2101c0e03020748505030302a604d0480074002c126051400984580381c0c96090514225038200100b00c81e1402c2d40e081180308401540c99030400140302c110b03078002c9001d40d400c0261419143d507091240041607001d036600041c04441424048518002c841090700940d10302801e00a001010304052440b03428901d0301541408864070a242e1100030640c2c00910f150b00100060001a0090042e041c4a0300b8608500800d180e4859591844503072111141c502500282d0401c0c00c0d0356814402800580380415410103410080305c0b4459440c0401003035080c900d070246c40883c0b5050072080c1100d00c0142c00c008244085030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 287878534 1250 287877284 287877299
    0x12030d060e061c0201080403050c15091606080a09060b1008010e01051c03110f0307030801080d0206010303020a120c02040e01050a0522110d0605011508070923120106 73
    0x346004621400d08803100148080c94070600400441500020040c082001d80d070055980401c003500882c103002090102d80076104040180a2501100703910544003800c2410095007800003000b08050090101e800078003c150300440088e401400e102c100141400080c18031400800d154a010780c0d0100e414040c0c4203007141d002041d14143c0385070518134025660f80c0c60410040d07405034061002c02c42110581c0402181c040e0300c483d0030440002e003d6407025a00c0e410b5031401c43d4014031089001c904088010701c01c841c0d0070042400344035983c1c0000d00c9294110b40b8040e60380d00124030020000c62071b803508070f61280e1017a0300682e2a6a406802441411320b1035034483d029150454201110b107140000040004c40d21023a00328601c2d00c03486600c05001ca00d512000c02c0301c0034943d502ca0b0001040c500200001d01d051060500800c20740241135401101d41c0401850004050f201c44200800074009002d082118200c01c00d00c9041100c40c8a1541e0441010405e0030303010248480495182003000102e05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 287879784 1250 287878534 287878541
    0x130e01020c071701140402060d0b091e0901050112120e090112021c150218060a090e0c0a020d0806040f060308090f0901030c091d01050103030e01080a0903080c0912030d 74
    0x9031642490304410000c10031040d400c0385e41000250405901ea500403602504003000140b0750080d15040101d00303142c148020a20090095070144150041104812030345190050701941114190009200c1780d490100ca0b05991090344401400484030012503000d401c0c020605040500009040f4071510340e51104400c1a039801d81e00203038090740303408001d922034105071400604c1c859440b400e10303103100400c41c00001c000e4200004507030b9080c540d8060620f142e6299405014100603c0d9640700b02503040210030100d0700d0001e40308211815051248081440e004075205030300b20813070300c0d00130066510800010003501c00b800901461a10342103000c0180003100c1c0042c441180300352640040c3c1c1042400b800b041c83d0092001134800c0d441c1c4203040c8106541c075081754941c207952403241c440340c5041c600c1c09421100281d0044000c100000318000840d42c000142d00d074800c0101d50100b210750b80c207440140500e10028034040c18a2000034004c8980e9032180c0c041c11514146000300c035110740c3e01c1c5045c40c1c000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 287881034 1250 287879784 287879789
    0x902120a1119081806100311010e090a090606080a0b1f1206060f080c13020a02030702090903030402010906141e0f120f010503010204030305040605130308030c0a080606130302130e01020c07 83
    0x450300380003a4041821000400c01e00070003d42d01b054080b280746445110132081a03c00781410001903030790142d1142d4549003100e005803440790f00000c42005510f4240110740d515400124103070840000ea202098404910a0384090a2512018a50140a61000c100480303400c281da4170309140041d58180601ca80c029000e40b101d80006c0c4010b141c4940c0d04564440c0f140e20f6083c0d004c4100740340170540300c03042e0700504201c0b8000d004880c200032040d80050054202254a0a1940e10100400081d582d01005c0807000700031604141401403080c2000d407150b481003180700515206040c2c0c0b020341c40d025200840b00d43c0f54444000c1364072200b0b003000c580c06003902501c0d01ca0803e04608008120b82c40c0600c01c99044952689406240924249059890b5009a52044079000200030004041400310f401948034030410880707a640c468078600041d103603040c060003045c0507107000d10119010322410061017050320380440341c08039807001c000004000740507000034900180d400070034160192880003500005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 287882284 1250 287881034 287881051
    0x50405010b100f0215010b0d0f0b060c03130e010e01150c0b1303020111040501210603020d030302040528061103070807120f1e0309020102030705010e0c04060902120a111908 76
    0xc0d0f81c0c049410baa42c610000b809030050410041000714031400713496005d0122712041d08030109014444800007240c2d50008903d0401d513400c00038000482010600048010300345181510000f941025011054610b05008500040d485480c610380311500a9240000d410f60040a04215140400c0200ca021120600403805503003400c5000103680c00c0042600e06941c0107a42c1c050b540e00c41200c0340084010b003500c0a02015a8956003c00541c070345061041a00e4025140540d0760352034127040c82018400c0015001c03088800300555800444080101c1044994601c0c01c3d841814100080ca8110f11400d0310080003550005268000c00202072660310307482f00c05482d09643c210320b5450580c1e0000113054070152140310042c008030000d00a51141e0303409130042c4111f81c1000700c0c2d5644c550848031243c07a6051140d00201c164601d42c94240030703100c0642145e08003507050960100c1503080803540602610311107926602c40035004907100c002d59410740346600b0340790b4506a003201d001d020400240e8a0340c1d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 287883534 1250 287882284 287882293
    0x150302090307231837090b15030d1101060909050c03070e09030a200a0b090105070e03030d02031803190206070503060d0b04052e060522050405010b100f02 68
    0x10340a140c58030168000d1030055981c40c01c16030341c18101e50100c42d500144c1d0b000211030754042078551204e00011066407171100c00b00203070000c900e050050200100402101048800ba0184081c58a010440003102c519034127020b05541c0420b101a405012b15401c410b02c030074a004201001d00c20700140c00c4130a0401030717003900c3d82d242e00d0700717214500340c44100d41034030780c0c0c0e40208800305000c1d120703a16040300d01500784103070225121000ca1480c00d01903a41c0381500c0d04403c000510a075010284074030740e0030900341d0504140c8504000c000c1780e01e90080d15510712010341c0c0803000400207581500300000c001480000d80307a980103900e503001050404074451000500c80c0c1d00004121034050003c03a402044001c0c1210103880da1550740c41d902400c014400c50f41402404c4140f1140e4052104082141c504c810b2250325005081705584103d0b40c2980c003007441072044010000da0104101400740300c401d01000040340581d1682882c80c003400401405a41043c1d00da0f0b0340401c5154083c00166003002181d080c5d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 287884784 1250 287883534 287883599
    0x1205042102280b130f14030310080d020717070f0b190302040f0e070c080408250303090513060305030307270b1803010e120702010f08090601150302090307 68
    0x2500b410b1002900144080300400204089080801000110b40e100314202c15664013541d0b1160310440152000c07022551011050080381001c400d140300242000800920303014807040402540c1b070070180305860a00300c1d8126851580c0c44140000760290841808070b031446591045400303d43e9000c00741d4200e4640d514082c50941a119000710380403103143c0c44000c1d0205040c00b40301d81d9007950140c2040184588590000f0000711260090801801c00c00003802280c0700d40840c0c66a13038080b20030680300307002e00c00d002440020b810500e0802640c506a40030f0032802c40c11020354000340707400d800241040c4008020071200c254801d505004040c415402e22140d895403100c0030403440c400d4052001712800034001c1d807420a4480c0820101040010004101d1170000d1700f1460402c5401c2c18010f0003400005800029940c00c441c2c5540150500d1401405515000010380d0b02c513501800b070713031181080e1881c41060f460f100e034050b181d42410040558503041c0d541c4009514560754903070948413906140550 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 287886034 1250 287884784 287884843
    0x310110a181d040c0b0a120203061809060601030e01180b09070906090b040b101403070c21081e070806060708030a0b0a1401020a1103150108010504030e0f011205042102 74
    0x46d5200e60007192544001e407080c0714100300203504020714640e0460440390980d59014450f42400c0d006424201c003800c51410804001000d44e202c4014200d026030610482801084a5145103081a9000304041d60720340c88162070181841300a0780800d001c58107003034000c1076100c203035800141d00e0141120100141c40760b003800d20031601801460b400119071010f420300b00e41c04814000b90380c000954640810140402e80e109040c2d03480301e54080d0818000a207510070159080241c080d003100c081c0080e03402800100b5280340075400000c0c45941000707036071f40104c1c106842d001c090380e01c05503000031001d0702c91420000c00c80003050600e440d144151a034820001c0e50000703910799001c103582c06034081d18101c15551540440918a40130980d0944113040b180581e21082450f1580a004c0e81000880c241c245404c004008129441c00280302e00d01c5c11900800903070b0807600a1461303011107a0003240c01e58517801c1544451001b81002204400700d560003042c0e1a9000c2000300c0d403404405500e035000d5a99101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 287887284 1250 287886034 287886037
    0x40603060510120c05090a06021f0504051f0906020a02011a01090803040501030e0a021009090e1204030308040201020703020a060c030801080d020331030f020310110a181d040c0b 78
    0x160440440c4120041c0040c1075030a82084803c608a17040a501d4017110601003907014040c2e03031000c3c0040c2c1249210183da504072380b240b40240b8a6110040c0982e00745501c507991544281115500c2007900184142c6101c1c1213504120300b4260011421501c4141c0040c001e4080c1c04200d41c00340062310341c280700f01a10360190240c00c09490340d800c01907090500b03020054000f000c1860030031445d403013162144401a0384100c041f0614070707043d941d4000042d10341009401607d4507150f000900d608101c107003001d8ac680041c00d40e800c40707801d071030450079544886c001030b41091041c0d00082e40100101001092041d00802505e0642e4425a62100c0c1d61307903289072458482c245500540e0068104002250801c500440c442c0d8081105500d01d0010400190030001030144940c400c40301c48203280e0264081d8070302448010380358501c0660501c10b80409012f6490360b03201d026641e1040c003103803540c0000c0c891202c40400c0b0140030408140c03a00002c141240240d01c040848045403000068640803913205030550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 287888534 1250 287887284 287887309
    0x90b090a0507091e050703020c070609030f0305071410022110121a0a0f0f0902030a021e03030309100b18070807030216120305070302070818030f030f0406030605 71
    0x1014100072810015081d016150302141d0320f5006000c4c625510380c201c440d04c69140200b0384e50f00c00680c2c59040116682c285031541e840752061250201c4100007040421016180003136040c501169110213501e00050404009178244506104004510400040c070754000e00e00e5441240c00400b101c14600703044e441465044540b901008428001000202c802d03030b40c031802043c4190000d00420880d1201e044d00107a04445080000d03440704081012a60faa1107001e40113922210240400d02c00740e004a6034452000d24000e0003a1645000c03400044882055180c80b60f50080c04d9136528102003100b2075035190101c1c85d00c041c240c13820000300310600d051042c0e02c124040b4102141e5003540d03200380a440140c8000d101606041d0208000c45118075403c041150b294890f2031f403110300c81802200141100c8000302004145803040080c3c5011500700d0b401c0d11405000101000304201480012904000601c4000c0d9000c1c8000700d111450703605004064410b85e882da540c2000101d40c0c8d40204082c001485 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 287889784 1250 287888534 287888543
    0x4030e120c0d030e060a020c010806061810030b0a090f0e0d0c08071e05150f10051203040504110304050c03010219180e010f080105090304061707030f0609090b090a 72
    0x100c014041a052005400d02c5290003401c0c468200e08408010072035035445101c40d600181c102080114166811000c2e01d40c1021003503d0b042e003000102d0900b60700d42c18045200c1e51007171000c000d0940000d44a0b03000b1078a10003018104059803542c170981d1002030001040d00250340340c00d0206860802100050802c80d00d042651101e44010745521800d9065201000945181d000c200c2810300b13840503440380030704141c1714100030b0140501c0d00040304000c2c8005802604001d12900030702481d400010001020765004954001a002400c04414036503c1254029034205041c0300e0030781c1c0400c1c541806940b18030300580a5500b00d0f014003040501302e21580f80500c8018249a5900c0441c83c801c507110b00d000050385400309019912030300706581100c0e0036070182620a040da14180a401001e002c0d954020385040021820302c1e090400291a04411400101c5102032010000c0c1c016071007604000301c84140c5071420004a03440700c400300098645c205064038048015004284d50400000e8201d81d01c80c0c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 287891034 1250 287889784 287889793
    0x221a0321090907030207060203010308030114030604020a1502100606020d02101b120902030f030c191109091504060219050a0903080a0c02031c0206060909030a0f030216030804030e12 80
    0x1140100071402001800003c2010390034080720300060424401180a540140c2c1031039141e614280f490162400701e0030800e80260000024000141ca8201c1b9900c16190204d05004803082d40c000128504940044140803090901a00084080c0c000c10a40c036001202e0f420b0f00c0f1f640d80c03010240800e039403410f4040c0e100c1801110402e4a00e900c2441d03000101c1c42c8102d0045000c4000c0e400003450500c40d50b000442075000040e50700383c0928108540d20b4100c0010105008000c0e150b120801500009070442d8000c801a0b000030711a10014081458615a1042081600c3c1060306003a4000d40155143c00400b0450110350070020b4095000d40f440301e2031b255030f85802d0700d055a6540d1030725000f00d40003005005000c400800181e9062141c12443c800d02e031200390b001072440701e00a00d080005001140607882c00420b000d80c5d40c00c040102c400381072480c10701d003045151583d0300310024800e400303035800021040c0c000d800815034030228083c0900d00940c1c0780b002c440c0e148010490307940c031104d50081c041e40c003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 287892284 1250 287891034 287891047
    0x50a0b010e101403060a120606051c05060103140712050703020a0905010503030306040905030f0414100f050f03100302150309010606030e15040615080a2906221a0321 73
    0x3e01400855100e040a8103003942150386108080c030584207403e045400503200c110038466800c207600c1900518544042702c1d00d2040d1035841e141d031034220601001d840c0a0044c101d4048120040005c00d00801302900414140c1c81c485c14041c2e01c41c0f00c82c3c00100e200300440c500009809680e8060135041c2c45006025500d15166881004003d00c6408400c17529408203004640024108002a20040500740003099a46954004221070040301103899014007200c4801420001e5000050320484560148000d55a440760401704e940710f003150380000d600c0002808402148500e01c8080c6000c3c58000d4024000319480f400300345d068403036031444e04820307a209454403000d0300089032141e41c000e40209000200c0001d6280b60490380d40306034101202691203400c8041c00c00c4100005007084411180c01e240c46004900048034524201800803449011036241e110084604040c81c41d11041903040100701c0b0014020303109100c4181030010030300c01d00618444c401c450458a8040389010b07405500689000d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 287893534 1250 287892284 287892317
    0xc0f080c07020d0501020a05070c0b0c15040c0906060f08090c01020c150909010311030f0a0f0b0a18060509151303200a1a0604091205030910050a0b010e10 68
    0x8001c6041642d0200311064500301252003840100000b400c255103295450007107040680d420403282d03008a250704800c10400c00c41c1000230640c500e40400c80c5848002c2500c46081c540041032003600070305034042c507040d0005500c0b40c000700c032012003491545400b4544d644003200143c4071040c6a004078050b0700460110406072038400960034000700403e01e0142031000070b00104850003801d82080320b0581e080503284015180420400c3d18000b00e02d0010300d00301980d5900c055440c039039807200920400e40400410411306981d040313521210340c00c0784892489000c600705207024003015580b414160041405403104011540003483c42581700e20315825041d0501d68046602c02c0c02a5000641c0281050204501901c14070260112900130b4410b00d0601c0000703030b0540304960000c0c2c1280c2c0f10700d00e00042c00c00041c082a40c1045d4426032070401e5500c0e0340da41c040c03030b6041c04400d050a1408030318050420580c16107a5001c0ca940240a03654489400c440201780300a62401752030b10300100300030445a50101c3c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 287894784 1250 287893534 287893537
    0x60f060315040f02072301140705070303150302040f14010f030b040f020f0907020319030605010f0804020f120a05060c13030b1e0705180406060c06020315060c0607030c0f080c 77
    0x303059908014039214031500d4400c2d2808000696400306e0030035000301c10842400f40612000714900607800040f5041151000d001031055881c020141511108040d0310001c0003544400119009041403114220f049040f400401d943c641c000480e14a0340c0002c900894038a900c0d50940303500403003141e030b5504c5036294012003031030002c0126408014a10700e50680e880342032100780100816001180c0350348000101e40ea541390010202400c0500d09002001980c0e4001140c52002042d4140012180c5a5001146003044c030215055005919810009955100081c1c0361585a001364281c1d1103a44030b0240d100e00701e100c0c40f0400c060b00c40002106001191002d08010781041000050b074108170020304540e80e111030300300d4110020941c00301d28280c0c2e2070b20b82d155420725944c0443d820850b50781000f4010f0710390242c07020080d203015804000030701404400071f03109080110081ca11a120112800002e5695904a40e26000a0f00300081d0500c140e0041c4c103098003420082d11402c003555a0112400610f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 287896034 1250 287894784 287894801
    0x408030715151806060c0b2d0903091206040c180917030402100c020306190b03010608011e09020f0607020324090c0102030403080301150c1505060f06031504 69
    0x32551481c07006040030030110010001d0400c08003c1e15003004007080c40c012a19158491001d05c40d0601981300002c9000140c3c80d40004880b030120503112000103008110204200041c400c08500d40601001c101d000010700381c0c40c041154a840186041c1d00010303114103054500510a8115520500444a221080b519045191400058078064a48a10483c6207580c2c0654882000000912041d41422001c1041c40c1c45142841107900003a5408255074160090014440d002d5410032141110856002203000140081c005d02000d500d400d0501c2c004c01d08444071002a010700d038ac100d095440940903190040c0e80051058245400030405d0146507800020100c0e0316004448210902c1300310310b68030383c2d1002204888005149444002d040c908100404058150750003840300300b00041c004800c59054803d103510100c4203010b850400d849003400d082c0010050143700d010040b445a00781c0c00540300780e50451305203103918805402d000142c03105413511220031800050340d081030f0400340c010944 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 287897284 1250 287896034 287896073
    0x12190c0201020f0d020f072012150c130b030a0501090606080c0414010504091b0306080a0f020409020303070b09060a0b060a05030609040309092a030c0f0e0a0f090e0f0304080307 78
    0x207002803d60b08c0d52110758104584800b14400c0141c45500350405030141040f44001030001c1070a40410186900d031220003c1c22203e88a0300040ea0114400f04140b03444004d142841c0e40d02d440e402c19181c1c0c880070780000d0203a14001498014002107152107958164018640090007510f040d05204900500c9481506400e051203010000001d8418082c0702d081c154107001300c030b400440c0489040040a84503954442c0303078164054030303451012032404881c101c0810344c110350000d1322107503510100c0c0c194007a03030001a08148408040210b90440440e46030701c01c24580d4010000d0044840c00c1003d1401032060300c800003074040c40080c1c4241401000700341c002d8000c0c141072101c07640d1089882c003601c88501d2040241d050804c801c0c1d00c0d00e002c40300d0f403105002d01410b0034000790800001c0100b4141444094504021032a00a042c1c0303519401041006400e64221407890b140d1540189400f6042d900b0350301c40680304d0303405000354455002c0103036825030307162802035458402e2a4a030034041c00c2c0b10000130b25 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 287898534 1250 287897284 287897287
    0x30a081609060915030b1011011410090207050c03060c0c010c051c020a031e0903081b19050c01060f0e07090b0d0903030b1f171312030212190c0201020f0d020f 70
    0x100e50782d47c9000030b802d4106076544001405004440590030349030900d00405e820382c140c20a10105030301c8030402e4000c2d960320350030044c0c444030941403031490046514010341d018080c0c442401420143c0b03c00a01404032000024000000d061a080303406101d0141c409800c0e00c0c124020040d092015001080040d00310316001c1950001c04620140704260148464420f0755141e070408d04158002000700d91118486a000070940494121840180b060035035410500c603002a000700c44502400079031755034202c61802000881d8aa80500c501c00c42580500c00d80b0170400400078100a100f50400802d0300ca8240605080110131180c00f4058002c800084007496100c8045019544420f04900241c01142c030b940b8001d035400000180010441e1324034940c020740140108039004240340c080c020041d500c102080544901341d030381140280910140052204120b0040c0301071041c2d00796403114071190300c1c6001c00141142c083c00740d08070703c503040b19144500414032048035070419960180141180d8040002d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 287899784 1250 287898534 287898551
    0x815031c020102041409010f060c170d020405130b03100b010c05030315210a03050d0209040e0a06050c04030c05062803200a052a030a08160906091503 66
    0x10440d010300a030030301005030760120f4208000a444500d0f40400d4000b03070703480c220650600c0200300301d0005a0050300e00748007141c8080d5003007088041950400c2c188900310281c46120841901010394001e100715841188080c0d58039603100028442c039020380700010700600d5035010041c00c0f10058600d18500d18140103100e0703c0034012910620046100e00d0a01e4000d40c001c5104800300103801422810050042820703120a81c0420400121958990380504245440c0c03e04140c0d4a4081d21503e8101a08142408070110100b500000c00681e418820071040c07000c0da5994038209118011488081c240280c0d0902c2006107040c00e00c0203103c0b403102d0045c40b980580e4880c0c80da859000c121702500340041d03601c1c00e43c01140790708144000041c3c280f41450070303c0c040c2c9201e0020190700401484c10820505160912a81c4448141c0481c09281e04070075241c0f1142080e02c007401140302207440d560910781c00ca500d04406841500d0903015a034003500c03001c60300e50070003600400c8540704007005002c0c0f540c1c49940 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 287901034 1250 287899784 287899813
    0x6050409030201020702030123040b280905010f051303030e0a0204150303020d0f140307110d030213050307030b07050c0a05070b0304050f070b0906130308070303060302030f0d081503 80
    0x204000c80d4040e40000d03990f03504a10602d07084800c0440071000c1c064021590501800b403100350145c2103030300300b4110212501e4040103001418416106502c1b005554104031085000603003000c40310a010703000802c03a0301e092455810507104201c0342e2034a070140b49900d24000070b001c6e80c09040702110b03080880702e8841203a800b14003121441110849002e441400030002c046d810030240c00c00c1c66980c646481055810640502401c4002600d248052004000203d0192160050a091454403000c444600e007030000090020750041c12036038040d061001c00490241400501c01d01242e81c40a54404d0301c1d42c401c07904076207a4000d11b01d2080c0d03601800810401051003000660003920700003400c00c0ea01d0031b00c4e15001c0d262050146403c00c164006060400c0442051400d944a01c881903c03110342d07a03451000c80a2459682d504014000e002c003003560002d05616a019400343c2c1e100342c0882d9205010310300c00315552407800e11410002000340000480401004450030070b0804080d00702d41006444100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 287902284 1250 287901034 287901041
    0x1206030206040b03100b1206040513020d0303060807120503030a090f0b01030b06090630070b0c1606050309060118230f16020604060911150702040f021204060906060504 74
    0x881c280d099004000c0c45401c55001c0c1302c0318014190890030f2454008442c07d001d0b10706c500104404c5c445c2d43d40c1c1c000101c1c0071819000d400700641d40280400c02040c224038000d401030016005402140c846e1480206041007100301c240b00c45500300c0020350840c3d60301c141d0b00f0050034804008540c240081c0803040700203550512164040c500c210340303440a504c3d040003402424100241b009128154400103c07020440110800441500c4c0d40100c282900021034124a04545544800d5038517000146000f403031800440c0310600070300b11403045104299101c0080350340e80816106d01100d6003001004200a244c0040240c01c0414902400301d040d0b410308034042c5104d1040013243e02c0d0381914000301f10902c12600d01c070350740c00400d5000349410f24441c00c0c0025500c0500800040c1601e0313807030030944c05001c0890341450300c5210051580340c1ca042a40d03184036070350f00a101c080b40614242110007100c00074038000d680181b1010b015410003036445483d4000a0160414150358440c0d0711100030840361a00d01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 287903534 1250 287902284 287902289
    0xf031202190602070303180f0f020f122b02100504050c04020c06100b1611040e07030309080f07060e1903051b03060606040e060108040507180e06180d120603020604 72
    0x50b00140c032403500c1d082c080c09036501c6044008000c2103602411000130206018212410f820182100d00468540301040b0141e081944c0103511519601100420020014580340c00c000303080d03d0902d100f070b0b0380c505841c0210340c03d1003101c026030071914000461800710307400160312038007031401c43d800e101d841c6011604992100041c41000c4d041001000064041600100e005004801c3c0c190315000c0d80d090300201e2110100c00c003c009010340381044001c1d40c0d550300034600040c41c1c039040e1002c45071341e8034000d8803c0400784143c1c82e05000b2840c4070316800d1400300e07500c82140d22036120014401d100c2e804102e9005c0c00000504d041d000da0000c0400807503005c122603c0311100154416507846c50200c101860424000c0c41c3d81d01c0350904000512914402214054100c8001c1c28642c40a031900d00c0c0060400c680d541054201c0002400017170410306081e04542d425100070f000317031182070302e030090301c040300d0003440c103002030303580c3c0004e010f440b00ca40b04400403480c03000c42d0200028825220340c0001c00321740c0a40d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 287904784 1250 287903534 287903543
    0x706020d0b03190b0a0b0a08030f0a020f2107050f0601061d1c060b060c1213080f1509030f03010801090204050f011d0a11070302060f100f03120219 65
    0x6000c0356040342020002d03a9401981d20a410b02041d4081e07444c0301090314000c180008882c1c80e0481d125403500e50307001c500041c00b50541540d03111070b400c003170b95001504001401d400520904001814451010809940341c0c018007401c1107145041e174491180c140e0142c50b003100c0501c15100b001084000500905000c0e192907920241c01340c0d817071070a00c409041c10501d00340c4100012240c07460841041d210001c05560f11a101148082240000410718018400343c00740314010307600f000441c8000080205220041881ca401c64180c5801f04142d592250768a4624540e220340c400f800045006020140d001d541401140d01e02403a41c000604160030aa00a5031207030f45414078442146054020b1030351111141051041c25850140c4449408030b03403c1046003120000700114241c0f062a80100c46405241040c0039500c42292070700955403c0300320745540b140360205011400500c03e01880f0b100300c45a048800aa030350654640c0c820348992280000c1c01d6204100c0c0b0301041403808044504e1840c040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 287906034 1250 287904784 287904791
    0x13021206010503160803040e070c0503040e1b03090c041104092a080609010b130b120a0b0927071e0915030c15030b040608030406030b040203040506070804080706020d 73
    0x4202c2854070340b945661000612029a50b0248880c1c40f000094608945001348103070166212075005039941e404c8410060420300000a000c5004995207150500074810000c2009803007a4186450002e4003007034540100300e801c014141c840c030b460550042c400e160002844149401d80e1422400202c90300e2222071080200851a903205041c41c5840d080009109410400c4291404600084442005000c0d0900c6090040b908914181d8241d40f240003510038151081e544005044000c020392808850a800c3c103810601d0002c40c9007004210240901c0500c45115000701084034800040c2d910511140c1c914440c01c8000140d58850300b4132007141408421005240310f080148207010b603426400010560900c40e10200002281e0844a904540c0469020b4080a54072141113003d040030b0950745900070f0030206d01040a900100c003e0003120b605840805c0880e211100384400c0c1d00007128042c00503003010001607001400340c100b8a50041c441c100d500d140400603034486003240c108c03a443c10318881d603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 287907284 1250 287906034 287906039
    0x403020f0d09050d0210120f1d0a020108190f021201033005090f04060303030504021804030215090114070e040c09050f06161403070b091f020a0504050a080606040605091501081302120601 82
    0x403844040046200c1d01d070040c254102b503640000e0300e45071016081400350480401244082e1003d03600c4412008220201959188242c40d20801001400c1c0000c0d41c00035840308400c101019a04846480f011080310100c5511503031902c151202d41103004660b822407502c5c03005004d1a512031198030040c52294030b0025043c1414014003810b5020030b81ea500b5907580420901001c40d80008184240d003000d00c41d403803899510040424054040c14401c030515918807000d0200c1207400040b9950b41200c2980c003003020446a190441d9101203611403160005001603040e142030405500402444480550780704000065a40d41070a000d413003030b03850040707400c042610302c01c1100983d0129004640c110017410b294a0880444403a4140c0d8014071040c0c81e030000740200c0b428014029500242401060000e0280e40d0310f0b201611404102c8100d84180e2902ca004902464901d65481c043d0b541c010264030220318507001500e10600c05488a00086800c800d000c00581e82c0302e804110020300079010f4006e551 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 287908534 1250 287907284 287907311
    0x3010b1306031e050c09060103060909050c030f01060e0604020f0c0601170c01171515210c03190902010c06110a030606050901051608120403020f0d09050d0210120f 72
    0x11601d143c071041c0000c0c489100c0109a0000d010503c00400311403404040e00c030368006800828147e40000312503030616188005121000c50100030780002a406c0d5400e211000c454135080702c0c07060007108034580c2c48a0201e801404d0a502a220300c10b0800561450806501151480e00d6001d84c40034200c203104803290f0415080074804082c598200b0b003404803a44844803403600505c1e20041c0142c0072610f00540c2400b05030f5510a01d00c0001c51021540c07503461481c081031003900e03401c896580401344002008a10720300c40f0a011280f155103a0031015020502c110307901000740145a105034100602d80d403014000c94080d11400303110b10300c124282d554a4010300e40280035141c42d40c0c03258003804800d02840307002c0d981040444049411500c98071034080000e141184150241112104e4800a0070007000101600011034041080100040300c0f07603001400c4086441a400d40182c0e40c10100b0541301d140142024030090040401c1802c109103030b2112008000e0880300a5480340c0001d40d22205800c0300700c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 287909784 1250 287908534 287908553
    0x3100501060261030b040209040203010615020c0117060102060408030a0f02040b0a0e04090305041e03120810141f2c040606050903061317180a0b0304031d03010b130603 74
    0x1844072807804070144e1568460300c500401c0100040d00030840c0e100060119902035001c01e025043d00c2c02d01da600b413401217000a665401d20050f150200766820b1a1002605030304071000c0c4a840142e00402c10355545640300150f50b04040c1141644a45442440d087c000da9800684080d100b201c0c40c0070f413107120b25840203200c8440d0b296414012450201e140010a501000321000e1318800039003084031403d8210b0f003a15801b030356400030700006003141000c211590300c540440c0c002c0708160407032804c5684540301450030070404403140340d0025940d0a01007840c1e035060404219414035044c41d500f020319010b40c0240d8044445030140000c005007021039818035180c414403000d401d052819604103818000425a50305011b860401074030010640d1504200190b03c0b4400c40322641e00301c66440305980720103c0030b903406030080c1600c40c3c1900080814610300a030300b507910864150759100b020007001c41c80c000981030381030480c40d00740d502c0300314131119606c9900e0030014095000c44001042c6245003411f040b50b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 287911034 1250 287909784 287909953
    0x1a01140a09031202120313060b032a04060302031609050a0204030302030904050c041e06081501051b030f0705031b030c0d050a0c0f05030306031005010602 68
    0x6002402881a20360780809804242c0341d10030144200550540c5043e850414240d81c2000000c10000401c401142411070895030188100e00c02d000151050701015101d24418000d40360211200500c4e88400040060701c01003c0d801500c00607000740c403034010900300440341455150031080a24104202d800c04c1c400c0e60741c4103803021011400c290650b03600035228880d071000307103110325102d00110382e0b004040d800315002440c0d40c078000341420a51407e2010300103c0e40c8900070106440100003142d00044403003409407408165200e41c0303090301215900208413000330144240d0703c070600c18615802240e074014802180520001c5844100b064412003880e0f0703e2510320440c581003071106030440d0b0780000d20301d01020a50b081587c0c8911201104840061040c0c1c03014100803401d420400034482c010004601032107054054621281c041482401038820a214500040e40045d00100722100040b0101c540d60310014000e03026121202c1c01c09680b0012000b410009040c1d0340040309140100034640fa42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 287912284 1250 287911034 287911067
    0x290c0d180b071d0a09110906030709030302060f0f0a05090705061b1e060106210912031401051507081b0105010602190b0c0a050919050f03190615091a01 67
    0x1c10307212460105080e65002d00c640307000307581c440c40300100b11080e06c029200a4240688003a45a280804004281512903c03064016020f0540810114020940510700c2500c5804a0f003c0c0c036200c480d03140b801048000d0919480c4c1c01211004121595040010104d08162001d000140140603072418148020703007020810551180304500400040410024111030060806405e406044000c0102140d07509400c000620b02c0d0020b50800c000c4c103a50220340001440e81c040007400c80300320b0311030b4003042e0a0080b07039130011025004030f60702c01022004201c503c2c441c0f14024180050207682102c1d420001c0c2c08022036035103402c01840f0344c6504118000b500c2804401607594208507071502800c01e00080c040c54459003001aa400302c0c83d018000b200c008020140003c41b041031003407a401014410340c040d0340e00c07030704900103100c0c114600012000b010b01c50000c40c3c666443c0303a643c0ca090080c210004a403005103004c000c00240d07a50a8405d500910039030080f041000e90305030000401c200c03183c030132020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 287913534 1250 287912284 287912327
    0x50114040515010e010212040308040306180203070b160602070b01091112070e0f060c01050f0a0c05040b180603010801091b032103150b07290c0d180b07 67
    0x1c088411100541c0002c0a08015601804400040b800c100c1d424582845207580090000b04014081c3c000b0b0003240d000d500204400b80d200b141c42c110a10745418060f40c1079000e414248000b070405401041d10345140700b4500d541e07004550b125003c2c1d0700201e1080e151442d00c500108442e400500541d12000c0c2c80c1404545400e60f0801c030031007082c0000c0c0182c001c0181228004c0b00f613886030072602011040003408903482e0020700c01c1b90b0307010703150803101b0100c0040300704003003242d002c00350145a11203480c0d03450f1241031031f09103003440c00240c12500e0300380380c0360545e100983d2464481d41e008501030305144001054501030b41c1400203400742c800039102c8605c9003181c402c00214180718000c0c0584991000c01d0810740700d45e81070440c05055050165042c01c801d0000001e003140712200117003000e0740f00304803610300c1d209152859064240070403a0745091203070510010b050850020010003a40e101e5000010310141001e1514030000e003180400c550281c004400c0c4807006803c01c5806507003000d000c00b8032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 287914784 1250 287913534 287913541
    0x906060302072f040203040f110a050a030b0c0d090803010914010e0a05060102100c03091a0903030601200a030e011d0a09020906071a1008191203020c010f0501140405 73
    0xc01c1c1c022496010100d00e0006942d00080f58032800e004215910310041095482e1f0406060603851340102000440f0304295003841c02049003444070390032044910090440800c94036640300c03164500c000600901020208000030440c0b0800c900c104c50456015420894696041410050407204403070814070340512403500411010f00c40c071010136070108040300081a00c1d203820005070b00c0d0484542442c0320340750528102c260650f40c1a8003040d4104d015507a2100da03808101812000414140d83c05140d68100300002206940514403005c504000306d047c1c10700d048000841542003a00c046004c400194204245801a6a0224642c0142c500c0c0100000c40e0b4000d4200181c0e21039044d01c10081782d1a000b0682c04803d50342d540c150399001da003049070b0802d405031030b00315008031a4045840c44003040c0c910074041042000003030140b03040c85e041201e50001154a454011071041c003444004e0825030200300001010030300b8001c81d000003160520105c3d065060820411003d41a1070780c460040d450305040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 287916034 1250 287914784 287914793
    0xd030501080c040e1e0d1d06030402011103130608011503150303083105010c02070f060c0f080d0f0f0c080a230106020a050106091407080a0f15090606030207 69
    0x20902242c40840300000c41980070605a400c050b50400c4000754803194044c07034450010007003010a103d2a95607141d0102c8540c00725007414000d580004603400c40404d1001a0040d4068003824030f14110f030008503828000d03100e40702c00352400c194000c04009160761b401000140704040f007c00d81c0c1c44042c1010b0103c4445100f07503aa000041b48000341c1000340d4240410301001e0340c0d01c421175603c040514040103600c403690440c407026110f0402280e0962800403462425031002c500780b02a92003144d898000940341c2441283c8000c0c4480c010f40c0e8030300c000300e00c48000990040040c40d203255882008505941d00206500c2250620408900e80c075080254072244658040e54070f80e80300ca030704000003c1d403984064020301e0092290081c5250542d00000101700346400046411040d1702c150000e20003940c4514588040c2c8110042c00b2540300040c1c808038910a01550565602580e01e050000b40404455014420744000300c046c1d80c850011202e082c400803903180100c001406140c141036140c150503549 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 287917284 1250 287916034 287916043
    0x10c0e061207050c12071a04020907030f0b0a031b0501031a1e0303040305030301090e012306030c04050c07020a0f0b220306050a2a05091908060108070303020d03050108 74
    0x119020300001450018007098040c070140c0e140181e0040032958201c80005d880380c80c80d4002c0030180e9041d007250b8034001c84500c10301c2ca002e02c01c80d405000114203460350641a0042c02c1040032a8100340d4603800d00c440c1b580c4031030711200001c41c0119407929a9581103c1e610b0b200c48129000343d81051700b0700310207610142d00582408208d00080d11042c80b401c4c125501009042070390f907030306607142c0000036001041c0003002000c4c41c1642e0480d4810412088124182822140d030414081e075a040d600542a400401031640607601c0400501511940065100000c0403108100c516450082c40843c0315029814907100820140c2840c080000c03000d4182112200c1c10b0240c010b40d21203020020390b401c0300c1d440e0140782c154015a401f4209106d02e0901058520240c80001c2e03103503141d100c864024a01300c20075640058143d8100e6150285004882c5080c410004600356507149a03003640c0c0000510f040013003214a0082070400040c1c4007641c15890001d003002e601549500400d414800103002c001c0000c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 287918534 1250 287917284 287917297
    0x310030201030e010c020c1002160608010f060f12020d0e0105040818060310030f020112020309010b0103140f0106030b030f0307151803171012030e030607020102180609030102040b0a030905010c0e06 87
    0x158100348102360040e080345000c0c80c0501d03c0d094079002d0340e4000b9260b500140218165014130144121090715040c048808504005081c0009219040892802c50141d0b00070301daa0503020700d011400441c008841400c0d100c0980b012101c07600c000071001041c8415240c000030030442295003d00d1828602045000711101d07010150103980c0350007840b01168050003000e422510316801c01e540360300c0c2c0f03407950314000c124580f48a8007103402d1090b50000c000a080b8803070b22910f0940d21100e216401c001044000384400807038641c052065504150004400700301070115603114030a0910088801d180700c00690710840c00300d05040d800d00c54104000fa0f0411502e900f9401c0e00e110003035851780c5054034800c200300c00398021100c01211803035107010300d940400d59074055841902140e1041d150050704a00303d2285403040001e0304600e0580e4030007031070441c0040c01c0d030243c006e00150404d51150500304095000c0758401c00840c0e40c960079441000028010715541880d117050424030329034004007003400f512422 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 287919784 1250 287918534 287918539
    0x71b060909090c180b100c020f010306180906021e030a0605040501050303070f020409021203070515062404052d06030411010e04090b0901020c010501150c12020a080310030201030e010c020c 83
    0x660240101030070540c40f105651134001e1036505642e06c000b00180034585507080c181c1c0103820006404d101c0c3c1d40070b03029840407180e4008410031120030780910b410041030b1074501110001c2c2c08100000584018400022005e880807c00300e03038a0074140b00c0038046452940c02180102e0415004009580c0c0110030740d034200b508107c05145000300c6100143c01403207081d100a50100c4c1c1c8111994039440000050710700030b80320f601141e0b551180344601c0114400115001584040130091040c3c400c11b004c40700381d11300c0c01600441da00f455150b00010f11103141e00d54040e001207030140c060034400509203c913400d020500b55001403541c24107440e40b00314141484601410b10502031560801500d0302d600806080c5e4000040413000c0c140341200d05d010b58070005118056609250010611440303d20941e19492074035101c0901d40c940c150b03286030b8006d040e4203034270080d401034042d100089a1348038003c52182080c1c1c0c0031640110304510001d0220307030702140144280d80c902180c500d503158000509546a0108 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 287921034 1250 287919784 287919809
    0x60402060f040506070807050105070e090c13090608030a090f050105030c03150a0b3f0405100501080c27010311040f1109030c0105070305030c030c071b060909090c 72
    0xc250038541d0510450380101e80010700001ea690074440c803100602000c070301c1003000b4001c03071305c46400c201c8040c041e40e81041d5124124002103002424184004c11248000d98141c103000765481039158125034440c3d020721016040015171903030300d0b0350180c80e030b801602402160302c0d8120f007040e0008001c4c0c00010500141c028001007c03a032011203040c0d080e03892081c000c1983c0607081e101c030380041e00c075007002004a0103450400d009489094042d507030304098001d203a80600807840a182c44184c1c00b42d000d4070507541c0380038611203821040c015001d100d028103444001060526200010720401469400030036003583c05e8074100344003000504640c2ca04503500840d0170a8000c40003000500140300d08084034011a141101461042040c0c3d400340440307200c00c405554002403008015a8075100c0c907000100080c10410004070701d07144c0b50001d189c0019003280c5060611040340c3d40e0b00c1d00e0200c800059000c40101038004c1040640c40030364500540f80802c0e00b40300d02e001550b0b0310088240c441c0514020300d0103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 287922284 1250 287921034 287921047
    0x215010605030c090f0904060f0b04020c1231030209070807020a110613030b0402090105030a02010c08070f0f0303050f061906050c01090204110c01181e0c080f010e060603010603020306040206 84
    0x1d8410039090701707290003041c8981508081c9003020041049180c019040b50070300614406510f0244241c481c0d250081014041c801c901d8518441c05601c0278a45203020700c0c1010f080c130202503051840c0301850b000d01e602d00c03411074258010816034290040500c1e04102c0701008214101e1b6002c1010200c00c4e50080500520440708000200780b0b00aa598000407100c40c92000030a0104401000e406980240d410511503602c40042c140c03600300001000e40400c0f60701d040c010008003144001c0c4282405481085e4121965545081925100302c0081e0300107600d420034005000005204a0b0304190219a0240c01e20b4a4441c00d80e85040580310714000e018000c510b01040100a4100700c1080d0750040080096041340d140680481c1c1141044244540c07071f10441c502c1200350061010714080d000b941c000c0300b2201c0000d5410403004d8488081f10210215a00054042c074104212202c000d144000490040c0707001564600d04500104510b119071304100082000d030300d010581d01d070056010f03074a25940d1107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 287923534 1250 287922284 287922289
    0xb010e1509151314071d150f0c010f0515040c0305011503020d06090204030807141501050d060f0c03061d1e060102031908070f0804150506041512030215010605030c09 73
    0x301341c810448100070100100c056000351080000f80e040000b1095480700041401040d038644404041c00d84d0040001945110044000c0c100c1150303804008110401c2208990007610b0003560495080c00001c2d510941c40d1a00340140020300c01d0034071341046958903140400c0c0718030b50341059181c18103a00040e0640344140310313040314010b0000c0c031005556680d03032803401000c5507010341801e443d0400440d141d030804200105604044000d8590301810a13401c0204101c652092100100c440c1581c55800c0460200640a002030190043c1c8000503440e242580c4010998080c40701002c404900f00100030149403000b0240c51000c0c00e10f80248001e41c3d6490050f46140705030b06403542e814a0b402442c0001c0c3d039225041a1140010380d0703070710385000401d402c240c034407000035980148005490b40c07405000c20456800316901c420f000b40081403104101c01100c0c0c00c050907801842c0e04c1990344081c142450340400081d05101c0d00c2070705801d00c40d03252610081075800094404912018000707403188255 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 287924784 1250 287923534 287923541
    0x40b0103081606090f060c08070c080f070b0a0501030606050102070614030a06080f01020a090e070c03030c0909060b2a06010e060d0b0702030d1a010903021c0b010e15091513 76
    0x101e5111400b04103403020344c10404017010905404981c0d43d401c1c0701416020512560019018294586440e1500392055440390095000301800102c640401c0c0801e40124001600c05400f4201401c1c001420354114202001a0b54803500600e0556106200401c0150b9005412200c1605401e0445840781c48003000340016082d143d1022007648285001120000c0066004060741003858071108150f0350744807241d038141c00c422644403003ca6040c0d841a404170317000f500f04040000180c50000d00c25a12810f0000840340140c0003031030030f420081480d1540018940c28601903204050350320b18a4003882014580d91032050058002030100341002c1242038840d8403107661001d5000c1e5621007540307085803009589400c1610005079144c10074091a0100402c03403c1c1c210381210680d60401040d046800b030020703450420400b0182c100c4e0b0f00c0d004001050382c80d900b007070280001125440c8107041043d00981641050055184510031441c1030110415194003c6501c8002c251901000592400b0001008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 287926034 1250 287924784 287924827
    0x10b0d05040606122f10030207032a05011a06071401060b0a0e010206160f030b010e0307091b08060a0312120504032001060e07140c0102130e0a05040b010308 69
    0x8884c10b904070300300704034446032210f00202c1c050000c01e80409404414446813034a40d150f4541011601c134242c40c2c0e01c0c1c4640c0040ca8000e0290422000000507220402c51004401065145002070104a042084401c1c0130381c0100e000850301c0744442851302400511a0b118446000704043c400306c489010402007904a807004040d04c1c3c0d01151220382196010300012864156940180141000208400640c40310311600c02c4d40c5541c0c0e91121034600030701b50020700d1444001030510a940e0000c03806980c04100800252107034050100e007980e009031039599403d050114000501c200d24080141a448029101040f80d4028103881c000d040310060503212140e0741e60360a00402e081104000a040e0040b1010280811000107480c5402032003030f01d0360890b00c43d80161084076030030341c01003414039228081224218103800015445c20b517600030700c582241d003c034510030000300081108101440103440c0c40360740150001c0090080e8a003554071b00003030b80014040100441000700d250440d448400454840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 287927284 1250 287926034 287926049
    0x6090c01050a09181508060925050604081c05030c0a05070c0b130f05040207020d11030c030a12031107150c0905060a020303180d08070e040f111b06010b0d05040606 72
    0x4009070130304034180c06850311805440070141c0c00741c2d0000710090005890f42c450100c50002c0c151040fa500361114000d0807400ca641c01072141d03000042102d0703403568010001460114002c2060000c0c100040d50f60b00d510006039014070009100304011390f03419074100c404903880d40c98903507551001441e200c4451b0300f060b004003150040110b1000411083d40b5195401e40d03507192030b000c46e02940c031000c1006034800d078a402500891710207800000a80442465442d085004040ea9202c07006100860301d013042420003070b030748000c520812121f0142c02d0311944613080c0d10148402c1c0380040c0c13900d9545030a02e110040994090365150548180c521900650700609030003071080d030f03940f400c0d00c100039900d42066a0004c8951400640c3c3c07100b4130b80004000e90300145030303111012180c2d150b207000d83e0910019900c1541081d280d81c8100409403691041403001504607104130307140e066094110307080007a001721010040d03100d28018003806020030190340d8900560030000c15595520b103081ca01a00550f03000d1348 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 287928534 1250 287927284 287927309
    0xf07061e0209190b1e0c060403050a08060d030903110a0504020d020a0e0d0c051513090c080601020d02211209030717070c0504051f150f0206090c01050a09 68
    0x1a5020480d80007000158002c036070000c00507030300f41c2040ca000d500d40d101d21489410100004414083e10081c40b002054000c1c00007810003114450090400c201203504400080002810369480ea070088100d603003201050ba8820391000785960b008d80305070240e00016055076128029411559907450390b282c00b0b00b0000e4400e41d26030b282500b0541c081d4110041030b1000c6240494400341c00d0034005504041107800406100342d0030318000170b116150540407800400764404104000d54a850000350b80300500302080e0000320541182001803403071038041e1100d030447d040b00d80350b94945540000c4408400807030750b10807011036801544825842c420400b026800324900d4040181c00c18000c006440182d0164800c0e2443d1040448201c06520480710010036214040c6810b0090341042c1e840654000403c5507504180d101d1010468000b90f403960004940c1c0400a820f00382c502d41c0300c2d105170858085400140040c0c2440c44500380c0710308d9807d100074104540818400c101038850714107000100070320250803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 287929784 1250 287928534 287928581
    0xe09130515011403011107170d1e0e0c0904060c02030412150b0d08040b090a0902070b0a1803020a12200705040c1d040504171b1b060f0706 61
    0x1001e072800f403040240040010865202506042c01410000300540042500c3c1400655441c1e041d0403c8080000b0041c8040c4402240c003003c03031042c0107241007900e0200355924880704405d401c5d00c503c001c042d205a002408140c0d0306440c0d40880d107400a07030042010542d020090012850340c083c43d813102d02c480c400c08090200b41316007040c103007806a8001005018a840f0803051194400a40c5801400c64400300020011030700d0f81c20150115040081c100b249041c0d86d040a039060342c10120041e505100700e40b091090420f80c074401c1c0c2030b0b01c40e140b00f1002000c588984010303440d00c05010018010104030301756039205510411002030200e075605003443c1100d18240d10f05681d60200d0040e203000740e1501d0340403100a40103e4004a0308040495282001d2a072a0140000303040003500440f111f02c150b5024002c0c0c89910f0014000200c201040f0710115845031910500d4801c8040e407918152020040ca11101d8480f10200c4800e0300740c3c000d146540e40c80e40c1c80c12a0017003031240300b1000d0010804406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 287931034 1250 287929784 287929813
    0x91503010e09070303080c0a0e060c01021c0b030307020f04090b1611060c03010519150c0b06090705030f070509030a0809100e01020601060e040b1915050a0e091305 72
    0x25506a856000746941250703910a10140da640d031a00024000c02c0c994400103851840010003001c00d00301c1031071700d5070842d410036002c100141c0241060400a940200c0c807550302014070b03c0300340d0350078040500c103010079003034480460f4070b83c468504003070302542c64101904016280c0303400072508554401d6402d20585403600320090454080300355400011409040c3d003021042c0000c545010360b00c5005c2c080d166900e00710400c03503074403919044802c85002002001440d4040044401128052034a0b08010703001e003850204e0f506000101018030403582241403008185d40074007a01d90211b803021920070b503a10f6903070040e2a10300a00c404650b16100c0d001d140703001c0140040c00380c22002d03019030f0508044129904240d9642d03805001560059200600400400348110840061080d002e0700c002001c01d12440452a100901407845046034030a8a042000003080d0313825150310f40c0c05203801130500003030003401402c0c00541c0300c4051041c0101c1d0041140040010800700409034171400326480d12010049 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 287932284 1250 287931034 287931037
    0x90102030405070e04080316020a020d060c09060203070803040f1b06020d170f150d1401050402010e06190315080d02010504030206060307030c12051203181009030c0b0703020915 78
    0x14115081c0c00351180004841c061311440d14041d552108200d8107550724240d0340703400e0040780840102180303d0316500340050b03100e0303038804804203000b00760219842480c1c0d10b024020a1080d40b001007154800c0069001003a024400e03607810540c0540c0c0e0800d00440c03818002101c04040584080041901c0d10020307a594000030030450701210b40c0c56080d100107182055042c189000c0742d1142c0405100000242c550380302070300c440f1010500800f2029241c40c1500c0d04280e00300c420501c0300d03480c2e540d80300f40015036800040b00348203170204498030f92524065900c04400c1c8814101d098040c16181c0e01e10342c500d481038481d03203001343c16808125511514546802800f07801d041c1c0c0d094002d4017681012440334100800c02c04140ca8101c0c8000c0f0b0110320b800314107c243c0c0040401a40c40e80109000c0449482240000390f0040c161800002c0c0720451340f410b400d080101440d441030000b0303e044c1d080c10009030882605610785400c551640c0360fa60b1842e80960103885203d064a50050000720702c070088820850 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 287933534 1250 287932284 287932291
    0x31104150f08093d061a03010f0b030606070233031b091207060906170f0406020a0e0303040b0c070e090c09040501060f09020a0e010207061b0501021209010203 70
    0x58402100c0750380c1c204142d684141c1640d90311078613000583c3d00c02408090f0440d403070a010300c0d00d000d002962040d1086a1050361074500b80742e8041e8881c90100300300e0040321100070403103205284540c40c1d0b5240400101c41c1146601c00c40518410100001c0e00030340d902c100303440d84160098825100e2224281c19000960419805e615885800841d40d080d140d07010410b485c400d6803403401c0416070f004400514801d0760040c40c10550b118140e100401d03034014050060f00000e16090b11400070030703414020064482a2072600d6030011841540c200005504600d410540168001a005940b4018000e0407609140107403100d6030180720004000900c0f110782c00042c044e0f85040c01c01d40b81a55210420044035420548800c0031b103900160ba49512031404805503038000307118030000a011a03542000070741d000b903a54400c092250340401d0f8a400150803100d10b0500c4482440582400b9081100c054080c82c1d1060110198a01c1c0d00e400c4010000e00b58125408014130107540c00c00d80c1f8020003094080d61084 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 287934784 1250 287933534 287933537
    0x140405100503190e1b061902010605090a0209090403050a2609160b091504030f03120c1e030e0f1f0b060711040b0a0e040c1502030a0801090c03110415 66
    0x40003c0c1d108002520401c40300111400107880d00788000d0f0b1410f01049006010a036100b04104900c82c81c442400034410020a4140c00200d0213500d88410040b001ca00101804841401002000039503030b10042156803290385400c00c00d488949900c0d0803140806c060040000000080542c19468044d00c181c042c07040040c1007c60320207034400a42554000004d04c201c45410f00c05000c0103d851074500d201680c080443d480c46410f003540e030744580c01410042d01040d1b0104050f00d480300382c00c0c0d00c140212a010f0324541003219510030101c1e1040210204c2000b9201016038643c0c08000d18078051002d0703c00340301e5407030844000b6056036240c1480d19045510080720549400810251070802d6030680e821075802185c45440d0348100700601c4040d200c4e2800d01c035031140c2540d5001c1082c40c41c84032501d005078091144032003004d0500c3c0200043c00c10141889056502c28131600003d2940641d4090644950b8000800d240148038000d401600190f04440030320306001c10003241201d869920411407651a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 287936034 1250 287934784 287934811
    0x180105090703021c05070506070204020c0613020a0b0306100c06150602060a05010f0b03040602070507030f03050309060a0e3301172b080702071a28020303010501140405100503 77
    0x169013260b500c9040c501c0010141d421141003001541707405d801503c440d0380044c1016241040e44030b902030510310103c0307031b601e4540f031395070001c400307504002500e00058000d0031401c51440c18480006040549408074100070440002400300806c80507030019030561000b00344c8241160f48a0720060746802086503883e03001440c05000040d07800348401003a085440d004017180c91030700d5984a503400f945c440202900c8911034840b001002a00030040ea441c0c99000f0b42d01d960312400c02c6800c0c24208030700075200200032410b0088803c60070401284441c04001900408103008640c1102809612182c0041c820384001c1d007800065075113540860840707400c00078801c0e13400c80311301c40b00c555203c1c0c840303000e44a0070b80440e40d03a4900f1080c0108015a0402c1c9140111030f040b958034005954090a103901c1c00d0420f0360041420a0030000403030020018501c54075610b14000014140255280414400c0d20304105d204e560f4454514100d904603405000090b0019245038900360300509503500940d820b0407504071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 287937284 1250 287936034 287936059
    0x902040e030313080c03040b04090504060b09010f06031e0507031b0305090706030c0302090301050709090606260403091205010507110a020102120306030c04090b100519050103020318010509070302 86
    0x801100300c2e8803c1040c8400d00085030700c0b5441d540d48a0300140c1c3c05242d284410000494078104000c0640000c201026011401345000d1614030b0603512a100083d0080e800711005020204000418000783c91b51331800140c007109090841d2200034001c4842816207191406000000354550069240340e5080a2070701400b00d0820400c5081f260304131340c0c010aa0304024800c0c030001340700c4d0b0811000d81015103400350411084000190031500144d500202007400b11074100321080301806240002c0c515401c0c91842407004081c3c50741900019000a454488008001801c0601808804018160414207100b840480b845c020f8028072040d40c003040032072000d40c8041c48420000034500851603069000e0a062800004202082e8001034072203981030046038200310060f21a403150309c0342140140c0e06003075141003031000c800320102c85400542c05044415901e070203c041528590301141c001303190040c0c0d2036842000700c181070240b40c84d07000c110394200300601107583d8001402d00b00740d0340200c0c0d501c00d00724ac = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 287938534 1250 287937284 287937311
    0x190503060415300b1f080d091a0a0507080f160c08011a010203070f03031d0312010b2506060902071b090203061819020408070f06020304120f021909090204 68
    0x1915200411070030311a000100014410b00760503500c49650004442c103075071a002050304140d41c0340f90340400540e1860b400c09c82c451600044800360018280d10318a40003200d10014080c0c03056180240a00200098543c8491030b202c0465040b0301c8844091080501e45103054074544466108001103903080c40308611501170f00303403c25140e18505070000c43c9050201e80d031348800c140c4226400e9044c15682c0c031103807120301c060a52450681c5d9200000d90381c1e68070080822200740c1410703000700002103414855100096801c0d040ca224907007040410080d890958074000000d0310f40c035009580754600219200b000c002d441030b0441c1c86124030325910b405003030b19100300340100e000444000b0350003460001981c400050190b00305400070b68041c6604201c001c10001e902c03ea9000794008407042c0c1c03107050b0421082580c035283ca07025002c1031010307601d003074542800d840d40412005005880c05014900704000c66850141d030000040400c00c50b6040d2641d2005108021303c98260245e00075401c210880140c5c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 287939784 1250 287938534 287938619
    0x60302090616050c0603070c060e0a020a06050f190f0e182205010e0d09060c030f030218100f02011104080a03050313060e0115080102190503060415 65
    0xd8010304000d08080142d00c0a09010b54100341c1900c0328084c0c0214024a40c50b5131700214851a03580e2144c6040a209240c03003411503500205000301ca070007202c5103200607528071034904210b031800d2410f01c2c0c499034110500d030050b01c608032000d007070341d0300182003080322640182e14050100401d4448402000d500810b02c120a2032646580c0364019907000000d070040b400b880004007081ea80b07504519610201e645440c2100c2c9021005011544042c80b049000c0768810800070240c8030615124102100d2540c000d826034881d5800b00050607004142d00c0d0820186440307800c2310b0f86c1c00030300422003186500005070030310744030040c0340005500b45039640d801d48020104540071580b15070010302c804642600c0c111000d1300042c05000c00054a0207000012410724040d00c011003c00d4000003c0344500c242e94208840700542c0b14080e04d900610910300862407100d4280d80c803854a00300240c0d00d03580c0500103001403812060300b0b004041030000100e80c280b011907562003200f04ca118078040d580f8540b201043c21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 287941034 1250 287939784 287939797
    0x60105041a03062d0f04020405090a05060c1b190302010e03181512040c05041802031009020102031e090906030118030f03020702060a021c1803170c0124060302 70
    0x265020501045501c404c1c40360103042d412540741d5a558840940d8251090b800007602c0c0b0300c07114001c00c0240815440e0503c07134030350012404401070904040f10341d1041d4448000815082d24068046000e5000e914041c3e00d00d510303103103240103462680030351500303d034111b502e800c0c4103030b00541c6441820401c075a8000201c2c5c2d0303483c07103a600b15540740003280c1c00c001d10165512122010030b002070011080c00764032001d03040d025502c9240440d03082410442440115050300380302401c00b581004100c2c0158401083d0081d4007807035540085160b003041e000503840e40c0309480300416030250101d0400f2080b0b40e0790002e030031100c40071500c1d081c01745c031030400301802d85402d2490301190001c00c28118002030f010b080400c69240f040c3c1009070510355203800050680e0040e84006026800c0721550350140c40f0340098401a0a5041c144003010345178142491050700c03081e000040106070306080e5929940c28003000d452100c0b0401c0d00910450011f00081d040506611940c401c449040c1c43e000300f0018000d0095401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 287942284 1250 287941034 287941039
    0x31416060e030a0615080a0f11040b06070807230703020315070203190c060603032f060c1b0109060e070905151018060518120d030e030c010e060105041a 67
    0x480f00241c2c440030000c0050642800c490034220b2000540701c1c0041c403500d11802d00844603040900a18103281030240d1744100380364442e0b85055052000da549102c1076803999030b000203c560b1a01202c1c5031000202c039041d595031003188030403101c50018040008107542502e1081d401c3d03610000402c40c038102d4001c026101c0d04090b800502000340c2c0f034150480c1100c000100c5203490300b84640d55443e070000300d60f03c0303800c07d400060308a01020115501e8442c4107110f02030121007080c1d0ba07010007180688425001c0c000e0492404002412500001840c5111498202c800000c1101c0c202d1890800005e01c44032030b2210b098090301a0015480c00c66102c0c003403140e50081b01d0701c440d20302c51008011503031607191098030610100c4110011200b460f03902c400c0141c10503884a41d03541007035102070404041c08000541c4180c1400564026034840480c00b00b00e0040035080205a03c038000c000142903000e0710a070f01c500f541c81c0c074200301c15000d0700246490480700203850412140c0d604261501c4440d41890fa17854 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 287943534 1250 287942284 287942293
    0x501151d0913080d060314030c15060420041409160309030507080c07091b14030402040b1005040e0703020304390f0801150303120b0a031416060e03 65
    0x880909041c40d00c03540c0003030020355840d2010a02d6a503031000703400c040725070079003950b48003000d204011b01c040000840386003090080d806c008140c03120554440500b90008032001c446c4002c235000340c94a8010000c81443c803403038540d020a0807450300c900d9801c0b510501d03001c032601340190856030911121541c003581c2d2105000e2610344c1e0084095000d010300d598100d007085070401c0010041884100500b8804031000080c0041301c1c13800305048103640802030704041d0036480d161440001a001202458080e8141d06400c0d2070ba592800050010700c084032400d42c1006230100052150342c1e02400500540b403103101d8071201615900801c8049020482e8004c101c1e103a40c8002940c0c00d1140f00c0488400744000000310b0784c2135a0a80564264641507011042485859005101510f03080c0504132050f01c441c517421038900d240d614024080ca228604054009039284161035040d00c48410000155401401c107458040d031040c561541c601e141a1299501d00881401103901d41c8034180c10246400000d0081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 287944784 1250 287943534 287943587
    0x12070b0a0c05090d030f110606100e03011104080a121706120109050106080d261b040515040e0603060103080406030f02040504060b121602030301060c030e090406050115 74
    0x680040070a180e09005116050080030b40ba50703200c0c510400107074840d07070b01c80000700c00c00d00d000381644d040100000442c1d0045010000315842c0c0480d581c030007105921784080c51015080c04a070040c4901d111140c0c0078a0b000802007500c80c4002070702c84159224040f0640424031031081140c106100c4203043c2d150000c0640410b10340d2400c95013000c031040c0600c000140507811961403a00b12821075004441ca40c100d59804113440323070440c0b844064070420b401e01da44c01c6044d0081081c003d00004052800b01d5840001e4508480400f1040d10094200079050101c40c10222548002e10b0300a84a0040d400d030015002910700d04001c60b499040700d0740409058109802c199042c0c020f805a070316030401450b403e03c0001401e9441d401000024490481c01070b940f45540558640c040800500202c2040c0c1d65080485195600100f01c03411215146492000720300f0500d000c99070440400f84079035100c03110805002c01c0c03098a52215040396112800551010790707641c420b030f0b105001185104410b1401c145607 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 287946034 1250 287944784 287944801
    0x121b0b0702040515040e0615040b0321041a2502010c0602160204060e011e060c15020705030a0e03070f0803032221200307060f1e090512070b 62
    0x41900000c1e000e0104c4143d0381d8003c086803c403280c48408003a554880e809003d48940c114240c1d164492080d00c050081c140085e021035030703807040550b014006c1036044903410110405182603601404180d00e450440b02480c851004142d001413010320500d10000f190240000c6105917402c02242d41a140c0c6c0c0b00319500f9468000080d040450f00c444a010ba14494400590300c40c460351000e00341c2c40207100718030b5050100405184603446404201c19103404802d000403900080071a01c940d03400703501c4000e103030080d518000c081c2c010703110b0052881c807012602602864000003444029101642103038003070760395401c080c01040703664825800d56400401c0810300c1d41c03078205644001d000f60780c10700c10948800c542e9603107407100451103906050113484103c03015043c2c0c44414207004220014500350750319540ca82c0d850f16485000001050186e458464441d421a030350498003c00105544040420f80195004800352415010403617480c000c605108001e130130b140c002d65003000e0304501d24104d15651100d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 287947284 1250 287946034 287946041
    0x190f09050915040b03030d050a050601170a0915090303050417030c090909011407021501150e130f0606020f010f051303050d0b060f07060b010206090303070e0f030601121b0b070204 79
    0x709540c0258507138184481c00e480402c01800c8584951030002032a00d4240da824040702c1c009001c090400c000b204100c8008442c0d0080c09421400340c03140007525124a18000041e84050b1941c0118941022410024190141c0c480361055000b1202c00c4500e4a40c1c000c20f05451000311080040814140100855070512000c050f9110301d8a4000003110721500c00c0003030b0424000c0719038074010380c07201d080790a103013421010300c50040c00883c2c03a500c400c0280e09005031001d901c4a09850044803c2c90015401400a41180116056000c010071440d40c640c0e200030b460b0401400b84106660900980c076500703218510540c0d1084404007051108007110b035070102c546a00800610340042c9c1c0302c04036609155180d400422018210040165441e18149004000e85048080303080c1590030200070091103000100c12a90701403680d24284c0300402e416000500c03803001a40c8031720740620134540046440c000c006c0304c05401c0c0e40220800c00000c03010120005000500703001c0c000c0c100c6400d00602c1c005051580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 287948534 1250 287947284 287947321
    0x30304090b120a061d01020f0901030507030209041d0114010312050a0c1e0201090b0c06060105130b0415110703051009240c2303060d0503090303190f090509 69
    0xc01c05000c500b52481c1891606020500980304503541d140c442c507424600e14035410b0001009002941421102040c5645074050026180e05040d180c0c00010601403195041301c6000780000e0040041070345403000008400b03d589440d072000c2d0300c1d001c24101c9450003411090b040301d52050240d40406924501181d45820011035441400100c8803814009100c20301c0501d100003211040b1452141306000042c25003100380e00c24032801c4004c000c0300010302404500140c0c842404e00346159600d4521426205c41d0641d40c7c0400100080840c002c502c2980743c004c0151220480c0d034503040c0300c4609804658a07540540300043c441d81c40182282f140c9030103030b04038640d214001d5100904c0340e4500e0040400100f030b00102244c4142e03850004d1002c20b42c000d2500320001201c01d4458504204455002c81035200152215204150900030402009410411110360303180140070343c0e44481c3d84240c81440e029410006101060a0b4800c001907240716584c01412940f001301070078490f4407000400c1d4400c14514 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 287949640 1106 287948534 287948539
    0xf030b010308280c0b13033c020601090b1f110307200108010603050105060417121605011103040308060f0a080f100f0207020607020105031003150e01050a0902030304090b 75
    0x400041c00d0841d60308d24a001441c005071042c80d4000c044400c5004503151400004802d5404241941299000c0c3c1062181035500010072440c8102c1d2002c080400d040c4607540c20801d0b20071004003051804980542c3d103803107015162154488440348002c82800c540c50b02061071564011616801414603141c200710035410702c00040c5941c840c610401d001d41109044c83d0417042d00600c8140100e0103481d8642d640d41c41c0c0140707048842c0095a00c1610349500c1d260410b88500042c000702c0e80b02c5da6044c1e4640060369208810881d0030324a2195064003c200d080d0042540d042c200303c2c103c4c0b9004100c0060810a00086002040d123240f19407600540c0d005100b030700d00503100d4070140d80040f039090805c1900d0b56207550070b1a5001202e984040c0c5132100c409003140c80c912040c0d12401c01440c1e10030081c411903440004402c11751314003410003500350788100404c000d6034126a11000350741c80d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 287769784 287949640 := by
  have h0 := BRFrame.cov_init 287769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 287769784 ≤ n) (h2 : n < 287949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
