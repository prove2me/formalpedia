-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3399
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:33:26.162102+00:00
-- url     : https://prove2.me/submissions/10b074db-6931-4a74-a894-cc0576b29390

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 611151079 ≤ n < 611330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 611152329 1250 611151079 611151083
    0x605060a030606030b0d2003010e010e03090307140d061805012412080703050a1418120105040b06090a0b22050603210304111e01030c023c0604 63
    0x60061404500a0175a074100020700c1c0126981d41510000c01e8a1801ca154058102c280c0900300781807280c0442d0051040b0b10140d00305501e46502002c00740d00c088018103424100310700303d5004589404541080400480099510850700d0100b04000389181d00141c000300c003c068421941803060b114582511f8490a403010f0054505505180c1c0320040e00e00c00c0041c00d42e12203c581c00e412982c0e80c1c4012441000d101405101d00401c0141c0b0f070f40e20030041020300300d001c0d00446466988041c1b0321020141c3c20101184106030001c440f0f6001d00f01445924859a0454100c0500c0d0b2600c0007880b2801d940a400403690540303c0a0305c80617a10b50401c1c200c5c401814503032039500804403c0c8030b602100c40c09090302e0310035044808000082d03080706401c688694030301814255a600d540c0b8010b04c400d003680b080f01e600190b0290958176400f43e8540e22000f90038081c1c82c288100c5c282000202d07240c03100e0340101d1986c0d00d111020b0703904281030043c02981072036000c40500120260a00308510707000080700c003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 611153579 1250 611152329 611152331
    0x40b0103120203071a1506040b030105150309030d0c020c030d0504080705030c101d0a0308030f102315120a20090111070e0a090302061003020d0b04060605060a03 71
    0x10410008002441c0c12001820300c040d509006250f5100c0c614086039009400c070303c031506004945d000244c0c0005c6000c0c60310080205950301e50381c0010744a030b43c0092003120f204e460360b001d5000002001c141200d10454076203010f5880c0c000740c802c404000308803200103201144900c3c150805035440c00c024591407400c1546880da2210724250600703203002d8294209034000d0700b041c6407441c0c0741d03211484000610000d85c208082c980940161345510055807821140d031000c1074507400000d121446008600407041c00160188903981e40d010507462403001d202d4165100404029041c0410598403902071403000108061294044502d46074026000307204000c02e50303c03126040c0a83d0401c90300c10800412601030b020b0001c0005404915101e0090904071030500040d8040340700552010b004000140c10b9a5100c0c00b09030800c05040e20007401c0b01303c0228054031903240402c400d1220203070ba045c1141e41c020244a2103100e640c0d0380001c3d44001500440b0856100d40003c00e5681c2c448010b00006034403aa0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 611154829 1250 611153579 611153581
    0xd0203040f080c03060f0a02070206072d020f040b0d060603121806080106051b10020310380706050c03061003020c0607051602091306050f091009030c020603040b 71
    0x41d2030001c102281d401454070381e1160142140701d49010031019070203000c10b10942141d64820440070041d120700c12000b50b10100004540c0100a9140410305103410314408921f02e0313a00b95404e840e44694031601c0694012802c00000e00b2a2402d5001140744000203054000c100f4210b617914016550740d6081100e600d021100711242059200c0b001c10542e1010b050f213400014900b0700040c00d005818050902004400100340c450000e10514081400710b100c2c0459503800e42e0708400400035001940c0c0076005810041c00003900030406e011030031510200c8a00705140c55070b801442800c135114110070603003401d0309120a0011442500c2020b110318600c0c1c2e02d240c0e90349030850400400411441da00d4090500c1809108840040014421380c410411b041032035413500b40c01803890306500f001030001c1d4000444000c102084851072030690030700b0302c10081403005440c1e4070045540340c68120f0380c1080302e9000300d9080c21070602c50380094003124001c0c10141c101d0344180d00820101c0e441214150381195040f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 611156079 1250 611154829 611154839
    0xc1b051c021f1a09071d0d110f01110f0307050c0406142e090510080105010c0b0a020d0903030c110706020a140f010c170606030112020409060b030d020304 68
    0x21090200c50301d01c0035050350204821102c030503a07200c00d62402107950307403100a51210809080d2000f111801015490180f900300ca00500641040403100100b60010381c9040440c10840040c0902c6139016028504007540c1c2170600c56031b01490b81225040190b0503010841210090102d001b1503c081c01c0950303520380c514208146403001031310846000d01c0c58901c00f0041c11b440004100540c102c12122104080d4010480390003240101200c010381240351602007a0440e00300340b00c1c00441302c095450744d66003801d0a0054511507000d106450106500c2d06c1698000303980404026449004444e0050a002603503c0e540c00701c514509007240800e55413100f000740c07a60407180211b02000d0110040a0880c1000002500c2c0d030310812005103080d502d078884100e0002d0a1040980c1038080c0e800800000b041030100403c0400d5400410400d1021640401c05504052042b68180d0b108890340b00104a0700b9800e01005007140e02c2e0030350300c440d5551900d525a64050180100d1903440794000d6441380e0820b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 611157329 1250 611156079 611156113
    0x6180509010b0304080904090b07020717010507020d0807120609051504050c0f070809030d0834050a03090f1118150f0102120a03020a1407150c1b05 65
    0x6600014403400d040001085440181c0c0200c90780030f60f00240f01743e2110740000200e0007a100f0a1001444440b0b4882000526030780024884120380c000c1101003603044005060311300300d42c41a120000103800c0745511840d002d014408d00307600480d0034501086c500540c014041c080f03d9003034114019060300c46081c001e0705411329101d0381c041030044604001c0740c01c00c0c1181c0c0806216104001c00c1e4984007040b07400500c034015041d203400302805400e0b02c0d0b84101c0d070f0100414001003214040c0d0b5558202c1000355003003d10b1aa0300185220f5100e10100203045441c01f070f40d0b540c100002031410180c444a6800000e04078040000c01c092141ca1a01407a1a00d0300402656481c0c04044a00d03a07142001000030002442c1d00c403802005055941038450740301c1c540101d003030140d00c40c644440640300042c0c0d2a1030302d5040d401002d07030542643c0d82d1066811100d10980f9a4031400d8030180c1098044520000c01061903408a9010320042c24586075808400c048003074002c003400002e440540092040940841032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 611158579 1250 611157329 611157377
    0x6070801090b011710121110050a080105090a0e1b0406060e210f06090606130c05270406060309060b10090306050606070609050d0908030c070314011506 67
    0x496000d0102180c000700081114013074100b0a64880c2003800485c000b070710b54103000c0000c0d108004200188108034240481070310740e95003140740204104034031480500d01c203109440c1c04441a0783c50f004070303900e4482086902107001d0561480141c0d212036103d07000f0002c02c010081c03040f00f02030100300b030300c4188104070881707a07a640701c41c0c01c0c0004c101030419265103501c88404d40e05440b0a038138494801608005240101200d8909024814403003480341390180002e1661140320102c51704101076280030303c0c2000b650707a0154010081030707041c040c030b0f90004000c01c0d040b00c3d00c0505107112021a41e44400050235641c460340420b000c40d540d0301107241404800c1c02480384945094864070010b81d40c2110060070400305202c0500825601c0010880703a54405040314a20380d04010103102514407070400315110300328128054042071006000180b008004030582e01300f807501d8406426120702d140c031507480c0304009800d2350f03089550b22404119001c000a940c0c0018000a075140d07440582c04110100d40030300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 611159829 1250 611158579 611158589
    0xb040302122b0c0e062a3301090f1b0908010e011a12011103010e0105090a05071d010207080303040506010305070905160c0203012009040606080c0a20010e06070801 72
    0x304081c00681d0f41074000002142d030a205844841d55145010403e10603a00078000305806240914a8070700396510028034081c039960131440240403050b9103220031210107940e04c8500c0090045c840100800754044d885240710070319111000c9541a04039140941074072020031342001041c20044240140070092065007800404170008010f081c2c0e45820780c1c0f58009000d13403c107100315102103030400c0c1d2a00c00c3d002000385964a031102038803561242040e620550090042501403030030f020006205100768003406010320303056101c00c0007084c162401c0314200203182c0304080c1548501a4000342201c800c00c0250b20039805040a46200d504518049080208650103108a54100300c240180203100380486090501030341000c1c12404528030110303016014204858021603090300041010303044d0403004140b241e104807020004140ca0b142c080c2c0b0300c00c10564044240769014048912481e00540700c0162950291180007201c0c10061045402e440c19200c000007070341c000c1c03003e01903029001340e18640908 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 611161079 1250 611159829 611159831
    0x100306060e0301200a02070e0106020d030c080f040b0901110304150e1f020d0f0f0c0806150d020705030405120109030e0f10320301030c140d0b040302122b 68
    0x13251500007802102d045150401d4081c0001d13801204500800258004000f07001107090380d9a501d200103911541c8070001d10012904040080614a04c220b141c180300d001080c4d282c105a49540e12041840c0c07900405041c250340d40ca9600c01201c6034080040c0d44182d100749091401c180101114005890081c982e0149540c80030000c2c1405241107554034070320441e8890b006843d40301120801d00079020791404030020f5441c1c840b0041c100c81c000d801c1180e40c00350545030303d1a41d0b10340c1c40920041d0b03c00748640840303040b814401c0360303050001900204030003030150003203908080d00c540000d401007088481007811a99100c901004041d00424101d000d100200d480c1f0740b24850080c003140d046002181e00100f00b0042c2400201400c03554000b6465030b5000c072004a00300513002250704040d5000780020703283c40d50802000500304c984a420007510000282842c070501c01550345681d0003c4010704100c0030b5025140a41ca02190a04003500c1d1041e46108941d1403c41041189005400a415003003001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 611162329 1250 611161079 611161091
    0x612260403080f0304031e0c0501151406070c0308310b03070c2307030302010b03010b01020a030c1a0c0304060f0905071e0b0c030c06010602032511100306060e0301 72
    0x40b805030015a04000a4071080c0d950f40e613500c0c6003c0302c410f15601c0300580c1c600c107018031003844160b004c1c000c06c2c0c1292044000708030b40024610110040c00f032512521000100c40300c00d0241c10b003401c1c8042c29a0038070412800922540329a10f40d00e11b50404021110b031080c42816003d0f032001e03440d02c100c10030b9100920ba86c0c2050b0400074840000c0c403005100105005d160001041080000421912182c1c80c01c0c5c0c500b20148510101151581c00c6807005600540c2070001456440c82c1c103126178855a1130580080504098079902607a0444886205417910034036554030704d441a99010b12030388110031003c0f17207030b0340e030700d028600401180c9000d4900c1d500c40b890144a14001000001e158050720100840106000fa22110000c070f014526007007c042c0c0c03040030440841e070342d10004c094100b0b000707028261051a0389a5000701e135a4011481d01000000c51591422100e07480060b150b608940154056041642c00c3e0001c240e4242e812014400025038420342005200d0b40814115500759080b8001e10003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 611163579 1250 611162329 611162333
    0x601120219060516080c010c020303160215131a010906240903080c0a08120726070e0a0b0c0604050c010323060f0907020105040c15051b010612260403 66
    0x60b01498103001c2002880c913a01209114202d000c0d500003c2c0c0d100c000b8000c915014074020b40b42e40007a03800e94600821001c1d2025894000300d0500d510010f150464801503860300806401600400c000307491850341030b4641450700e100b680c10300703001c0c0400c0c0002040140c0b0b400c0010540303400c805040d01c07070514003e0030410010342c85144c0d0402c4903008840130380c90f40c15148090f400c20390302c0e0400030103032240055012149910418000d11443e001c0d22020b0b207424141c4038120b50324a900e100079071202c00300c000054580d4010000c0c04112800038107010401c0303454409910041d0300042c6070480a5020100700010040c08200c03100740c0c92002e00c2c0034042014009a0480812000010420016102c600060058484401c811205640184241c040e824140300c064001c2401f0b541c01d446801105030046003120340214501c41088256a400d0324018548180311040c50804204003211354840307000007401c402414064000b02d000d0902003100303000d030010803c1040d43c3d0030200013103c0d10520013000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 611164829 1250 611163579 611163587
    0x50301080a2019080706030504021305070e0604090f05060a1206090204090b010e07021b0f040b0d05010c0315080d14031005040c1205130203070501050a050c060112021906 75
    0x4580e0700c10a880180e268220614051600c0c0514040d008404900550440900c0f10703855002c0311500d00c2661030036030b20745130100c091359401c9a002c1e401003204000e140040c00e990340456805016413505541500306d43c00041c200d548103501c000007090b00d941c038081010007144241070b002602103074154105460156402e0149102402c060403a5aa0b0035082c015034546400c0b03215980d6001a0b41805076840e0000342c68410402e0700e552006110f540808019500e41003d800644540100f90010620031181008081d06900521a4001042d0b0040000003130b02401040320341c41c800e850226000c00b42c1c220303440c0701d4429a8000381d51680506a04252640c0001d880003004840c88040d1f41e490703680e64010020b0251541c012604645010034014441c1e9101102e010381d079090301c030140301c151982c0b10000503803000300c100a545504494410001036000f0001006e901d405414101e0410010ba66010b080c200c090b4448516080511000360840c5000c60940084e009120b8201c528030b818031000030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 611166079 1250 611164829 611164843
    0x3123c0c0c180105040c02100603050708070906060507080903010b12030a02160b07261603030f02120a0509010e030c0a0519080a08060604051309201c03030213080604050d05030108 79
    0x6030040c0d1b921581c643d1070714400d125a098000b80c14806101842d624900319a0310300092140384654010050003052105180c083d5400310b90490381d6080c1010078640f5648190703404540c0a907410f40d41c45030306400e1034803034103c01c000500e103010103035884e03001100c000ba042004052051035010304047d01405110b8601094039115078012416500700e00f1035030603d08403050b8000a40301080d001180c0c944010103010b0403000a070b44030b43d901f800301d4021868040281d000e04806580c031ba00c48100046c803290019030015500400e018000700300d070002d5294480c11680320380c82c5054160404100d8805002c030070428400c825481d200c07400010820342c1c492103003a010340b207080c50400c400c800114071315903101c0068401509004103000c0034404405034140003400001811a21070b14406e0035110400c1c51030084d171ba050326000c0d06100d065107450303c44503610040004110141507081c010b030740000d2004030408001e01801001801d072814281411441c0141c0020b1340e20070440c0400041c404200d001c10a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 611167329 1250 611166079 611166089
    0x2d0e060612060415150e041104020319050912040306050103050f1c030b01180920090a14150c0a0312060302010e120106031e0c0503123c0c0c1801 64
    0x2984405001550705130241c20441144241200c1c12800400c003030756110391881c0903d116006224480c03c45c1030030710099000448004005621444418014030095000300b54402000c00664555020351306035040c00340c000b030300709592041d5544010300804c80100001140000c80c01d0007030111195403400c080e0680503c42c030403810580c40356940d6170303641d0140c01d80c0c810346110680030341c0540740c8900c645030007024950f444030b40058031034aa401e407200031344045640824000d4801c1a500b420403032525200c001490a103034202e900c2d45c0c12880403150318000303011040d0041026191148550400a06240d9442c1c0341c181050300d00481000181e8000c1c40d51914281c064800c2c140d00f24522480a0060603a50710140c500ca9140b5140d1501484100441074228440d40340d180000d61120180b60341e44200305904001c00c07a0401c41d14110107400b0b42c40c00c940d0142024a001c041c03280f801040705240800521034051640400e007024115410701900d80750700c4098408040846c00d140700c1a100d11818410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 611168579 1250 611167329 611167343
    0x42303011104031509060221070e1f020c0411040303090b03010f0501080402180a0e160e0c0309121903060902030610050a12061401110304182d0e0606120604 69
    0x1003202c1c0714400d4101c0039117260000811034448051102140b842c202e07600c40c00c021882a0000a501c13107002e6100d04101d880c014203032682040c48002d99002502c0301c10048400d500c1105a66802c9540c3d03030040c410940c0c0c91595458589255140280002295030822040d00000380f0050000610170700394403089400900e40003600e0b8a4500220b01017002c003c0b4544000101c1c0010031801a50329002105280142c80480341282608120007080781140d0040385902500c540201e0200c1280c44041e542250f80401603900703140c002240c402075644414090848850a61101c4400c10303010f100d42001840d0303282d0194a145028800110811300c0b903080117050080100d4100b4a8510070f000c58034001181d20000c02603a500e03181e000201740c9045643c14005504010780740400e500c04016a800c507002e6000825258120b20445009041041140d045003a0300f04a100d42030444d901003003102c455441f0000a40c41c212808403401d1090082586001c0d00304101900154a00094407a601c6070304150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 611169829 1250 611168579 611168603
    0x8070209060d020405091605040207030519051c0606090f270e1203180a05120304170316030e0c10050f0d141503060c1c0e0304230301110403 62
    0x2d21150700640002e90400d10300b80800100d9240060201c014105000c480b11130580e90300d0405c000e038452581d0050014500b400160344a000d9003a0640b520340c210b00b4140c2c2040814206a540d004483c80007201c02c41c3c5070305080014a8000c03054101038a2044c840584490914000341b41e41e03440c8a01c803003500c40c55041161329810065000e410b041c10600706640c11021840900c840380d80050300e42140002c00c003218414a0352000400b054442e9000c8007a044400c4214141c0e4100c2d04010003c0c0c41024010002e11414184d40d03000b94400c42c000c02daa180e00c001c4201000b81111015400c2c2d0030264095007440e24640d849070507207004108203140043d62074400c41c0c841845402510071001205007064260405060032080700c034402c3c244001c2e40c0c40d0222030b034800c03d9960142171754540c18410040001154200c000122284824a400400b1500d41d41909000c0c0c0303954441c2d0b00c0f0640300780120080941000341c10310405080b0408600034041c04846c0d00d4243c51901c04c91100401c9005140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 611171079 1250 611169829 611169841
    0x4031101140c010f14040c0302120313030605010e0f07080a0c030f0f020a1205040b060d11031f0c021b01030b03072d05030d08060f0a081009031b08070209 68
    0x4010748900603661100c1500ea0b02c5006400d030180041c0c6103800c404c241003860205400040c00d814500c102e80040b0181041450350302403109200c1005d8000310035020812002c181890f11202c3e00b0020340c801c040020341585848201c502c038500c0540320351030700714411b010700c0442c1c1c2c0c0c0805a079404c400070402c0003070010031060701580241650044003040c281050550090200640d000e0520010349460b0344042c40400b44c910011180c3c210750041c03403a0161130108010707042a075410001d89102d8020144c07500a440c000a180031184070941400d504801c0c400303100c4503050f00844a80b610540002d110344000340007900da4a181c0f070086e50381015603400d40f00200d680e0070490980100402c02442107030919429030f6044201c4681e032034407400030740c80b8400212420002904403108035079594910b4141c40e12801c01500300024010151700c2430072184045003203442845010a91160803400080e0260b441c074018186012411186003400200061702c1d020401e04012102090ba040340c04000b5903a0304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 611172329 1250 611171079 611171087
    0x20c0111070302120d0915140a03061e03061104080a020f01170a09060606080408071b0f06051b010506090a27060b0405060402160f08040519030b01060c020604031101 73
    0x39030702c0a580180d21314800c00c6501c9020176000281413442d56001c40c0c290701e83c544100c0402074500e202c0001007540b0701412015404001400c180981d924010072495234070842d014000403461421508408120820002c200e0540708940b080d020442c070440c01e191510b0b41d60b903207410080c0d0020b4014841d1100d14081d036031003814983d1041400c0d903062205030600007a418000c103d440e40c05c541103881c194010072614010b00c001807145034041001031400c1c0305a520f1a8520003480015000c8540c0c8081c040b138002040c0c41c141024016594410380c0b1180084914004441809209002030740340100340410340d2111002070f0342c02400404089404003141d2000202c4101903804410810440d00000d41081007982100610340d0046405000541325202004124030950500a04c00b1511000300e500007200b0005264007039001c1c1d240d40741010768580114040301c1c2d22011111145902c0e480520070004d00c55201030250143d031410f80e00030210f543c0031400794840c41c0005040000140f111240d00da1103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 611173579 1250 611172329 611172343
    0x212030712020d080604050f01211401020711090c0405060f1314091005011b050106050d06230912091c050714060f040501050a02030f18010807020d020c0111 69
    0x1004448400d4100d024070700035241c0042101210000da408000b0803840d00e400c0c040c0e68042e401c48011541c141c3d2a01009044041203580c4081c02680428000701c0840c040406049107403c084001590305c4025140895004002402003445a08106c051154100208003a90140c46064a22580e1143c0640700540e503401410008500c103c0010004a126500000c822a401340140c552443c1c0351215100c0c1d11716000309000301c900050340d0a004d1502c0200d01d139490340d00f15004100002d03400d915207000c25840b5820070015540c0a03100c0c2608016441d07540e1030801c0b4440c0d0f80c003500105041000c1455201d00707034221051000080490398600544e500e03404604101801d02620b41a60410700d80356848807068444c50b54603619549001403903060540403102d4440e58000c84070324007401c000042d642a00080885000c600c405e024050002c407a40340103010101000d803401c0290f01e4500001082105c00805200854000d400580d152940006080d0399140003428114501c10740c5071483d51a00031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 611174829 1250 611173579 611173583
    0x212010501030309030201030b0d050c090a110d05100f030b010909170c010b090a0b010504090e0708100b0301050c0f0304020409051009030804020f0a322e1b02120307 73
    0x4a800e00000405411640d4070301180d02c04c0c0c805003d078080002c1009151444008040d0803500304401e003441c10700d80408100e0f40000d10300000030f2105a0403111a0142e003183c840344c0d25880d914001d03c540203c003030f426207001f402c0050340b0b03201c400c0c01c0d0f41d0fa8040d511010b1040f070740c21a88442c2d02d0000c00906a0040e11040070340a19030b901c80403500741e003601801c603a21446010f050b800010813410515401641030108040e1a018585072610740c943c8001c044100e803126050040c1c2201144400060000b0300c0c0c0700f01c05010109200380801c04150840f840548040380800b400c00442a0800720002901c0e0b200350102c400041606050500d00e003442c995110800700c903132074070702c03a48205038221034464011070080d034140400003074a105100d044602400351022001500c81100445c581c007481c41100031440803820a2a00c401070302280409100e041c946018511100e1074501039102d100300040c01008901d802e20802c0d400050100341400000380290040310162102004000c00700100c0d04411313 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 611176079 1250 611174829 611174831
    0x8070f150e12031e03060f09060d050609070317030f16020f061003051204061b0f081c0b0f150903070f0b040609081203070804022205220c060c021201 66
    0x840910309501c961150b0401480c001222103858010300b48241506c2c82103101624505a030324846041001340c80005015560249404224100040081c050680602c2e400001844603d06602d01a140813918040c6140c0007003080c4100820aa20050b50940200c031f5900340f03100e8100101c104034100f082084504040b0312461040c80000b070f050031380002c1164021000e8070b6241414a04e003540a00c100c0c800d940005400d14513180300c942040d208d0321041403286000b000b000c15a40e564440c3c40d0452a003100c00c211101c503c3c400b002d05103015103042e40c0c20488104101240d4603000404c2406401c9240d440598042400085ca8900b0410301000c0e21098000104265072400a075a05174042e000314070000380b4542000a07240d000080e07240302c2940003000700b42503039641e580448101c44024416a03002844250500b203c0c0d1490990810312002c103040400c2900d45900c541c000b004541814541c850742540b840404544500e000100707451441ca04201c1d64110740c00000d89980d500c6d0340c1d0b88055 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 611177329 1250 611176079 611176099
    0x16080622090c08061504020f0901080903130803070c151403150a03150606050703050301030209040c05180108011b05041e050a080f0d08010b070204091b061808070f150e 74
    0x2400b00280c140d205001d0001701c03205645408062005074040c007913990b0074001c03007440000300035805040704943c00072940003160308000b2184170600090019900c008000d420014050b81030114406800307001d080913007041c00d491400f0308001002000c50a06054807520302201213244206820100740f07003c000200307414030440d2641000c18040c010303002c100c03910910303101c400192036001c1e8050b100d516030107444541c116861502448503d0304000c1080759490480360012540e640c0c0c08640c0d440c2140c103048001c1c243e41c142a101d0b030171a000b202520320030318448500d2001e4503510200f142c0a803400c0c80d504840c06000d603140b00074032080b981c00559126445079800b1a00f1500011002080c20b0354504550000500005c10340e5160020701958800c0f90302000044c0150400790081e49525200b00343c0c4041e622940c0000b482e12030255042100065007940f0244030384046483e17460b02802d00b00300607010b403d1030000c60041003072080c0306004072007000c208503e406c14082d11584142c0030001c1d00307a00d51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 611178579 1250 611177329 611177339
    0x6150510170604061716060e0102030d0e030409090807060b010e03191a0c07211b020d080417060906070c170d020f0c01200a031a040c030516080622090c 67
    0x45401086e00e41d240d120481ca8001256840b0b103901003200071040e000b03185014030701c1007000f0180c01290031005040c8000c01000170152100d1244804d99401207401e140c903882030b8506001680c011204260411a03042c9188a990303a0200c3d40300c02840b0803c004080102007450188109402040c0400c031208c080410800c0780b0481c7e10081018a10585104491016480054010300144001c0100042c082107070342154521111030161258002003007801c00b000e16030354048044c2e100f074018520f40f083e40a8008a014400c010070390704014000f001d030900d450246001003050006810240c050054100c8080b40340b814030080b41d00e207000c011401e40d42c4100108070303800c4907030109051502d190b10b0a82280e103004d00c0107901200701780580607070a01c0d15182a178114060000c02c141540311142c1005210020364847c41207140703a003095280801c02d80b80034518048180c4400719204140100e450400030580e441080c0341d400c02c056a42c0c51a03c030b688000d4176000500e6001801010096a1140407039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 611179829 1250 611178579 611178583
    0xc030503030a020c07090c080a0203070527010906090b030c1c0e07061e2007081504051608060720030307030b090a140613021303061505101706040617 66
    0x312070189102100e0003650344046c880105d484201d00304c40041d10b01c0001c111803202c0794000795005030741c0386070050501700040071001d0104102812100310404070000d4008650708108180d00401e1242041038039546020b648420358400100810040e200014940080f1050800e400341447d0345248104540e111910800c0da480c0310900414001c1a038504513180ba0110a01c0490b444203841d0b5124000701000031141c0b03e0001c0f440038141d4050180344404110000100501419401600000200342c10b050412508260038040803000400c4e00e0b5009011540340040c140b80c008185240c0240440c100e02c015444460003030113140510b00000049c80715060303054221141d00c100c103d030281999200c0318103c03011514a106124003c8000b40c000990030724165040b001d81e1b440c250009440e21050401d07990405e980ca410480300159207003440d2860504900b01c110160105540408a0f00082c900191038a8501c490b9411b5040c0480000750090703c60341c104100501340c0d40c000480f40f105141d050380e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 611181079 1250 611179829 611179837
    0x3030a0c05360a050f01030b04270c15170a060b07060207050f06151c0206040f150f0c0b13080309211e03040303060305070909150b09060d0c030503030a02 68
    0x703000b41154001c0c1200c645020101c0307800315040240b4244554550000642c094501d1410495000d5951310201c2c284050140750321100c038510416140c0402c08503e0844c1144031140c2044081102944c00607045641125081030700e80400d4202d1540c0b0303510426032101618187d04043c1848101040c28400c100c0c0319000b40c826903101c1e42c240c6004007040c62030346984040444200c0107c041038000b0101c6401c00e4203400440301d41c0030401c1c0074180e403d90046485a8801c1d40280700050f03c402040084401000003804100c401c0e103401c88185044d150020310340d0700600d03405085003110310082295000d00d0410010495417051500d6100d00c2d2542c109529920700d40211aa40810390004c0310000300d403801180d043c02140f030b5001c403d01c000c10301142c045804c000c000b01c041c0f690b5040c2c0400031820070071000b001440761120129003044c0c5840c04a03000417800c210108114100341c50b516043c0c0c0c0d9600840e41c002c0c4c1c25075a01c484200c1d00d08202d00c0360300841e40060042c0c040001440000800c1e03800138 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 611182329 1250 611181079 611181157
    0x70803070f061b0813050106260601060203131404090606150e0103020903030a200616110a050c0f010309060f0506010305010527270d0908030c03030a0c05 68
    0x70850b440b0f10000b500c0c8001c0d050050000090070782e00c0041c14204491500e00025400741e0000a100c43d147d030340b0741881c00010036000f00b01d2050ba000c1c1000074201000803d0252030300d440030314203004201c5011034021086001d07045240c4401d20011640f41c5681d03004c0000c0d81c0d00007801788000b40c0d8444502c002c251004d5034090000b11a0181101c0950007030088985404c00503000f14540b150007c0e08a0701510780c41050440b030308041701c0b0142821020002d07240945a948088555036805440181180342403848082d04c40d0003080c0e880c008030b0008600104054001d440d8521100c1e04000120000c3c00382000050815203000084020100e107a84423911a40f000c1e201080b0b242d803200704000c1d10760900c02c6241e03c0c40000358842840304580a1030700c0e0300b000e088180c0c2d0b1801c2c481400102d40e4204078008000c1c407507100540c40e14800c0c0d884030440c001001d02c507000d103103090703800d049d903c0e22440010007000301c0c542c46000043c171081c0324404071600390324550b17a00c016a01d1081c00400106000c0010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 611183579 1250 611182329 611182331
    0xc0f150c0302180f0f0d1b1d16050921010507020c0306070302070206090d120e060a02071716060f020f0102090a060827010e0f0a020303040302060309070803070f06 72
    0x58503960500030b01c01c80c1c410040068603e0101500c0e881041100f0b00c00c0324a95400054600c51000d054075080070183d03000b4802e2000007500c9200c036481c81000b00c499884004c0e51481c0d5291450308046604981d1b402c030f20f4200c0200c07507a034030300c40e02500c0c82d209030200c5a82099a2086205441c11090503c0c941e94064030000e00c400d032908041240d858110080f040e505030011401310300e46502942c02060880c0c4040d00325400c04004a00003940c00d504400107581e5000080d5980b00380503400400b000c01303520101e440d981040602c10000b55a032201e4010b01f260402503503110300c0e0000c0e0810100c02c0c9400c0d10000240000c1d02c8071001410b10000c50032590141c07264603043d6010b041c045c001c1c1c883d20f00016052540c030314602a41162110f101070440960044100c08041861a02801400d04486000d0000c01c8144800e81d1091810503051a240c542e9040340b0900b60043c5e401104407002c80380c04031245030712511920b40d0b5604061507544100300320300c4000380d842c0c1002110f00c0100c3c802401104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 611184829 1250 611183579 611183591
    0x10606020618060f090c041103010503010b12120f1306030902100f0e0603190c09140d0203060a0504021f020a06111c1a090f0a050709140906010c0f15 66
    0x803940011032031001003a2043d0012030004007550340100349194811590f50442c0e5001040c90b002c2021509100201c1c0c050440010040c01107041c03d000701480b4110030380b0415009810448880d071180d1018400590000700041e41b45041c1c24094283c4043c205600101d03294a45d844801800510b00d03a03600728002d4034500c202c407240324000c065410141c80143c070303400000030b03881d800c00149501c010b040c680b64103101d08101e255040703070748500440210035403100048541070000d901d100040d000c008500c24401c1d1610750780103071004908503421030403480c804101c0c2c1d00c4501c0010740c515000308a40c4481e40240c0e02c0550305030360010700c6511580c0105810441c1c00440c94542d41341d44030320344060b5446172244580b41c0390a8280c1d441084070b5032840b4200800c02821500007992402d054407514450100c0c0d009101c00f4014034031920760854007a007400d800162400108465101d450480584035800240000c6e01c180d015030011401030703a0000340a41c04624500d031400c1d070800340c140c0204500349000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 611186079 1250 611184829 611184841
    0x11103070b0f0717070e1f020a0f0c030f05070905070e0d030c030302130905041106070f151d01090b062b2307060318030e060c1c020106060206 63
    0x100803039264035044030301e203180c940e5103002564403408003070542400c01c41d0012440140020070005a40113101c81d941d400c4400e44290f04100500180d5007481002186142c011400e5907000100110059442010039903210fa8a00b02251a08003a50010b0240342e034a54414003044000b0860100380c80c610f030402c1140342c540600448140c40707807114598108040d58070080100f8001c2a001483c07910926016107032142c4c039090014500456071000890944500a100030480c15100c1040701e03072400d581943c1030207044e403a51074002124800203000c1c145018030280400f0f0554125514040c0302440101c4072101c0300840d5030003400d90b00381c01d40d04040c01c1c1c008945207113841e40030302c100664a0461b03401a820441291251901d40d00400c03903000301a4000034051446072050110600390805c00341498030f00d040c1015056881014014400c00b00680110b800240c0112905240e50800d907946a00e420011030690314110b45052000200e500c507240e2514095070540000c0191456039095070400e40b1a8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 611187329 1250 611186079 611186083
    0xf0616090e01031e06020d0926030f07050d0203070804060e01050c0901050a090905100614030613020a12060b0306100203161421030a050105030c031b01030605040f02090111 76
    0x5401880741141d007000040020078800c0400b15507a01c982c07400d10300380400c5995020200d03401031b00c84c50005900c6010103028091280c07101c400740e410700381ca0005071002c4525042d2641c07000800ca6000b50482401240e08503100e036043c1d03a0540120034007196642400240500341e00001c440803075010f81410314001c0c4500040c040d00380104005802203041001610064803903811014100c2d00300035001c2030008011215006090045100c0f1200c0c0110038200600180b03071150b6113880e1018000200140311a94507441c0489a00c003450740001030b01d03880d10074021182002c1e110501c2031810305012011030601c04810040d4003401d411034529a00f0400c85105907224000c82088a08660882a040000c5201c01e140c25600c0e020791001d946452120300c1118101c8c041142c0d144c4031a683c04410812aa8450300c00c55014207811401000c03180c80d5000001e03510b0054120380f09c1c204042c0d21011400d64041e4000001401e030050040c030040ca20121203000a4011500080c00107411500c010801200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 611188579 1250 611187329 611187347
    0xe01080c0a0b1c060905013308070908061816050609040f02090a030303020d39120905010b19120b07170403020307020a0f0602030d0b060c0f0616 64
    0x1030500140540380102c418000e41003200c00551a0455105104088085100e160003501700e50388009540c0d4101492080640c2008455442a600c0d01844070320340703601c00d80c181186101915021500f9650440201e501c8101548841c25600c02d01d018081c0902203001e041c01c403800f100d0201c0e9003d0042000509241c821403140e640c00403400c101c50040e60400340c03c2015800401640903280180c00804500c08108650040d000039030f010501c440c5e10020f40c0610f18000b800000d68110115498040c516a802840030b051b000c6050700010810307a80c040c080328081341544110820908910341400c6000c0e0000d410810302c164003c030b50844249041c0b40048040c4d601010014108103650307031700c8000c0c150303000d0300384003e0004002159001c1440c4408031303032045100f5070145031180c07810720500180c64170031b1304070301040142ca250900480c0e600206594001c42143e0010801c502c5402c0494424480c8207202c140c1402000025010390000181e424001c019040e81340c560302c40c15050031988084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 611189829 1250 611188579 611188603
    0x170909160e01020304270b0909160e0103020f010305131b030209090601060906050d0603150e0d17072304170601090e0a0201030902190305010b10022b02100204060206010e0108 77
    0xc150300f0304d00260a41e074806c0310440a903085c40003d0000c1c4103000120014003c44204100f0703030100c07a901102c3e42036465060018402c10305080b505505650014400064803400d0f0f604041d51b13940080c201203201c14814031300e5030300100c02d240302c840100004840320607107000903401501e0384404103403e60400138145040710a6580d504003a02d0411604070781c66032143c14140030300380d12084088041a1070304140300a1041440c0001030308544020f2942c1410355003007044081c003030000602d001410380c01c2c10b81c1e44c1c819040d280185036460105104050000c1104803a00c41000202d0041410480c0d5508880100c4440e42200c0d2240e0340e403182c1c1401c0d41d50038600c210043d00078542c00d1005500a8110140c040c0c40100444180301c400310326210b0300591680b050301d4aa44881c064802805c10290703844041c82d403440945101c1c180c0301465840154500715651032010808880d000581c820300200401c051481d00a6541d140c3e5254002c0d500c0c54280100c0b0001808139000055182002905105003c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 611191079 1250 611189829 611189849
    0x26090307120c0e01260a0b01350a02030601080f0a0f06020405030604050a060e0d1425050c0a1502060a0b030c030f01021c020f0304170909160e01020304 67
    0x3504140019840e154500710071540c2c2d880b6004042032450f400203443c2d019001d14003043c0c100303019040c400740740f401e45401807101907045540f408021850150034507040d5039070644100d8031261281da102c0d07a1110004110070304406141d6a2040c451300c08a1881c1e06940200d0840c0c0c204c0e40c0f103c0d101c80d04c442017400004c0e1694070007002c00d00015045000d07081d519008410040c1403942d907030040b03420101c2c202d6088426130003806c00c01c0108091072203416001382811002b4000c100c09050082e241c1610b112030754500141c080b03100d00d022024440001e901103801c44203c00042000d280c4282c1d1800e02250301c0744681c0c1c2c1c800f00411010054503201d04008040d81c01040a500e9544005009160441025402d802a04490510b070b46041000d00d40340581c15000580c1c410340703000c049040d40b41e2a0031402c0c00500420a20040c901c0c2007080c3d030780064001e4440741c1f1125070010040d07120320504882d503803c081402c080002c143c40b0880070020a10783c2d41c0313500550000d03070001244c4030320440c02010307651 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 611192329 1250 611191079 611191093
    0x90c0a0903030f0507060908030f150604061409210d02282a0e100501090b0309071d0a0b03010c0519090b04080d2006060d03030216260903 61
    0xb00703110701c002e050b9603d280e060682c40d102c0b40ea203075142926079000c07095420910001c18000086680f41140740d010400240721002081a00300103002441103200c0d00c003c0010f00c03400c042c20b45424000f00c50480e8001490205105600c030b50641c407000c0084d80c41e48032806070f1a10f00c182d1754000310381c1c83d00000304071919110300d14801c03210700c03030005003060156800b80c58040190203c0200070800ac141303514188040d42d58a1a00c01404000c200003407001d117801144110400450742c121204005a030300c1d46a400c0d480b03684854031240340003070961049420b00802c00c4001c0d400c6500c02d502d43e024501c0840280010400d40c4107160a039403001c2e40d8080092001c002c1603c0c4414490201d100d80d2086190420301d441c1da4400d40d0841343c0041c1c001a2440c0c00c42990405200d03085242040404680342e0200e240314000380010ba1035440c014507d074011040c008081d030030140300394100e62402904001980d40c1c0300f42410038002c1e001502a40b54000b801240183c0e03244150203081e6501c41400400629903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 611193579 1250 611192329 611192333
    0xe15060c034017150903030a0e070506040923131406060f04050601021e010e15070c08030c071505010302090c0705071206141f060f122a080402090c0a0903 68
    0x242600700f40c541c085034019241c4051142e92480701e200d0169010400a44c3c03207042400750481140da61103101e009035404800100440e48415060306c0480d41002c50014085150818244a0100400000101d980c14000300040304e4089504a100f542c000e034025585805050007156681c4010703500aa40030000d00300c40c070160300e810f41141d588008180306503030f02c240e0884824111070300d215100480e1a511243c3c00840702a0400c50f401710103100310729210300c500f41814007900f200880c4501400b1024000700180005908004465500380d2181010469154983c100c0008090a0104038810b0f050780000c0340d44141b000c0d040d6181c0325007207030244c0b40315440c000455020010350401150311684a2520f240001a13070b03c54107104420001100c28204680495408800348580156042c0720b2801300241207158014419000151803941c005940380d1182a04000c1414007a00c512075815142d5100ca0034980c42991213000398030950702030740385445201a034001c0d401040c0080c00054099541000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 611194829 1250 611193579 611193599
    0x50601090515040e330f0402060304030f090513150b0f0a0e040f05130308010b0f16150608010c1e171806070c15060e15060c0340 57
    0x2250a034020859802c1c03000c40b403a5000140602809190345d41d5020220880c00c24030019496200f2215400750345146400d070700141d0f245c08054006800c02040c402d8000070315014113440c20140900410181040d40c0340b8000c40007410f90440d00d4607181d480103a000910b0005c5105449000011a51050918030064411110003450291032540540ca0309900b51000841d07105444c0a0070350403810762041c8101f070801030302c10380044e40030a1003014100203c03c5a03441f924192100480d40c000e0480b04040c2034100506501420340c1161304a174070307007040010882d8055020184110039925144060424941c1411600c20480d01110115446426014a640740c0c0e0311342076440012244d001c032030f141c0e160500780e151450448064010414180080741440343c1c42c00514041142e222040c44203900381042200c60100150621825003e0f00c0c6a00040d03985807000e40703483d48080d804582d281c070604805103000d03201c03818415070400310780c443c1c003000d01001070340398442041881d007181c07492858044602 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 611196079 1250 611194829 611194841
    0x12080613020d060f0602010c110c1309060902040507030204060216030c0303111002040f181a090705090d060605190f0b18180601120209031e03160f05060109051504 72
    0x3000090f551400440d07281c4004413414081c0c0540c0d0b00002d80900c1103800034102c1007541910b18080c0d440504036445a0b522456113500c04090f5520114454582c0c0c0307059005043c00040007980305082c1003c024040364113034042c00449681d5030843d841d040240d00515000c0103507010107026103295a00500c046809040e0b07610042501c04219108492201001000c0f80c0054200c2c91a01c03c0e00300c000c100e08580c2076032420b1100c004400c10001d010160030842c01441d00035040e20b005201880c001007916001c1c5064545e542400b400044100c1c07000c2c40c11600901e42d50298500c2460041115011068007100e003002b5500340c0740c88108410309060220285411080740700c82c031041e50a52040d06a16042214015a03102c10710380b600320f052010014150f4081c26030b225401c144188198451a9000140d18484445182c003010100c200c484c4401e04605c5890880040320080300c150000f00b04001d590803031964028800c0e40c074981d813500e0020741030741c0c815642080002481c1c40d040d141c51030194130103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 611197329 1250 611196079 611196097
    0x1090e1c0908030403080d0c052703070f090203010807270902030c0607050c2103091e1c120e0d1101020109120905010320070b18010203040605041208061302 69
    0x46840942d5841800d186034041d410031501c401010600c1070120043d40914101c43e52241012414803644c080105c01c00090300101c128110011100c4204644090005001500400403803140050b150541d00d0060340c800c0c0b04a81851086c2c240019900301d019050921051480191540d1500b007941150040e05500200780da16024142c036010495481d00001c2c45000d201d04050403100d2070210401555440780c00d0003074503940e80c00c042c500795503002100b00c0d220417504880980204116a01454001001c50240e6822010203540308952407030061441103400e105002a880c5080c00410445076010010b140c0c907004689101101d00040030400401203a142c18130001809462940b103046403032140110b01c0c004500a00c105002c00d59140c000c030620321407184c11003500d084450003080c42c00e00c22041d010b0180003209002c204100319200003d402e000610001390344034145803c0a500816080d01c0c11980c080800517036251042c0035168142c801ca80c0103050401d00f15243d4014400303540082d1103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 611198579 1250 611197329 611197337
    0x9030206030a0608060a1d0f0d050d090503040e011e030209130212062a040f0509060d080a05120603010c020a150f050c07050d02030c030a0f0c080304110901090e1c 72
    0x414050001c2003854401c90aa11007c5131212050a8244c9a50722120018090303400500c40110b24000c0090394854603036107460102e1755426034503200c100504071200010800d00001800007410840036520b00d047c0c4207840150320110303810040d0855840454400203402c984298005010112102c2070100c07658005000c1a41c50850b4180e042d081140407a450b100100100c4c7c03443d400c0302a070041d002c60915444a20610700382c10442001c084280502c64a8440e41a20300002c05c00c0d15850301d854402c0e40d100581c180c540303000c81b00c003a2140d00800e85201900351110001485480c0500410180c0340c0c95401514100c40c8a8403440010300c078825402805a85464062601101b5481894814041040c1c00c0b0707210307181d916102d41031800307240039442150302c00c3c0803201a502c008800c640445596090004214203142001ea038030302c2c2900e1001c0c00101010040100b0b028842000310040e890480701c60107540e803074404d110100e40c40c2c09000b0040d43d1000050b0751640400e82c0e00121a42000e0074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 611199829 1250 611198579 611198591
    0x100903030b01180e15060304060606030b15070f0302030c06042a06080604050601030e0a140f1515151207020c040e0d1812030c060f0b13090c0e0c040501021c09030206030a 75
    0x1041d447e50040d00c080f81c0907940c0760001c00a141e458807620b00b8145040701ea0012103400420319011a0243d041d0281c25030390030704408000c05008108441c084d20540080d00c0c401c0c6003e0602000706420201140742010100010b038034550007114409040da120fa44402060381c89000a100041500503c001c4c145039550307107003002025040060f0000c01d0f22409050700c13800c0030328901c00e040c216950761f0b00d100d0368490f0940701e5019a030860201d90205850786190402680c1100007003580059000148803604000f8401e11641d00e20034200d841040c0c1c6030200c8502c1403049052108036180680d40850640091503507a41e0a8850040c1c0e032680c1803a040344031a03040d00c86958264040f280c08088000c00d14007802c40042018902030743c5800030307420b1400c10110700d00001103421080d00807119012030740e0b036102c1d510402403420710300c00142a1840c40e89101d0b00e441d00401c81141d200d070096074050301c00c1ca01a0700750030100310441c0e0102d40c0356680f8039096625560900119400250006038126202c070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 611201079 1250 611199829 611199871
    0x6040b1b03160309050a030506060d05010f0614100903030e10050403140105042105090103050a1d0d02010e0601210222020d05090c090c0a090503100903030b01180e 72
    0xa003010111140582c1070203001454040e0071200c0075804680517181c00102040410360114040d80c0c03204083e02c5000341409180b402500400c0c09001107080d09140450100785612201004c01094406440a04410010aa081e40e05180720703c001800222080c100b000c0904014181c065100010304180742050380343d07500d03010802c15552824800f60f6680f020041401281c80840040380ca6110b207101254041c248024080e1143c4184581410703201c1010030030b14110b661100407020450b901c031414000b403550202d500d500c18014200019070170080714020052020402e07504854003162645c203181039950400301c07080100f4070241e0380100800003002c3e072500510202080c0c084d01c030400595a65100368901d080b03d0002d00401d030300380c0c4080200030b49901e03201c020300d0300407825484244d00c03420506000c807104001600044d4040c01209421601904190451006e06110752000d0101c560071034011507030151601424a01c10072500c1040044920846055800052031000f01903c00c40c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 611202329 1250 611201079 611201083
    0x303070b1603181106160b15010e0406060c14011509020310060f23040801020c010b030f1903110c09130b0901050606040b0f12070c140c06040b1b 64
    0x11078080d030300550401001c000165061094541a9400c607411034840341c16500c0b0810030740440a001805003000040d002a0203240c045140c245a0b4400c03e444014070701030341501052080081d61501042140319035900a180c24090b01c3c06548255841503c000a140c480d5010004c1e694110324495507106c140b000e00000c0d201502020300f118a10240e42c90610b288040d042c0e0307001d80c0c411307810440c240e1450f0000c20392015140e40b00c44e01202c615540c0c01400d60802d0104c3c0316540c0181000c3d1310006141c3c035402c5040d00990300b440b5048041e1098078280d505035548509902c1120f0a00346810100d000019024400020b00d450000f41210141084800410300c40c480617548101c4000c0084503e0042100380d058441c0d022203110300900090400801040240c040e0740600e1216030350100d6015200907480003941c9413803106446042c0b26007840b09002d040c10707140540544409003006000ca0f00c1c2c038000100300d10550006085d113894580740c12980c0384c8542004c44290508140004001c0c058141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 611203579 1250 611202329 611202331
    0x1e0b0d0c0303020718050c09280f0915030f02120102190503090f0705090c090d06060e01051c0b0403201c090806090a08090a120804090c0305040507140303070b 70
    0x11a07001045a035091441e000e05840001750380c0f03083c090401003003101c0720420105a490072402500c8210f015848290009030210125a082150120010001400002400780c14003100c0400c8010049a05070040f1080341031071501000d002001d00c400b04400604018810140c000f8404d0300050510616402009000440c0f819902c0051303004024003e81034014040c0c0440703215240b0042c01200c0c0780001040340e0340d100900044940b1404070305000b260b180d41c0c0c1400440b070382c0b103030040040c161107003094a0101c401f8010b19004107130712031800c1c200340c050010f40501c940c0c02248200ea00c0e50782e681d0844200450001d001c00451150701d08800321101000301e601a00039121089804450f602801000d00f03503241e01019480e4044400d00c0003600c80454030208160700089115a54440d032800706400190340e901050840310928000400d1204020140041d1885442c0a0015408044048003510001e40e000b610503084404100007040309410a1400b03821b0203800d41341020980d4440340c1280d98 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 611204829 1250 611203579 611203583
    0xd1e080307030f0e06010e100b0f070c050a030809040f2901030c0219020d0c08071e0e15132304050c060c06010e150d140607031e0b0d0c03 61
    0x100c14030585039090300680c40b040d8018001041141007244902d42d4032401841000b200344500c401007510412040b155501610520840a039500740e580b6000030642c1c44a0415130701c0d505913030000b18440c038001c1d105a0480e504030f03500394101500001000003e2207689961701c0341d16a108180318002a80784600c55680c8040300d4035200ca1100d0310009015110b03151404001c54000364900710703405200030f401090741a0180c80692041c042d51400d00c05540e510b803c80307400c600c52007000040e003024420424001c00540070101c186140d45513450f10905400340c50100395225003283c090b0346d9007000e4442c0d0b41d190240807001704000c5070740711034584c540014140320100014200108020701a08001ea1f40d07a11005884c0f00b4645560406810303103607001801810340d04080400410301711500f50b2038003584540000c1410f0344000356450200a080d054210014960040c0c20005d40400d0180c45910350800303840c2056240d220100c0e40007401402d22201c0310f94024240c001c0c1c4004555601001e2010318 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 611206079 1250 611204829 611204843
    0x5030403081501120908160c1802090108040312110a03020405120f03070f050c031002031f080c01050703051204060b031002130e0403230306040b040e06060d1e 70
    0x104003030500800030400140603480c4901e00195250250b68000c104c030501e04605100050b49018600d01185035100e040010700070805108015400d03c504682030200701c0d5910b46c14081d0300c24210101c0810303401004281c60200b1704420004d400300c3e000351a00d80307010000410020740308950380c07c0d45c6029001440d117540045d5020900740a241040541c001c8028450401000c190110342c940300e03624420440014908001f5034055000c01c0b50810000c00007003401400d460607202c003070b2101340083d08100e44100e01008410700c440b040b151500004416505000043c00c02140f0380340054403d544080821001c0003800c001e6500403000d408150350040d8070546000c41c0b010441d02c10545000710a40342800701c18810032400c0c4801818040f00d1040b1142800608055500e6050640f1500749203064551200314141c81204114008001503125110807202001a114288140000c1720101444840540c1c00a80401c56518043c48405542c0e80300e10b54182111000d500b660046195118048680d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 611207329 1250 611206079 611206081
    0x1806011806180e131b122904020a0b0c120301120b090610290307021c0c0b010b030c0903070605030a06091802040504140313050a0504020f03160c0c060503 68
    0x642c0a600d4044000c20607080780290906040c40340400304406120001c0030800e03618040034012403a00d242000400030384c00d0f8000c2d107540e80c1c00e0a411101c10740c0b24941d00c020741c81d114140c4101c082800113008503000b50450540b01d00785403440d503999000c3c41440c4254400c20741560800464000118040c0c100d90241c07040801944c900036404c0c400180a01e2036940110081000ca1180450160126a81020040984c0c0044000410b500201ca82401301030500001000181d507000103443d000040d00f411003000d8112114000c982000d101540148112043d030010802c3c00440409141c1021250601500e08146000024580782c12a803000f0007080c00801001090200c0d44102c0c401011821402d10030380c000d6900e061a0311070b05043c001e2041e84e484c00402c0c10f109082c100c01d0841c44842c8210b90769011030755869280c42003980304040c81703030051300c0010403542414005c0d02c1c613408045c0e10140c2961118203901380b000524100540c200003440c1c0c4010040b03040d01e0901801400191280303980e03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 611208579 1250 611207329 611207357
    0x308070210230a0c02031c14040b16050903122505060103110303040b090402030702070506180f03030a021903110d0f022109040c2d081003021806011806 67
    0x280003000c04100c0c1303140048a450044e0040103c0d403600e5080c65003100702c80101c0c0d0b812001400c00d8a102034156400504100401505a0711103000e00d80300c1410b0501007021350b00c11070ba90702c1a8100180c054028401d0707400c5c541d2882016200e075108140710480f8925190501c03a1098140c404161074607030220b00108213000343d48800e5400d01300c055001c1c500c0c05080c003400016500c00d000c02c01d80580d0b8004000790744184240854005014001c0a85a41341c401c0307264140444040c00e10b0074452901645050320303520300041100c6020b843e079005001007441d81c10058500c1400c02c00c1c1942170100c42e44640411040905c0041410200d94458000f1031021400080c505444900380d070107046132000d0402d00d801000d809582c1d41eaa0101c0c1c0120301c1032400307141150710b604182800c410104401c402c02104960341c0025407241002a543d0303d820307540e011140e0000b003900f48006500125506451800d04210148507903024006040c90420034407514003c1c11000001d41c007010003e8600428005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 611209829 1250 611208579 611208641
    0x307080d1413080403080c0c0307081c030603020a030f170a0c0605060d0b0a0f020c070e0402090f010b0f1810021506040911190b0403080a1b0b040308070210 69
    0x18110401c00c40446100b801591040107500c2a4000600500808070300d13918415006c00103288030020140c2504c460070f0352610055034441410360a02c1c11805107052506410f80309100d200226500142101d2684d8070f50703240e801c40d48000f040c1c2a62052100c1da0203500028001d030007409100b100b551180401c10b0103003403040445901400107807044142c0417402d07002c15801104960881c05403400001c2c40035100703070b40328002c0c8101e04401c00d8038001e0220020710a0313182159584224000d0b1501c0e070041d82d03445200f6511138000d01545c40900c5082c071204005407418809484000c000301c80c1180d0070b0b4030407000500390340c0c1542002401a404021650081228035401ca504480203450034003100200340d0351080b10180c80f9002c1c9020752001c2c158040307800c188511550040c180204841e0307031a40c4a0134141059070040320301c080400d50744a140141c00c0713800c0103007116680c4c20078110802d40e1911f0ba404c945400c40a0000d8003107204231558907040c030100d0300c14001c002c20034910306042c1848140c400c170 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 611211079 1250 611209829 611209831
    0x5040e0105090105062a0d1d03010b0109090b15030a09152304021801170d0f05040b3403081806010e092a040b091b0c0307080d14 57
    0x3400b40451400422050726400c1c10f5940e051034036201300c48128007503000c0c3c1913240001e0300e00d1442e900c43c4445140303449403c01603410018094003855041720043c0003d16090350311055003680001e44010042206032500e600c4583e50580090242d1000545a98107a103650030690310181840d6850b48024100711401464000d40804524188a0340700300154010f400c06840d010b00802d0007040002804540d241d500c80646450221040d1403103585174282486042c103155a60040c81c8070342414094068025050341c03c03d00c2260ba1854a0141081901e42c5103400480800201c008500e144c1c10b80c4841a6a074402c02d00301511001740c1a183d582002451584040c0c0011040d40c0c18011400b4401e8001c917040741543c2c0a624200000e0b16811212031418004490388a0a07581200142c40c144071900300ea4101203000b21014011240c2d581300b00032441000791998170040d1055810501c141100402400600f281642034a090032101d40b00c0741c01a0344045411441f065942070040303804100d4038102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 611212329 1250 611211079 611211089
    0x818090a1559060a0b160b040302010c140403020901151e050309150f0115020a122d1d0a0801090b0106090b0a050403020d020d0615091b08040f0f0206070305040e01 72
    0x10320000e00308030010442d648130502a025030042c00203405c00840a0865400011540c4002111080d180c0f40c10300034000c11521000300300080b80147c000f101c0301c800500362000e03282c0040c0994860707441c210408181001e10300451050110340e5010781c00c0740c21407020500c14000f85441d025500d10302001030a00300200c6800d1511240804004c0c020400f60031102d1a0540d607109110340482000000e0591a0190300da0000b000240040c02105445a02c501410028580015040e20307048100c2c00e041ca5013042d095007034000a4842d00c403013605140c030500940c40d4840141411103807507102c0a0031130070740300c5807041a68107403084401088001c2d88140c02d6001000c00c0400706003412492400200036200da444041d20503034107105c004003556504c8450800e404da002401700100038240038086807071641c0e880b458000c1c1d40703011003015076401f80c20040200d02089540c1c0c410301d44c0e560381e04e43d0340d0746070540c0042d01e5007401c0d2621200140c983c80c00409020307020303031a41c640b0b444c0307052203440307071204140c001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 611213579 1250 611212329 611212499
    0x605090a080412030e120d0e010f020d030504140a0c1802092d0603090f010e0c030c1c0c0b19140702011101090818090a15 54
    0x8240100d1401c8056505a400c0e01d00c541ca900300e120b040444130440d2443c2c266a00c40704401080f0540301000540c0007000e81281c0b1680702c803198800041d00d04c0e01f04d0400140c05a0044411000345620070b5101d030340d0051181440072000310040a641c3c0c41c03ca0341c2c2c0d808840044164500340050308041c101030804200001c0103520b010030030008554001c0d41d5040d030002d00c5031009044900c01d20b03903100c001e04041d0042c1900340c07285400e501c040d98483c90811403007035552a0250718001e2640108590f21555800b50007448104401c1043c010041c4203041903600da43d4442c038000000a005050020080030f010780c550352100e4400407485c0000303241d000001d080c8202141032030244120b440035514496024200628852520780c40706015280300b240c014405c080002d100a440c3c4e0000d141501e412100303481c2d003e41584d5a803030f035500701c4140c403180440c0c0c51000841045007001c0c1100c0341078403040c00d414003000c2456203c081c003100062205c484030944448400325011461b07040d2110026025010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 611214829 1250 611213579 611213593
    0x2604090b09060127080a080d05130b070c020d06020427051e180601030507090b030c150702120601060f03110a0c060f0209030604080403050c060a0f0518030a0f060509 73
    0xc00688040c130400c500c40c0c10b5a450004140d005040055148000c2c441c400660b040104a0720300022554072610071843d00900e03290104848555103040541860350242d00d20b05251034140003552140070b0000201d901c60074100101300090003900280000f49029010310481c07030540c224224a00d0070400c0e06200e02442d0100700031281d40c0d01d9060303021035010140d80d80415250850700050040030900540303030500c030f000000800c02078002100412206001c0e000c0045411800405841c0d00c0e4950009500803580040e106401448000800020388010400c44680308182022414200d09902c16004a00105144880c082d09806a031510740c8160100c0c520740500e60902030070201907041c01403e4560742d207180040d04441070741150380c1c6000040454806260038a800d0615a0081c08121441c3c000c5c0714a080072410200c0c2600e044580a468462011030203100c1102d0030f40100e0010b26034140480c280c071000d0384051150f005820b000d08540e100c0d05409017010010f0b11809002540b460380061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 611216079 1250 611214829 611214841
    0xa02090a0213090f050c160609030e1008070f0f09142b0203060709060804110627120111030c0c1009150c02300904020f180301050615072604090b09 65
    0x500f94140140c1c4030200086e150117a080440b07009140d861100e80cc0313240040704408050700540c0707a920849850303950300c84a1200034011200c02200c02c5800300400e1110704103101c0b00c880c07120000d2070064041c1581c0351591405803101d9180340140c00c03030000082c20300c0c1e04500b5802d041c881c00c0e9100b4024140b6a0400e1b180141c0101110f1004001a08440d04a01c40003880c0d40d811040b01e900148000650034440070014810283c41230281c503507441400603000c41040000103001ea680e4101c0c3c0c10040318195036803040303001025071000121000c1d902a03070082c0d2038255164442c1c0d207245c1e80644d018141c0f251f449840c42003214204101c0c50203561258114010320801407403482e800000074800407819014002070b0503158041c51441c254854000300e1ba0640d0041e00001078480316019840405d190348812090500301d038410f0703030000d820050710011840b1300c9003070800074000c01d80314909001d404416014001400f1f12503071513440340f050340003c00f00030182c00c60040d8420202c0c1200c00c511b45040407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 611217329 1250 611216079 611216107
    0x11030f0106081e010f05010e0a0f05100203041d06040b041a22050c1207030e030301030314070c0303031a040b030d0f1b030903230a02090a0213090f050c 67
    0x1441400200000c0300c0001d01211840f070000c55120f506100040c50310b58444c40400c0041c5401c0c02154006001180b060480303150441015044500f560305416800341000c05200500001da008902075100405c00014000710403114040c052101848000d014105901044242c0784201c000b1403286080950301141e00141178010040d480d4111884990900100002690301011541d00301403149803000b04902d2504000081c144801c040351000b140d650351700410b400300c6215400d911a20b500600052002030b00840f6603110504191040d0381c146030f0349941c0c0c15400c0c1c285d9081240080d07110a403031000001201300e1f20b4031144088a0511035003003940046640c60317541030030500401c01480780c403a080d04d004030140b01c3c8101c40c94090410700010303810043c08840380c0d0f10080714070b849a90401540700c500c52048009a20700074010b00491070b815005c00c510f040018010604481d401c0154100c0165000c0f602c40013001c3c421000300d000141400d2400880302e000709418821001007220004c0440301d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 611218579 1250 611217329 611217331
    0x609060e0112180605180f03030403020604020d0309091a041d030904020906090d03170a050f07080c0f040603060f0b091804060f0c030b030f190b1909120311030f 71
    0xb200030000d0480112010005002840400500b5480ca00024410264881c8440f166044080822104203050050035170796a48001c03980640180c00c040f010800600e40000e40d208101d00038078111000d9901c40480c074080320700052402580c034003030000e5800c0d03504150084400d010021a014a41d105c00317504c4154483c49200a83d2344107950000e030701c402e5075035064151004014098509a041783d981d10b406422000c45460300000d0400c11400594034440328080c0341c1c41220701c1d5030108100d807600c21051b0740c2407001501c90300e81c10b1300034405c042d210505034000d07000502d1542e0340882c40902d01501c0c1010031196402000040008021a80e40c5890f0f002450b156655494821401983d03242403c00c010800100d0320601e6a0500e003003103640681c075402042d1616011410b85490003511501140d44175141c02d54840d030485e5040500c3c001c00e501c942d0300383d4402003004103900c144a41240b4179044a03000b180841da018110764111100079450300c00c034004060040c3c071300707403079420040c1c1c03143d0325080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 611219829 1250 611218579 611218607
    0x10c0906030f0e0a08030406050109050403050405120f0105090c01110d0c020d060f06090e0f0601060212161707030f020c03030d020a0c0c030b0a110f1e130b040609060e01 75
    0x2803610829810070078103a1003c502125202d042d01c08003a102c4c80c006032a6481680c1c01c0c4c0301c4030f0900001058401e12441480e001d290305807141442c003032a20003403003030480e0048280400f41c050103500241c80030003801194031651359400075201880842c400505810989403542e07116a10440a8803005034001e0703600003020781c04592080710705e0554036080000e0988421405c3d07080e8144803000070b82d060b6940200c907101c1092001c1e54541c1010581d45640c070300007446101d0041c2e0103c5647d02a442a9800500030700d0391a01440c92440380d075883da0a049207e040b01e000300900d0000e4240c081c03640c800d165040418061014141441d60000080d0362405104c01040f0aa40d000640300e0103940500c6819038403941c00390f4040c000f9a56401e04031130000003110480c6c042c604269032100400c407514116010b060b0f02d071303403040c0c03c0500905048a02c0500c12200740340c00b4004011a54200f25240070100c01020701c0302280c0d41d5030b07041070300c01404400a03900101c14024501051185680c03c0100000c06403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 611221079 1250 611219829 611219831
    0x30209030a320a170d0c020109030e09060f0114090402040e041b030c06050f1903140709120803060d0203100e0c0603010e15030709020403140c010c020607060e01110a020c0111010c090603 82
    0x2441c075071004075284a1124801105d9190089420034207406400000000d400780d01c4030070007845000d050205200b0202e031515070180810890072000d40c0141d921000002101100d182004189404034040364800e8000000b800d2408040204000d0100c008003400f42480b00301e000c000713107141ea402811501c2c6000d0721b0144000801c100c0080c40b260415199005280d100303091a408410f90082e00400403c1840f007110401000028103050207180c0d04011240081814a00303082d260325400450f400c041c00d15980840c151406c500580d41c20018100d40318500440080c51001c40c80c02107103800805188140100000d0004200c0d040c03060450b0b551129910300581507040c0039000207414600300b0380068500f04c0c8040b4000c030a1041030300038180e100600204403107240c1003450040d5090000f603400254022810412840020b00310303040f00c51102d0b59100040f0700050342100281300c07900140175260050380100b80e5030800e5a8048110600c10441d81d008001104035010300070300d148070600841083c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 611222329 1250 611221079 611221103
    0x9020616050a0b04150f0c0e01120605180a05070306060e040e0f0d2f19110a090902041410060e03030f03071e020c0a050907030209030a320a 62
    0x80902402888180340c2d00c40000300d1186041d02d04070242c00040f103130a80b140b46c0f0b00030625203d68102e10802000c0d00d595114011103a5841c0e004403034400a09500b203c00b95202c1c0e90000d002c1d103070090203510304404805001c01c41d240011440049410007040c100425042640800c00240c01003402d0307448090586010032100c0c0d10384520740ca4226405a03120702032182480d904056940300008030561840c002088050700104114010610010404e0400c543c200f6841007802a04050710310b09142e2145007050400c990040001c0d03945082580f050f03050300c0c0c480310144114585407181d140e01404e0146100c081d402c008903841003103961405803030705001c04c1181601050707800700b0a403404a07203a01100c0e035880c0b502c048000c0014104c1c0314003110011112044c1d00f01035002180308600a100a82849001e62600003003000c6050f02034400030034103508020480041c2c409105500c551800740d80390b1680002000700940002400e05224840302c000d000c0707511a5078401080003401e1540141d8200b40d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 611223579 1250 611222329 611222333
    0x1903020d03121d061501020c030705061c0c050405090609280f0f06061403130b06270f1b040902090118060f021002030906060d081e041809020616 64
    0x103000840f041c0e011007030301101e54040b4440015019103c0d803803a00d54001125010001641d9401c56400016071542010805003e20b080031000b030a815080e40c490205500380200c0a0382c110740c2c07160b40b49000604001000c1c0310604015000ba80c0080f009d8908521525000800070b1141440d170780078410f25800d04440c9041350b0050340044040d034411900030048861050b500000910321481a480072031041105680d04160800c10f8070301c20015080d100d80c1d84510790703440c150358140082c42d15501c001c408580380580c004a9000e0420712230b0031001f0304178604090a03840100c0e070008094900502025041c625030700d64810070f65080310000ca4002da01e0b200a00c006a49084980c1000c19a000100100080d4103a0000f800d41071b141d600e409944065240003012401ea200c00c07546d100c03455100001299407070402d0000800c10758003a000003400d2101da2001840a50064840300c11044c20110b024404a072a54500d0398641010603010850b000c8298003142e21405040c1c1c10a10400b843c26450003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 611224829 1250 611223579 611223581
    0x30f030609020d06090606021c0c1a040302151609050f040b040524040209011b0c030206040801021b0a2a150f0e040c02071206060e070e1903020d0312 66
    0x9000e16401c2035460b4441005204000e00d014810b5400783c07428504006115400803483c1050304002882d0303104401154403080e0b801401c48101103500350751000100c10f03441180d03040c481c0907604c654058032140b103010544036071040d000350011603c0d00540b944c01030b0f07060300414244c045800070fa40100d2240c404200150083c0361101b000c681081c1004104510314100203904100003280c03c895901c5150840d0611080303008409001d0f0101c0d942c0f0f0348030444240c10100818950b0311410f618016070351642d01051b0300790060b42c840c44540e034012030b25212540c00c0246503903540542c03000400c0e000d4055101d070320b000c200b01406007000c3c000f1010742c6081000110061006410800300081031440b00400c0241900307008810040062030410084404e1301d0039003e11000c4144540c0100000342c00c207000095051241201242c4480e07440e03400081e081e4500038028400c131080d0325a51909200c690501100c08000c0b91a0341d46041070110500050b0707500c0d41c02e80034582c1c06203040711401a503012204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 611226079 1250 611224829 611224841
    0x9061504050405070e0306072118020d050616020303040206030a110c191502160210050c150f06030601031a0a091506050a0518042a170105160c030f03 66
    0x1504281003504101c07203150001c002c11083c075070643c02c4400c10784d0f49007000c440040b40440c0d07020716a8000440d01e507040c000392b004551003072001c1103a00c1c02190701d80d0002d400b0030040002103031150015800c1245c0548629101c1d9045580f5002a40c07852409600040c010310004010782c001c01d40d00c42d00307031030209050400c0d242d95280007001c6078940c100003840302180400f940c408903180c2d1441c501d00d11180c107081c001d488c500d851201048200c0107070340d800c1040304e09011424004120090068045000c010083c0721040400140300c1195402e161480034212140248210700981c0000c2c01007001408074a124028541c07400144103054440c0c6100d88003070031000c50003410f1000410303110b01c025181580030208a44044401901081e07554051046a441c08115104003102000c0050f01068200c0120525200e40a0070840001984182031100c24000c1d00091480700382035403c0031421000b40714154024120f807d0304406495041e50040022003011002400c20a5804e024610a8002d4200c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 611227329 1250 611226079 611226089
    0x8030313051c080906071b11060f04030f20031b0307030210210b060a030b060408070617090105060f19091e3e070605010b030403031a09061504 63
    0x180424207282c8000744410003d40e0040b600d4090003010443e080c0c0103035056001201000c0c1c0c3d1303528282043e11a01e0044e079080c4105a00007400708007900f0f001d5050b0005002462040050380100d00e0641000300301490112001c0040d44105462900da6503000948950050a59000419111003804c04039007070648550009411420001078090501e41001090800c1c0079208418680300c880071180100785ca80c0182c1e03850300500c0800c100c00085200741c102000e9004050080d614256540550074035010465008500150f13a049100882001d0720000c0c82e04044074400a0040d81000740016075500a03000a45214401c03401c4490b280000101c0804004d00c1d0700c1a080240c1840600302903038070103050010301100c900d000000440c684160075402c0b00c14110f6850700d00404035504006041842207150f607026890140302c0303140080e1a900419000e013828000c003d4480c2440d00d0b000e4195915145a130b080c1400100b068510b17912105c0400740c3c415021990841c4040020300c601d62580b00e15000303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 611228579 1250 611227329 611227363
    0x1c051f35190f141f020d02070f0b091e10091b150f081501080612030a05070201090801140a022d0a080c040b0a03020708160b060f04060803031305 64
    0x6041c0c01c2c400304201d5a8403650044920841401d0a200625212880900c02c401c50351440c06115101e20620b41c081d207a08110340300c005141c245151039941041e00045802c480000000c020005250824026203980c00d41301100c08001b0790740c1d51034050b00c0310b17010075031148200daa501003102408507032499191038040310108000c220f5120780c41c040200a00300c40a40200703102d00500681302d4403400079184502d0210b280444201d2000f001141c2400b005410194800303044200c0e2844040c0a1004000552603a15006d0f6103019510003d080c5411550080c02c00380d26000101500e442a0f004040c0d105203803803401a81d5134180f0300395203075003040c1d08041090804034034480441542d200c0010100340307a80391203100b01d582d5101890b1116100741e0080c00740312030090180d016001c0c001d4028060b124490a212402d0040342c002c81c252080f0918810350308044500c0c140a86804c111030040e11491080d14140007050030074070059540c0c40064030306005504c9812914007444414083c205030981603141c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 611229829 1250 611228579 611228623
    0xf0b10090e160b1305040504050304080304060e0405060604080d0e01030f061d060406030f080a02010219020102070c140f090a020714061503010b10051c051f35 70
    0x8495507039031031090690801502c4100100e00c80c02c20030141d40d11210080600020b9a0601041c0800b809000c1d000304c03060701c02031101266500c0180083c101070415569070700801040407081105640300a01070502460081005100c0c810011a280d248501281825803100030100c0041380104005000072407224130380280891500d40c040ba80f19010410a6050046500c680d410403040700c0b282d1000410305080c2d1801140000c02d88000f80080031070341d000040c1002e565184071618030440e6004240140d500007424010090700e2150701d0040d2050403920005014807602090099901403841842001c10300c000884094190f0121109658880511400c2e0394001340056074520003600c6040c5514603441500c280b5040c144201d8004141c010f100300342c42031b0b51000560b4554000e0810300c0c500005909503024503a600e0040078003c10702c00c0000c0b85111384034460310100c41601d80003020b015140d100b40d0458142480c04d90400000c202c87e00d0840c115040904078a40042c000c048908650000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 611231079 1250 611229829 611229851
    0x130b07230702030c2713080d060e1008060127020f040e1605030105060901030e0a32060c0a05070b010b030109062c130b012306070f0b1009 61
    0x5005007086a100b902210414981d40c801c2012501c4954500b07007005c1c1e00c000d11050606040140325801c81014100b180c0d44443c107403944d06032507104100c1540c4503174071841b080042821b4005400c1c1e12000c40d00c010b031642c1e0b0a1200d1142c460006110b2502561503801c645080341c00035140c2074880700500403045548028941c154503407034109110302c2452080160029010383d072450303022003401c03001d991041d140d07030300b01400c11035560041c14209040550303c201e082c0554a04004010f401c5004a014001c0f01c15104141d01d40c42020072034840801d610075600c050454000a5883c2d042510000b169894035180b0720304661500841d60080c0a846050000042804602d0700440c144e03842c0a605207d46502c50901090b000010240c02032038101d1b0144ca230003100c448006803500141165009601c607056070315144031104003a01b0002c04140c40d50074101602c240c0c842d00f20011002660001d0400d41c3e540c0b04c050110b4100000500b61241880000381ba9005000400340945a90b05c4100560820710b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 611232329 1250 611231079 611231147
    0x509070503010b01020304080616050f0307033608161506090f0b060913060909060b1008090703030c1509050a030201050c03012102031c17010608130b07 67
    0xd2103900d0182d481e100500c040d6500c040f00711016203500b14010300035a21500080f100c070100d0303da90001044820f00812185091540045000b081507560125103480079820404c1c5a4002c0d907041641080c1d14540e200d0501c1148071586110ba0f0011000c81d1101c0440548181c1d8040048000302082540b1904030103c03c003542c001c100399108228104654081c0f0030428044400d4521090f9000c1000d2010710f00c50302c3e00340b0f14005680c4c88141c022402e00d0b51240100c0a440c0003540449415448086082d624100010001d0020400b45480c690600f007590b007241c0c8402d01d0b40405020000c0080f80c0740c045c040c42d005804203858070305a0801c1a04400d050032510703a171072500124019402c20022800304090f21050768182d46191070030440a80882860700488004d2101c2203805010340b40216506001e0100c43d080e85009a0301c8000b08100040429804080141c2114043c031103c6005d010542c000620311090440e4007036078040481d01d58840645001c0c3c10100c4007000c10481010b040c81d1070340c1c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 611233579 1250 611232329 611232343
    0xf180e0a0e010603031107230f1201060609030204200a121b0c030807080105130c09030c0b0403020901170d030221071215030f0b06131107020f030f0a030f0e040509 72
    0x241031b2108941c803207680e030120140b004042c0d061042c408d6991111480c20420407449c8210081c0b0070280c0030b05158005003502d100741e1211022841c0800208203600306400362016071002d21038850140c0510b04410309060152050070030801920245100900c0c0c0c03107034012014420308402c070060060300110300401c480400c0d8002c400003030046000c190190b0050107050706031035005080c0c0782c0701c41c0701c0c05c410b00041200c0c0c00d500d4104100001d000000c560940c03d031402401003501195a15411030040c0844e02c2e006a1104141403450180348004280100795400d6140d603030715015039581000c10190740280440c01114107000011400c1c4400c1d20740040c44c40c982031401120511500c0c0d1003607100000b8550741d00c400740000048412038400920440c4131a03038030140081100e11140c0c424490f10044a0b0400c40c03412003060000b400e40154a050801c112240101300d00503d901003c0c52802c5803190070403817004040c40492900080b10a02a80300e2494001014200b00000d140440c0c040b903a40038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 611234829 1250 611233579 611233607
    0x6030504080d1a011710031403041d0402030d0203072a2c0901060810150803031005030c0411090f03030417010b04060e0403050f090a03150c0f180e0a0e01060303 71
    0x201014800b030b100d01c1541103030307105510400c2c6c444411455034407280d504201e101d503180b01038001000003041c0014200d800140e4406d000c50182c2c2c45141ca441031503d400850020b0034150341c414480390000441c05039140c5800c411100e81030386100c42201604000309200d4200164042c4000111000f00400500d006106004001e1030005030300c071030701058201c43d664001c3c28003a41185010000620301500240c02c09001d4142100b009030340c80e07020342c0c25504182c070480c07501c0c0f80001c000c0105180400ca12408440d04803420040819003c3d491502803051a152a014000700200c60106560030b0090301c1c01010100d089104441240d41e842d4003c0c442120018491841c02d1004600440000c034120310035941174942a18043ca820585900c03500f12540082d480390310008003000156101d43c2c00303010f0404000003c9082c0c9003940f8060809289401c0720410803682d0311400c03101c20342620300d4808550755805040ca098076000c21381000303400421464410303582003071350001c01c0641c8502c15041c010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 611236079 1250 611234829 611234837
    0x40312081e0603070933090606050406091502150a0603050714010206130501091a01090c0c1e080f04080c091509160c020a090f0e030f0406030504080d1a01 68
    0x1403848144206040c4042d120540c00d5070140500748404082580003c40345410101500842000080f003041003240d42111645030024881d4200a0f051041c00703410083c00c2c403030030000d08007810306200401c07508562280c041c0c2c0c021074107c00402c040c024041d400c3e40105013960441d07145820400840a401c080c807007180d881c800c950340018a0138001528030410f04051b4060419501e4079400111a5074000d80190303401d5603620600c40c005400b21010a00270281100708554030361404040c102210f0203d4260004d100f20005400005418032070002c50b14494034594083c119000c1c14a0340c4580507440c12545041c40018010840c182c0c000360284084008a80c0400d40d41c4e10744003000e810002c100e010617040181c000102c1d24400082c64490903c800030728110a2009a54000400404803680440c200580e5903000c01000c01d2036008900d070004100000350700d001105450980584154816107042507554008242000a81405c40f001300058240030701032560003003200c0c8001440102d2032800701e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 611237329 1250 611236079 611236111
    0x913050f0c1503090606060304050f03040305061801090f020907051213050c0d031202030417071209290307211a0a03050a02040c0315120506091c1404031208 69
    0xb0b00400d0b022680700fa41d1384006040c80e5200c04013484034070b0704040c00451315401050725500c00300404001500003180140000c25141c14028421007038501040788882a0340d040203441004a54008003080407190b044d1580440d0342d940da2012a514020328180e8403506014205010000d45100740b80e109090007001601d103c141000b04004110862101c010040b600500f0340300c841880c294065540316024003441600a034102c0c00c00b01d004d40c4a0320080302d03008800702e4414600d42e44407500c40013400021010b28940411040904808d00c41d00081d451172030ba000000a0020307100700404442e5030440d075600001002c914811b00050700406144803102c088000d84c1c8c0256141c481a41003c80c1d42110103408001125024031001c0c040b10b0031010203058458804100e01612400d43c90010141241ca26005020768603103a41003400c041d04940d05030b84443c403c51000488518264418455030518004483d000859070306180500d90010700a0b030489465441d42e0794110007200d100c3c94211401e90b040d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 611238579 1250 611237329 611237359
    0x30c0a031206091415010306050d0f0c090e1504050c0d05030a0f0309020114030603070512010e071401080711100c030203010608130503030a02130801020a030209090a09110913050f0c 80
    0x3240c03c58200380c05149844c802150002143e280043d4130148107140100b00d00c1d48034000b2581040101e1012940100c8450081c001d215aa00b00c02c409054401800d000840c40c0e11811580e42a00401c0841040c01590110f0200301e01085035403902e60018007120b00303039003941c20550b07201e401140180c00441c1283d000d100d8040d00c01c1c0320b480081c950503150403e5104400c0f01400480d000200100d406101d402d0011400ea50b56000312102c44004030f001003892201c0740d4002d07082512650244034220200c0b040c400702e6a8206010a13880a940e1500440c5000c048804600c2e104041c03484d00055441c009944604a5042e002036041c0c40080d216a803084e2201c0b014282088001c000190030b642083c0b0100c3c006c030301180c000304110b401500030090b190380c45410141c01c81c0d001110040200c1d41c0040d500000c1e080552656601c4031803210100708a10035a116080d070880448442442032040c4000200c404803080440355003182c020081754400d168060205a99000b030307100040c4100031612000314 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 611239829 1250 611238579 611238581
    0x70201022701023c100c0c0b06060703020a171209030306010804060b03010b03100c090b16020126070c0203070519230d0309060e30030c0a03120609 65
    0x1803541c0c1c180c0c0140100801c5203449400101914000321318072a030510786a082d20281c41840c00550540070242c24412102e025800407141104145000d0160318017030100420f01c20304101d03500200503600030303640d95550b18040b0308040c0c40180040c107464001d0071041c091040000504601034200000c0ba025440b0100803542d02d0004a031940c0c0000e20003400640025002d400203050302c6000b40010a6000e00303000002c2c28000e100c131145620681d50704603104010b8ec800090360040000c211158a000d4611100d5a20000c407220003a050044c0044c8400800e007403200001c2c0d0345401241008014200b03000000e0051605c118243d01c41d100b0308401140078500461990b00c141d040c5a0b0030800140b0b0100b90b1090031082c080c3c1200343c0118100e801040740c64160b11038401d43d00c00d545144a190038102c016051060074a94540185480e54041000b2501d00359107402d281c41c5008090700f50200c0304647c0d0b00c0c510415021000034001d43d0020403c05030414a49200c3c080e1400301400b80c1611108410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 611241079 1250 611239829 611239897
    0xa0803010e060a27090302121c06060801030201020d08041113020904050c0f2a06010602061014130f060305070f09140402213c0703030909022107020102 67
    0x4d07142e10401c00c91811000d00e603032000550600c2401542c2102e0598003a0508a4100c0c0400181c2001c900e4200154581c036441a40c01501c0541480c1e00d5075410360700000c0d07444005101079024000080b01280c00d21543c8908030b100c880000b01021090314400360840081e401c101100350003107007080049031048151070152009250403420843c2080300314109030742c1c421140ca031051445030f20f550150a04a9043c00114041c06264005000707505004100c845084c82c2075000040103001140d10f040e1f113a8682c00c02d4464110305c03034004900c0182921640009064035800240140b01c1c1000005407a01c00200d032500302c1d210301c801001226042003042010034402c5800941c001c01c0d03404100c0f445407406980341e88080344d60040b215080e000142c0e4001c152440c2400c000036401500f050500309140c1240c6017a005d03010f40242c060541381d5030380501410700c10300958580c6900452a00c00d800041c2202000003401c4885c0030031641016400607000b9886420111078421512183c81510030604020b5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 611242329 1250 611241079 611241119
    0x40305161a0a031811090108031c0506040f0c1805040204030f14102d09030206060f060708040f092703081806041a0717040f050a0803010e060a 63
    0x3008100781450300300031080c1d00c00d4407220181556030548084c0704400d0085844e1452181004d10283d5441804004d030707032407050b03109090710350040002c4404080c002081e503494001d01e580c0400d698aa403c0090003900b02c030282c401d40321b40790085030108142d001c00c00b0f401070307100711158500f41911801408264400d40c0006407040781c4a0703c910f40002e42c042e14400d01d40040741c043d1818908054460402c0d00c01c10002041c08010348580c072064244120340d41084084114020080c12400b6034003e510760300d00400891003031104800c03044041d150746088451103a0700c02d01042d503960701e400c50740b000800140510b54146141c642c8400807500c000d0a4684c0d208960507000140c4031240d50102c40c4800000c1c007440d020b103400105500f000b031041101d540101d00c44c00e04c5405901d4003c9880140810040880040004660301e181f445901a03088a421035006007078401d00c0c60150a000381341142c1020002e1501d035000000040c46c58115000d203020f28030458801c1010740c0e4881c007840c0016410289 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 611243579 1250 611242329 611242349
    0xc0818030a0b10060c0305071407030b1003210806040c09050d0803150102010216060906060f060c140c0a0608041703130302010b1813020427141b061b0109060204030516 74
    0x3440300414210f12184a030310072600d042b202001d880740e070782140c0708106448956514800d00e0b410300400211440700c1f483d001c03141c4990844d00c00d0714840200705000c00b41105024643d241c002c080300b2446401c000001c0d14014041c0d280c0d0310399038038081c07031240d000322644d21000074006042c101661040c001c554150380440d90b00c41303d64409031560001413050f010101d4000750384080004410b000e02400c00c008069540340c0b190001c08a080c0544603c032006040800c64000303580c42441d80c0d441c4500c0e81d0a8480307a10705400b403640c03145001c07a02203401c0c2820b007140020105c10042c00b41c3c0c160250400d114031990090100b411040103020504082076000141c41042400082c148a0301c80c0c0c802c80898001480031540e10b4860100d554241589901d00c1c841189218070306003804642041824840d0302d240003000510111420081c1c24280120134070311a490004920411000d150044c52650868000801c584600c502c3c00a000394400c0c03100711079500620318004121070b080c00004d412602d43d240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 611244829 1250 611243579 611243587
    0xf050a03050a2a03060207020f040603120509220e070b030709150314090c120c0901090209131b0f3002040f03080c1203070c0818030a0b10060c0305 65
    0x2691412040140400e42c5901d0f4491035403050140d400ca00f03910080d80540c50060382ca071030a006101040800c1d4402034011410000200b000a241040034000000c8614150b40c50f5001040050220190b00e005642151051101c002d10b0038600e6101c00da43d548008115401d543d500c10a4030120f01046480c81d0106843c02c000304480c1d500340c0140118445c949c9400100e080c6103045039200c200080c0d601d0542ca500019440c5594240a090030b003000ca031440007011200d44030400505004014040c1c1ca0102c1d402007081000740d00c8884a1140700840400103200c0405600d000d01c000b85a580d007490000703038805010942640c040c2d40c1864040c204000710354070706400085100c0c4029510800000701e15800c01001665080e0f01034040042c5202e8102c07079544509040e42d0500d0000040d024104c2240e08005100200b80c019018070026030340609100c1e2140610219880b00b910180640c0b90103000315480007081129150560788076002c80602c654826488110449042001c400000c001c41d0f0104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 611246079 1250 611244829 611244833
    0x3120405010818100b040b03070f0b18090903031905010302101107210203070501030509030a030b19060305070f1b020d0615030c0602012003010b090312030c040f050a03050a 76
    0x1400107502502c028100c00311112024140f91804480000018a050fa2010140744a00c2c181c090b0340c0d403d0904800620300309052503102c2403420047e1090350490701c0009003100c4031601144207108203c4c0000c0076502c2d5490b0030740510742c0343da0040310341080e5901129089028a5094400d550580380c01420a490b81040c2c58400d40d0b03801c1b02d51400d41c42030b10403018005900402405031090030301c01400035107600c0400740b06040c600302060b0007540c18142400c2c01c000c00c1030000000d03078100b41140d02e00416000d4408000c61050302d407030f81d00300806440c010750128415405800c414024083c9980d03041d6014520401219258100050b00100c1841110014058034268804811181c0505000648580c042c0461031180546604c200c44141d07078008108209902031003403421900c412030313241c07002e0768018a80d00c0b4103100500600800d8680800c0e070035180c2d00c00300014581c841e0800145903507403c007207024001c4c54010384503003291a84681c070045482c1c1400b80a11048aa000004240807d095 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 611247329 1250 611246079 611246087
    0x513120f0602031902210c0a14070609060c2d0504090b01090503060412020708030c100915060b180f0904030c140703030f08070e0a03080c03090904080a020c0312040501 74
    0x580490031071584c40d8914110310710184002d103e0386008116540c3ca16442001c0c0c407441c0c040007804100036080510404601d190010047c41c0440c00750000603540c0e40a6103084001898010030261031145002d01188010360024410222502c0c0d00007490359107010343d06901c075000c09030803120f070028600707000805c19014950000c00c1c0c200c0f41410320031302e12510b81000c02d1600300202c0d000c0d01c02c604528035800095406105a0002e410008051441c105040103029941c00e00b4181014149982e6000340051010301c050400b44201484800e028650b0789014540058100b00d00070807002200034806001450052011070401d4070141c4244519030341c50700c080e2400620b1540c00d030751581e01c6241d00d060303801003805060003a5200f500d500307200400034080200305010080081c42480127540030390120340c0ea180b03105400c41380e110f050f40399103180e0600b40608500452001503042001c50007070104000010002e0b0541806e16822102c2d039001e180c04150307881c803011aa620344040d041000340010351007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 611248579 1250 611247329 611247331
    0x130308030c041d0f0f01060212030705040b030f0105032a150705030a0807021c08060d0c050a080f010c03051b070f080c010902040b0a18051f03030513120f060203 71
    0xc41d81510341400d984840440c00d0306032000d440c06014151a0030000340b80101c161554124903003c144010540c14880c01039510f00c0c9150411042c41d40100000700414071031401c4601528801603040d80780c4c02c08500b6907440c1c032000e00034940329004410100407180811105030091038000851507a034440e201c01440035240780c804800048540c1080010045542003004018100c555980c8026518051400a0622000c2e9640c880c000107003400720024039500034102034100d00c0c200c6010804a502d841c10128031045948134940045e40f082d40042c081d0300204941d21041d1041001384040c6849035000c40850f18100c46019050b516a011028061001c8000e420094851f600a0801d18015114842250404965208980c1d15030b942041141014054458404000e48038001070506000382c640780140b4121000703c2555489000030510709a901d05107030082e043c0005244a540c5038180100700d5070120100c0d00d000504403000060689502c0c808882981e0080d2806640c0400e96860700c01940c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 611249829 1250 611248579 611248591
    0x1201020a050a1809090803040c080703150b041b0207030203010e0f07030f030320040302041416030c0905130203040c1a1b030d0e0106060e010318062403080909010b13030803 76
    0xc0480c0c0131494521030f10921181d0390190720381c01d880f890285000d04016031541c00c00007503900114020800520b860081a550f040d210901241c007030003540108004000134040d01079601c006004107108640c01060020a40380203400034050500400c18890fa80c18442d40101c1c466888007008202281c21500c103012490301c2460081500141c41d807040d0752044c00e0042030b031030b0507800250070001c52034544140e4200d502c490081c0c529034070317040340c5000700511001c031024141174440802c0982c45108200000140c80700400810401040701141c4000350011602150381e40700483c07000c1002034081030100200c040310f1842a180104034403030126403a504071460702d1284024486c410044005004006a40e0100000021550700c2c000004100700d4842c1400c078103051034103081001a12901c081c0080003508402c0102d01159400d0741d42c000010700700504d41c92400d00500100810807207200030013209200302c48203142c0307989589041d810b52150401c2d240d05c0f4104000d003000090a014045c0d941702e2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 611251079 1250 611249829 611249867
    0x212091c03090e0709240206180f120d05010806040b04030302180916121a150c060a0b012607080601050c0f03070204152106021b010b1201020a050a 65
    0x141d0307564825010078200713890810200700809070500c419205111180c1e10114041100300c00205842c0e80a5180c000c068410748001c000c40c40e10b0410b19030100044040880103600300e03410003181a0320302409410404c0e10380f501a080c84000a1540d40018807580207e0300b02d050102030340c80e20340d0305800960000340f91150080f1450842401130b9907016141e40f10784400c0103680ca1140c0988002420024089843e0103801d140020110785021003800c0311441c80d0041d165a00801c4861058801602590042400034840d0100f04040300c1a280c0200c94010400e0b25121800c00d4a004602c0e09952824a540041d1207400c0019040c24801c1030000c0d04a041030600038900342c5504003580c20207112066400e8186d000091500450420340b0901041e44038103000c800c121418101403040c1c148200c1050078207003440e1503402c418041d542e412122500303e99200070303242c000755039240342c0a8585102060302c200305100403224515418007c688154000340d440c42e24001d0b801105842806e22401180070701e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 611252329 1250 611251079 611251097
    0x1804090b1e071b0201030213080a1a010608070c020d06090b0c130b0f271e040507031401120c0b03010305030309100c020709090312090809010212091c03 67
    0x1190941008601448103815060049122640302681d40d840191055042007025a0781c0503200700e40c200c081c60b409509190140e40c1f405046180c02c04180c0c40d812440c7c00c3e00983c1c1d1010204590219015100303034000803030702400da81c2d401080d5510f402c22618000828040b00002006107400c0c2c1800c0c1c66544200c000280f011801e4070395900440080302c500500c114005410700f29041c21100100007400d0b80600c1502d03081c1000c981030720501560f80d001d070b0301070080340484c8800820220701e03805882d000340400200400820709180c5440c4a04003079401240f410700440c1e01c4600c01c3c0940014000c040c00001c0040e40303088454105000030079001d0303a0b107201d40c10010074110030060085000f940580011901ca00b844115a4205600c41e400c207944145006180c81ca01038003c15500111082c1c150006080e41c440d0406840000304c1141300303225a440d011035101081a000003801d400a02a0300319850401010030602035807045000195000340c000b01e00310050523a28240303c500d0380c4031740703002918 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 611253579 1250 611252329 611252333
    0x200d03022a0d0306080f030909220609120c2102070e0f071803050a0602091201140702061003080f1e0d0c0e1f1d100503041a010803180409 61
    0x381a500400d000c41e40d400c80201108440c0c0c0c1030003400041c2040d8409003585610050f0455603901c21110190300407142040003403080d84080628244e99405c144141540401078a4480000c2800300000c95404100000c0207140d0b80c81014441106540892241e400b450103030240748607c00c1c046201c1086114062010400034855001c0b0341c000c8107010450901400c00703510250040000900705483c0041c0340c181000811000a118140d00350130084c0182d4801a00000c10455500700290002d00e42c00c1c0402030b1074080c50f21503568441e000d240c3c00e40d01c040e1a421303070000b5510001d01c8041d00b030000901c10140b542c00d0b82c6009000c01240d01c0d03400025900300e03200c684100e070442e054035201142c0d00d0300c50701c09080c1c0000505440c490300300c889031846910b001c3c0084c1100801c4a501c410001c1c110407a1080324448100500c8441d402000c40c00340c40b00341c0d14001c20541c411031b01225068014585185100c2c0c40341a070905941642010314240100094810b60566501c8440d0b68001d8445d010480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 611254829 1250 611253579 611253637
    0x6110408070306230603030f0706060b0705030703030e0d050d15091b0305130b1f0803130f170309010c080405303d050a020901200d0302 60
    0x11807003000301244d81d6003400644a490f880c0107200401c42e9058070304100b13559401104984401c0c0080445d40d8541e001070401d01c000b8a440d4002d2140d29000282c00000c1c808008090304949200380d90034070001d00c88010440d00d505000102d03c2c040303007092201c06501122900728203014121180307044403407a0b80d0102041a80c25460f03000505801080b40749800a03132500030f803a4041000ea006404001c85641c03840302e00f1000420140e194042e2110511003144079480c104003c10040c000c69444008101c002e41d007d951521410b40c0c5442410b100140d664910003641da0342441e00005981012003110055841507401d0400b1985144100f00120325903660900c080700c131026070b4980c01c08045d0b80b05621051604400e002a1003a0302640540c920782100d080002944814040c1d03c0214050300c0540300c0700e62501c4150800b219007800200f00c4c6440065000c4d0072415000d90385d19500a03425000c0c07008080c0c002350b40d00700c550084410140c1c160701079001400c5410481100c2006022203001e054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 611256079 1250 611254829 611254843
    0x70309051905160b070512030103031209080702040e03031005030c0618030f0f06010f05010c170a03020705030304052103070806060f04080f010501050a08010605010e0f010c0f080a030f02090d06110408 88
    0x1a10a00045070179014010200b10008131507401c0d10189103194150b4401a02a007034a03c000c6800b2500e5a20384020044000151601c46902810038401e02c05615205a100d0b0821a6041125403060a0005940c9800105111110b90152000d49030011180c454000504000344241e014030541400c842440d00c100a280741c01d4207008054a12541800d001c401c00f81c185900190400c00d4a81c0c101000ca43c801a6480c00d591000c610283d417050001e4064020340070b100400b41043c00003004000070302c440030552824405045582800c1e103810003165416500050305c0705800942c5103070001e042400c22800410080b0034104a407802c090751030000c90b05d8001a01c0341f125890751240d00400450800c0042c18000e01090802131040e075081500007080494050b00d0240f00301c410708908401c41e40a543e80c1c0c0062078022054203071034034003801c10859940c812823044002900c3d080740d5009954461083c0c40c200c1400030701000c08405ca6032030300700c040d10810008441111003000001054a0108414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 611257329 1250 611256079 611256089
    0x1e0d0b1006030501060801081c03180605180f06150d060203160906030c0c08030606040f080d020f0d0c03110f03040602010b030708030901090302150903011e0507030905190516 77
    0xc026180e062010080a446041e40030000744102c000043c00801400700d50a8141d030404c05941d14a0301020364101d002d031811a103500c1c140e055400f103a01c01d01840d900481e22401c64140c00094103600a4403c90303659200d5150f900c45604041c0c045040c110030760301e40e055460301c010a010704100d031079110b480403a40141d0f61440b0072408220021000c64000004c03400500c5182420851000c42410260000062400091103148004002090365072264140d038050460300c186105801c0c0c81d078103031a984120784548e16016201b401ca10103251440000c0b140c801491a82ea02521070070140d4080c1d8918400f00484005405803d403041c114000410203000104074030340c0040b5951503400181400c101940d04007500c550000c100c0b01807a6600104045c017107940c1a100540614640d150b40701840c05211100b42d41740d401c007013034004400d01ca10003410300c03017030034050401007501c0c3c1307581c190100c0b2622030f00100030b600060040789000b422100c581b11514040d00542d080526079500c0080d00114903005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 611258579 1250 611257329 611257351
    0x21030a030207031e020714040e01060b0a0912050d03020c0f06240402120615041206151d01050402130518070f11060a0b0406030f0606140102010b1e0d0b 67
    0x1464107044e4054402e482020300030040c2403040c0e40500c002520b410140c003c40d0b146100740326824030140c0f25030f80044540c01c0180020080d8948071261444030750721540203000000c450060104801d01c00b903001e408200d40c44401004115174501e0203402a400c0031300c024101d03002c0c030411146e200d0000d00540348a001890f00400e008110083d1169280e4082c3c10103038061481444103d121030b40141065411a0044a2402181c02508100e0540d8030445d0003981c3c1d400ca00408490400c196a0400c88100d14103c2040c041c680c0c60f0b500e0310304c81c46c00c07484101c00c90210700c03001008103040a5000b4200e0b203403403031a0301044644a901013071a1002544d403180071141d200701040f01c03a41d4406900316450000e40307000d201e00f0141c4100169100001b030001501d056441e0341a6006644541c0048021580300031440d101c9002400c0110040000d881a43c1d8042140c03001981c1d20f41c4103103d41800110004d1161050b071304030050b0101d418045141c41908140b0002e80807000c10509a84280714503800e081c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 611259829 1250 611258579 611258587
    0x5040e040c2d090212131410020301210312150f1d0606040509010e06010306091103190506030a030503040f0539060f030712021801020609150621030a0302 68
    0x7407120390b806540c4040310480c4140b08090f030b9002079071940ea800c20401c0ca000400c042d41d40c28078902c080025481d03c00244644480a00704020030b402550486001990b6810204410300d40c06528401d200801000079400e10349401034009207030f001c1c0382030460300d0400d858541e44a0403000d08038205500141818503018880300003103801c3d080301c0c650000c000d0300c0082c1054a8032001c0303030401c00c040c0200c000d0f41c010f40002541d02e9200364000d9000b44100841171046107540c0741c0001083e0700980304604405002491184075000c0c0b400342da8007900001c1e0081c50f44880d16207084525810140045580301070701003110020900400101504814100a03101c90b501c0c544900480030340c1032010708001c00280341c40080f9656504054035506001f40500594980c0e44503812602801d000300c460341101d10100300c945000510444a05040c0000e030200e60b4140c5410081541e658009008030400c00c94240c0000c100e0700348004610f0174103101e400318034070f11806402c03154195000301100d03000080e4049 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 611261079 1250 611259829 611259899
    0x91b05090612030307050d1b1d3102040b0c0105060108010e090307030c050c0a03031101060b090f040b060c0102120a0b1c02010327150608030a05040e040c 68
    0x40d64050304030204840c0000c00031610b00710719803207010042c44c1ca020310401244c82000e0001903000780e00700842980c41c81161265041000c0e00c84104014040f8510700703d5440082d00d81002181d4440c507890246441c240c2c602c86082e01610301049105100c03e13203409100006524400f88041d21540902d03000120b40e501d0140001001d081050f881000e1014210f0305001d2800000300c21103440c181c00d03190040541c1d003141010351030010024001e0f40c000d1103400f8008141544440303142e501202410082c0513182d510900090070340036104e04036034058132880915000e4135043d032040d124854060405818408050741329403c87e001a003040040d180d6a100300801d810b01031154104125003154002d084550401000c0407041c2c001000a060603038134014100071180c6000c81c41c0302008140e0344c0c580c480d0040e1a0142d950402c1c0d070411405075007054800300307030a9008000d035407004c0001d65600b42054503081210340300d00e0000d003044e12491b0741c00d000442c50510950041040e89039040450100c14044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 611262329 1250 611261079 611261089
    0xc1101050f1902190804150306081b01021002210703090c080d0f0302070812090120070515010515030a11160b07050a09091e020c100614010c030f0201091b05 69
    0xc49040107121003208030b1000045c41d4601900c4c10f94030b4043c00034400e04407100d025401000107400c4071505200b0300820f00e044240354035000d0b00c810420ba00340e0b42c02501ca07030a154107034000c0c980b525450b14003000107008010040c501a603030100d024980401e4240054440c113845000a80017a260b5401c4004041244c60704450000c44044d0344e45011850040e103078072090103038001c810b01b403246002d04a0100f0310350340094010b0201406204003555181e521041000030701c0e44200022101070141e488240d01d400a499038480c1240c0303001d05640b03c4041e40c12038003102030b0b100030944441d480d43c0d141141100b19030040509104100d107075034116200396a00303000050f00801418001008400c0018100300c0f640f15058208480098001040a003001c0d0224032000340403103104011103101041d0b4216420000070821a40020300500b008541c3c3c0307802000d10200d451181c0e00e401314080c00315580000e031150281c814104800e20001501a84998038280080150b18150048484e051400d0002d4070341 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 611263579 1250 611262329 611262343
    0x7051c0f380c03010e0606161205040303080f040f0215040f0b0c01150f0501051804090804050a170307140f0f03040f0504060f0618090f23070c1101050f1902 69
    0x841401800c40d1724005403416101e90040015020706000300d0304008100200114102c05603101515072001d03481c07243c00410a8200e444240c2c00110440c021821844004461900458008440c0307a120800d60b001d000b01c60008a040344040e0104101c00980e14020801c61340242220003411681e40044403c00d07800e40d102d980000170100180481001401034448240c81160821308141e61240d841e2080b0084089174641c903150014104480c44040200190040c010740300b007200d804000c580c43d5401c4070665008101c0303840c03c1d0b9004100c8000410704420074000c05007051022522224190780120b400c01025400d8170301c3e5607202090511400c11654100e01c0a41002e036001c016a901c0c0070043e840024030b074854503080c882100ca03c084044800c0801102500c401c51003806409010390058004041c4080c1c844078111301c0f290700031440010100310b940030303283c1507441003850009911044210041100c5550601400f040700809420052000d0f00d41c1c541c0c101c005a2441c1044030003c1c1c00c00403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 611264829 1250 611263579 611263591
    0x507020a0317250210020d06080d0203340203010216060501080d2c0604060c0312020304030c020f0f1315080307150c03020f070b0907051c0f38 63
    0x1184400b0400d007980d040f034a650119180328543c0300350080d110001c1c3d09080c40c95045805c1c0c02d0000841c0e0190314035541107441240c001c0d00031200301540c0c91a0498a9004401c06d0b8914141070788401050711010a400c06100810080850980c20956000a007282e2100c06150505121084400d0901c081c0b40701c3d190052041e480680780d081c0d011400208070f1308040195000c24080c030130702c090350a40c1e420102e080b0070344040c2941d5592078a405000d000072812a8003100040d50440ca407100c203c00b01d0090f60b01582c0d00d81c64061034914903908202c0070141c20468550064180760700c028081d80c03030b02d50688211360350103c0003130b4a00c0c0c51079810280c0d240e160040400b660040021100140c80030001090141c0b80480015441100810490292040c001030704074051003c140d260510155000050150401d541110802d590b64014800c8440d0000c2c0556001c0d04080040c20210380310000c1d80034842d10034034203000d030f240d0400140d421810021107808400350362054128017031516990407580150b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 611266079 1250 611264829 611264867
    0xb0a050307031820060408030406110106050405040b09010c0318080a1e0302091201060509040803040f0b0109020d0c0903030f030f09080f0304020114070b180a0c0315200d021c0507020a03 82
    0x290030000307ca07039203200703900c940401c00c08071006084440030203600c120040c00006205200078101418a02e410020503558440294a40426034a956020b8803501e0001d925951000780b800303040b512844190740141c0709400601c03585599505880c2c032b8079407207403401c500b003501c006885100d10010b00600450a60882d0002d03031401c0350501c09036079401201d41d03201d03500c1294070b0f5513039545160480085415460003006140c00d4000810031480d19000381c10501b80e080010004e1481c5414116000d01302c91001501007000030003034070a021b102c0c1d0889403003406102d0000c1000e121039981c1041d030b9445252804910b07907001c02488115a800120500d0040555120504003901615a20385990020703120011100340380451100512044c01940401900300710075a84240d60380c01c7c1100f05140c002c4500c15114a01000c1c0070320104046102c06002520317803000c0e03051101c01009076009500c0000344614000d140f03402d07250302e408030780503061003002158081d181500103458054020607101c1c018120728 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 611267329 1250 611266079 611266087
    0x9030a0e060304170304051905011d010b0f09070908071d062b020d050a200a08060c0c12071518020916210509160b0a05030703182006 59
    0x45201303815607209428403050308581c0d80d29031703252103071405019002e100d4064441c02c0ca08400d0041c190300c1007601c0c1c03c0b02826021902d845108540c202c0710980005684680f1300c9910391400c0c01c050301300300e40c8011541405000e650f200c4a51920702822036111114440d44100000c0003110b07019140ba030000e01c10348480c5d00020001c521740c4140300100544043c0d0100440c602c9065544507089002102d07005001d60ba84201c0f5400c00c960030340e203100303e03610160501c031000181504002151400303c5001601508854a49400d0030409910050842c91284291045407104880041c0180546485040000c0f2000000c541ca4402c0d0391520707a05c1600200e654078442c025071206091940d11a8046055289000320104103a400e05040041d00500210014818280124542c0030900451009040740c49002c281c002c1d40c00c103692180100c0b40c4100c0140138030243c0c81d020b07001a54000300c0300d080c04103440d410001a0650050307048010307140040e100d80d5003419404654090300311700e0340c1903508034a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 611268579 1250 611267329 611267333
    0x40518061f0507080702060f030c0c0d08010605180406050306070206040b131e0c1a1803190f110d03090501030b011d010e040912090e1006020a020111030c0609030a0e060304 76
    0x1d00d001d03e42010300001000640d9804565421040b81e400d01540d24800c5c0d2282170020000510b90040c0d000e14000c1e20540c801d500c801400764034040e0494505e80d841900c1c1c29119a0a660107415058072541c0007615141c0100c0c080d0303418400584594400d0f801412645801c0c10000e880c444040c10003400700c07262081402c0420401c52610f000401c00340003800484120340b40ca198a00b007154000c0f4410103064481c40c85928280c0002c01c207860a410140f40c0e101e018104040c1c84410b0002d010700d2180070800b90100140310344000000d03030342c000c261400c0f010083d10049984144044811400280564802c1c001c0350f8140c2325002c2060002c0ca080542c00c1c4101000075062448201c410741404000801b0304c40650700ca070414801d01c0d60101510305030050329980034000c98418007480141d56880d900140c6a81d000500c01c2c011108158010440844039400640d4204070040070340c80302d07002c20032001094030701c20003059000f0170071000116a81c05d86540020007030a90301300b0091040c4410428480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 611269829 1250 611268579 611268587
    0xb04020c0111090310090f140312010605130b0301120b040203100c020706030606050702030601170c04020f0712080f06090a1103070914060408061611061302090609010308120c040518061f 82
    0xd01345602110007249502300904191031030140103405690002d5800011502d103601c84e0103000f40106d80300000707000e151114007400007030109000c0c850144500719020008150f200c802590030034000b40540c1c0440b01c6001c00002030341d0303000e4550400b5a02c20402004010760502c145801020a49001403d024140c0d0010741c4a0b04180300b9040541400f8010410b00001884110030030704000b8011582c5280100e207070003071a0040764007541e242002400d40d00ba010b0003003080d5881103100e04c4401d809035940c8020400200ea010703103e400c40c07a80c0d554100d00000b08800c001c6000c2c480b15290551070340e01e0401101ca65002d8500f406028010034801004030b003c0004580c2c0d044008a0003080c00c0c1d0100c280c8c00c6404d609045920441440f0313003010f014808245c8090444101c0c0240c0304e8134415960032003401081c5a0070300c8014821170007001a41c140703109242e881900082c402203050324140d611000524121580030030a101c00e6050410300c131903441c1c44841020480520004107460764101071002d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 611271079 1250 611269829 611269853
    0x60a06092103090b040306051e0105010c0308070203130801092d02040b120d1716080114120d0306230a03020603041703011401020118050309040b04020c011109031009 73
    0x940401c001401101014020034006004d040d440c450151100d550b81414000707414141d595002454280c2092407051032215841411fa48060f1101140e48400d503404030352104000b003e2070214042403150360b0345150007121850041013402c00103e03c202c0340e0b05204240c9004106100084482c20115003858040c8418200394607404071030000740c14840b00003040111041c80080280740c0103c550488106030021100002202e03000c00b42e00141c1d0740c0c11040c03030b0b01c40d5090314010b000c030300c180c0f004102154050200980c1e10101900720620701c200080c14a15220000b0000000310703450b40024854046110040d03075002008411062180b03002c90085a00d600d2103000190003188000001380c140246100078914018010384030954a40e580c501301160091050403a500650030b103000010502602d124440b20f030b81d0040c000d58a019000002c10008100d002042da401c0b81c1c0910000c6d000c1c0c10280300f8480703528940c8060982d650303a0102003500b8450129164030102d850444100c010903480310b03003d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 611272329 1250 611271079 611271119
    0x615060e15070209131b03080301180207231204150c21020601030c0803032e05030a06020a0324030b0709030b0702070501020f191e02030d08060a0609 66
    0x407010300480c0e884800d80d8441c060010750040c0c040004e101d80c1101580c80040403d00030182c05010415011308400c00543d45d00c00a800c0b0602400107111030903c10b50050301400351610014130381a0b01f5a201d0700e030714556000509d04449040f1400c40d414500b80075440c01201296030552030582003200504e04407030720042c0d80c001c0104104281d003c0102c18040854140444481500d0303001d01030000942e9802c5c2404100c41c446031007039001030550000800e0368015a60060368540c00c003007c0d9a03540b0100c0d0061400a16801c1006000419403000d000043c0114060350303000d44d5030014110b01405584050b400303944040c1c4400302c1c8200c2d40c468120343c0800d80794000c01004458450410407a504241c54001600c2d0104400a00a17010340005003401100e90a03001c0d00c1e00c980c0c0c0e55002941300d10751491505c418801d101d024400044c80189140d0074200c0348404404044040e030040391030590131501880c041506001840240e01d03241c0c90800c0202000c1c540614600d0924460022440c444015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 611273579 1250 611272329 611272339
    0x4050606010315090e15130c0e060306040b090c060a0509100e060307050f2a010c0305151c061b020709060b161703151f020606010513150504030615060e 67
    0x54407542c2500f400403428420142d50714842c6c40c200840b0000c44285e03c41c0040301c03104a01d030000031700f89441d124440c2c411840280900040c0c0e65903200c42004100c0200110000e019541c1c101e0584d42e1118041c0c104903040740c1d28192039400000c280b164031650140c54400380450103410100695400b0100c13039001e08185449900c44041d04010081409040403548883d907800100c40c83c000030800342d030721003548550000d100b60a03a80341c00b40d0450301c0a46000e10b892402042185060510b410b9400c07644200440e601211803094a0310000c071850040c2c45a403c8003800c42c0c070700c401c950411004000d050f100c007040051519003001e0448520640c1e90142c248040758410700d0520040039080002e0041c5020321035942d1500e0441c1444001643d07011030712404400b01c460308042d0010445043c0301142d0740041160f510386000565240e04000d49003601d5100184000c5200b00740c0b0810301c0800c1000f1388034035480c1c5045242490940d005400e00c412500769403002000069841010f42d43c40103800d1362 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 611274829 1250 611273579 611273591
    0x509040503190210090326060a091a0303070501330e071803030f1b020604030816050708030d0e030a0e010e0a091d061303050d15031a0405060601031509 67
    0x103001d904001300a00d09400a5160030f04030010304d40c0100020010b036111940c5c05d40311440030420801408001e0b07a001303410007903483c81407040888a9000c00d2103844c14030b0780741800010b01030009113568425201104e40c1d0b510340c40810844901ca02c000c200d400165800341c450a070210003424040d200303511541850101038008145140d010300d0500c0d14544c2401c1480803150b4683c00c014013407401c460f03a03817000507008a8001400c10303a0400c0b1a001c403640203102501c0c103481e68072a600342e9000100744c807162042c40e2100d080040c10800801d0024202e01014648031401c515a50089440d075652151403034004004070381030a0780c8160560003482d0309007898130743d400102003c40d400403480d4011a2441e45025282000c000010352100030301c0720500700702c803026034074654402c8d00c0090642c030040c041203081c0600403c01c175490b0060303650b03043c2100780c4d04891640c0741c90380d40c0700d0082c500d4503078004001e02e000c4c0000d0200c01d1007401d0b130002003030030103000c400c0007c1440d401c003a00620512010a607284 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 611276079 1250 611274829 611274877
    0xb0d080a080c07120f0807020f060c0f221a030105030a030c0c2d050d08070b0406110f0309060108060105030a150f0204080717010525032d05010509040503 68
    0x8019141c505400071030319944403103c034101170000b00c40c010541000c9a25400054480c1b440010f21004202111002d01000d45440b0001446a00092801007a480c0e0922001019040c4201c0341c0714104400c440600394185801e8402c440550000641303282140b0800050000e9200003585900096051501884012079400c22940524080e08551a04803a4050b03004840c00d460741c1000e04200c240142210240d0707280304100039048440401090b03c0000c2c480c020206d40743d20074030b592003801554085098550030b0650b0b13206501001507180c803200048140170402c2c100b040481e0150000400410503541894006a5200e440c024024040c0c099101d0070313200c00006804c1075505075010304c000e54480c0e40714108641c46040a002d442e810141c0400303070044043d414081c1a00071982e80b4020080b161141c0e03000703468181148051400d040c1c6484c280b800780b07100c141400084c070340c15820164480e058941608181c3d00103a01907131242c0b5010301032001059006c41214220705500c0e00d000c0e1500414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 611277329 1250 611276079 611276101
    0x60c0215031f17060115140301030807111504090b010309020414011806050d1419110a06090819170f030a06050d0302120334030b0d080a08 61
    0x3a103481a036800c000300502281c0c0d80c841501c4018a849900e02a4040352588400b4040e800c0c2c82e03204602e564450401080400800802c003552200140b03419041458041c11102c8154030a9008451086000825005100ba12502018007003c1241c4510114604080c0345040d8002c078000c00d40ba00790354106800360b5a00903840001c3c0c040e0f01900921080b22050341031181c00318240b02c1c1c00c1c88100e00e100c00c1d40842c41e01e0b11599095070401400f070a00d009150303c8008c080d01c0245040b901910480d2945038240590039211840170744140c0300002112126414080d11b40120740c070410500c2110704042c0444000820404042044821050300b050598285102101c00b4814001c0400c900081e0201180c0b002d0002540700e2001c940042c0a0a5035840070b01801115404018006800c409443c01c412015080155001042c2030300300c0d42c014141101144100f034803012040510300295009500568240c0200f150895044480c0403d44d900e540f5604030a1040700710308010400b0f0301d400142d801c101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 611278579 1250 611277329 611277349
    0xc0804120e03060a0504110105120106050714100f06090606050708030c13080a050106170c040c1818060b09010804080c0a060216020111160303033908060f0a060c02 72
    0x2d0454450b0300b0001a07050041005443c256a00c464a40321000554020b004075406181c2e0142411200c1c2e1030040211215000050222540c00590852412000040200c05460341040c40000307041221001810b04846580e8001101c1c00e04182c03080229540050542e108150801d000d00c1d5690384078404001070b80f051110043c0490b013040c40205d615100014039100b07031445071001b0400c25807500c101d404451442d0129181c1c80c1d00c0380740c0980c068107154001c2e29445070300d800e120f100a0071410720015410300715081403e04909102c44903811810718081c4800400048107130903c2c040841000809500700200003034081000001c425001a50411081d2032460b00f168003151075003405080040410700c0640700342c0c0080c18083c014003140802003000c2964201c02c10031b84074143d00d15941036001d02070a25560f041c02e0140061410590400105454094900036503403141098505014000d09400b80c9045d014860b0014411141e440368000c2030140e80c824144411861018400141c0d0190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 611279829 1250 611278579 611278607
    0x2091305010605041a1305040e070302031b0102012a0c1716060b090603030d240914090610030f062a02013602060d02040b0a0e040c080412 61
    0x12808000250503540040600281c481e1003021201040c0c2044070842d446c01101c2c3d4000084405000030003007443c05910494540520400f41e50060350f590b0006828281c0d441c18801140400351100b4609680c2842040c1c018514090250284851400d520382055886d200007814400e00008a6051115070010b40b00368686414086a071960300c0190759068902c181812603000b401c25155043d103113007003042948200c0c0c0203030003141030100c0507031480040d011852008407030795417081c40483c0c0c80e0104241d46000c0d207407104000ca24840032000582c081c4900525001c0303103402031024800c00c000426440400c880c2c111242e840301c071219041560043c00028162407017009241c1c000581c0c00e40306902c0442246241d00204034191800074440d02c0d82400300c520140c05198211401d00d030421048850599a002808060401541043c000220391003a00065144840400c890078a150312a020078031028080c4d40071300c12200345800c00f6050320300192004000c4d0412030002c0d58a43e01c6001c0080f1000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 611281079 1250 611279829 611279831
    0xb16030926040f140f01021b13060906121217061302040902070c061209031704050309130e0c0a080d03110c0709050f180604030503060f0603090f070f18020913 70
    0x380d50785000c2013a0400104594000d44c10022004a00e600200d601060300074220220b410b40c00b1180104081c0d1298503e00c900b042e030365011301150004162060b18090084161600d40f00760290604480210710b02800104101e24402815618202c4040d81a04000252480740305a8240781100d400f03070059400030314000f03201003000020b00500b10349100460b6a03c5d16a02045074101003450141c86100310040c0104600603411085805100ea043d90b025010f002524180f1b003a040000b07458941e1381a260042c0c0b901c0e80c41c0a14440014000c000c120761040303d000c0c2e459460715a81c251190f12100d0f501041c035507174115015001240c2400c9440c40024417083d40c00803900c40300884000c1a0584000c00010040800946900d182d00103182d54034024000a002c1540c40d650300703c840c3c0e0b100610740c9401c114140303184401511404027441c00365101201030300c0e03040c17507950506103015048d40c0305000320781c800c1100b0401103d1900410f000002c0003940581d80f000f0080109802c8003000440454207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 611282329 1250 611281079 611281109
    0x1005061f1409120c010f080108030a05071a040b01080f0d140706091e050c0301090218070203040504050c0a0206060d02210c2710051003050a0b030a0b1603092604 71
    0x1d01140c10141141c01340c0b00d01c0071b00300e0005011103580d0400d020781d4003641e1041100015445c05a000b0300106481500303c0c03006124080c00d1010120310548086075182c100c0d20050060b41806d00c03090288641040060501c0700e01c01c0c40050051040100c25002060001030510900c2480d411120f28682c100200c202060f020f421148420108640c081d2010300948100315103034901801041c0145400810a403501c0c43c0d0404144444e940152005c825444100400200d540710390203030611642032040c08a44817032460710068109030004001d2032040c128400c0e04001655441b0031911845030b901c00c0801d003024154102441c5c442411800e0b6417104008800c1062296684000300289265502c816105d455036511080c5011107070042c10f60200c55800c60025052099002e181d2003440054007041941c080c0c004030b0f080400406060f1500344540042042d000d0304c205c00040c64044510b410818800c5a0300d552452140000b01708038804129034042c0c8a41c0a0030b01520044c09014003000c000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 611283579 1250 611282329 611282359
    0x20f1002030c07060305010b0316230403020109050402120f09250501020c060a141e07151a0604230a1508010504050f0a0c03110c1005061f1409 63
    0x602d8001c0b01e04007210344603075100451028441d0140e941202c09848100c2d055840f90007401a00700c51034600c0c82d08000041500318052400d402c603008003d492640c0e116522415800014441207043d00424061030040003002070b00c4810007481075011014440075242a1501d82800f401c0c03100c41001c5078400d10f01903a04880f04142c4100c000202c8509070200c595242c040702c203000d4640034001c958804210405071011744208144010300405014100c404143c8800b40c040c1070082e00014000d03248101c5041090282014a11803001da4000104c1805013002d1510000b42c2c151055006802c06c4090004030404175070301c1c10700340c1014810007d2801002c240c0343c0240b1000412210780400010b030640b00001400d0070148205130040719101500920fa948001c562800ba081d100400c41c1099900d08012484084007409003a0203c01da5002c0d10700120000d1407901514005001c19105458202469410310b6040c400100602601d0400340f04244001141e15070301d00680e14079540140d10054403001d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 611284829 1250 611283579 611283583
    0xf15210708070e010f050a0605032d04050d3b1c05061902090105180d0c0f0509060301111c02070f0305071e050c010c0c170105060102070617040807020f1002 69
    0x4140c40301d0405ca44400b969030410841c941001d407041d03101181c010070100e001400d01903071008001d400c81e004c0c01640001700410303510054003260191882d0700a03848049406078010b0345094a860402100319686920051012140141c5038205000d1b0f0306090070000c40c3e45801c5d845c00340081d00d032941e40d400030003603051054440b6001c6502c0c1c445000e854501e204080c11510a41d6a000010f9603110700300a060a10b080d4100490300880354406d503410a1403002611030010040900084941e0240f26440c200c00d22800050242207581720383d0500c0c40d41540d180e01c0c842580d80014408040e4485a410741c0d044130001d1040a00241c0b0030306110300302c0e0003419046401002410700c41e6411004a4103942c109003240998a100140180c1003840c458440d50701c1040080101c0340110215001c43c1d5031002074002c0504491503030b89160b5103440400400703603018455180180781da030805000c004441808201c2d8140020402809a01e021581d0030942d25984d01049451300b014001d910031407401c0c0c0020f5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 611286079 1250 611284829 611284831
    0x100210020c01241a0f09030d11070501080f0c090118150e09100501120b0d060b0f030a0302100f021603030b270109050c0c06010b030f15210708070e 65
    0x40d0328005015001e54600d0041c00510445013007001e003c0c0311428042034100140e2003401c40e104071040911841c0c206540512444c41846480d48407480fa041500080c50b040910315404079044c407540804000c44800c606000d1030b48100d04100b49a900c1004030f0060f107421143e03507110b0603c00c14482c0085108200d1601d881c251550301e86411849424103403c10400003412680c005c510425110104095402001d20905805100b48040303240141000800c2d10401045800d942d400d81342d40002d806c605090084001c8410158041c024010301c40e10f000c1d65807034078040b0f102c0b002c6684c0c0030380e0300080241c1e0781611310504415a40241003492030078010060503040c1c1c40710344a1449950b00b04094040420000c000c19054040008940c3c0390400507001002c004100710f010074400c0012280c8048188945806000f40b41401512420300c0141c1c446032a400800e190625402c1c900450303001e039281c55808040420190803407404109140d91503041c461541e0082900d4410140b02080b160701c0d15082d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 611287329 1250 611286079 611286101
    0x6020d0314090a0f02041118040b04021204120509090c13060e1503040f08040f060201141b0a1103030a09060e0313120819030504051b010e100210020c01 67
    0x50207140c0000c10a100514001c1c1c9000400d50301c1050258002412a9201c03034149000070000036a0740910b0120003500d030b002100c940006199500b0501c400c0c505481015409001902d0031420007240c1001c0f04203403040604040d0603912029034003041144039038110750484801501e0101d507414040038104141e0070120b240c03403610810b0040816064460034aa044189000700102002c0c05260304102039070b48054810348201c050301c415500415407480080000700118104d82c0b0072180b601c4402421568111600b003011504481802240304403d4150390301e4a42c60b6500c3d41d0b071404c5210080c0d8141d112061404c0d05800080100708081d2400d0b48100795140c0210001d000207a1034461980c0c80b4828008654076585c3d54140c1480f128103c80740c184101d40c82202c00c1c61400100700c500480b4030310f10a80410004c1c1c0c85008001c2082030500c5441070701248203038011005c41c0f120f00081d01d4601030444103400f4612811080390344510030041d0680c02e00b10b50800b159543c0c55520828042d0005101c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 611288579 1250 611287329 611287331
    0x70605061c17090d0602041413020301150809030d06030606050111010e030406030e100509030315030c031e03040909050703210c060209040f020d06140f0102030714010905060106020d03 81
    0x109600042441c0401001c40d07001036188107064100c0c05400301d642002d50b00036003100401034098002100c5200400c0901544012182101188410000f0300c44d20010512041030050004100403580c10a00c40d021403441e03709000d1a40c0c403401c800f480c500403d0201080340781019030010900c101e076400101610020380c0da02c8007020304840c5141c240d079441d5644495990042204105580c4640d019403030b00d0210006440c56494001041000d480c0146d03902102c4d500000103110400110f9003108181e14800d40207001c0c0540300e100041c1c0c4501001080c00090b108004400c0c4800c4c9081c4101e90190040c134204011030851803c00c02e5907a01a400110f8810b1000b00c03110061340b00584e6003100d003507510341c0d40c8500301e9200c1e42e40b000a034100c4071829030080d480360860220031905001034844200200ca0005106103031400341000351441000781c0303010f81c103031221450141e41c2c0030048405a42e000456009074000c00000e0070b00400280d41d01514900a84002080090f40030441c000052910f83d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 611289829 1250 611288579 611288599
    0x610052502041409061501170603030426060a140403180519031101030213150c080c010b0a0b0a02030912070e070c140c0a061101060902030a02040302043204051207060506 75
    0x48040d100c0072203050b1287c0800d80e40500b442c0d441e0b0741d540300a03500c010050142e90a09942c1d00d003c03a4541c0140d44000c44008000c1044903034114100001940401c1c0c070a400d004803440b0030700c180c0c02c40034007500140410011003440d0030081c58070819540204006000b030100d43c1060140000548400c1c00202c0d0700b0402c441900751558840c0c000c0c2ca540c40c0c7c41e40c02082c0301d00d00d008500d4001001602e0075074184250544100007040c43c10010780055082d51001048800420742004841b8120703070020080e11409100c01803200d5800020b8031110301b010780341d090307141043c40c11851a040c50765025080f20f01345007041207030031544644020192885101c203c00002ea01c011410303180c0070802c0e00150003540e40d503410441d044c45480d560404100d400c0000801d0b0351108405070a036030040f220b100396280c0020302001107051901c00c01e04494140103010341100c00b0300c0e4080c04112451181000c2445800000c641442018040260701c00345000c0724650f100e40d80c2c40c16002034603045508600c40e4840705 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 611291079 1250 611289829 611289841
    0x60109170114100302090708130516080f010c050f0705070b030c2d030402130e0105070f1d0f19120c21050606090703090813030b061005250204140906 66
    0x141d8000c050381e6000b00540587d59411108944402004149241d0300b0030b15031204002c10000d101000c110451410482c00e002c2c01e00900928141c01c401d0300c4031560303140000401d8010307440020f507001c03c101040d44c0d5980300c0d5a810a00e2502e0959000a0543c1d1000014003c4034508034008000d5002c0904c00b45004500e4590b4140104140b07520300500311400304000350040c908075407102c1440300d4408000031110019201c55085800c100c8414020a03448940303007420580092500003001c0c1c440000007507600070440490040d2440f041d030030380540f00000f24846195680c4100d00c1c0644070356400300502040c9400c0040c61800203110700c0b1045005200c0da40e0b07000f0200d142196441e904240201800d4881006001d0b004200401070403c01da90350800390000380141008002901c000d040d05850a401e60400346c011685c09003005210707448005440444641100540d841e0f91040300742204030407504a180025450745010080d8041e10344051303030b800e1002040c1c40b140a50400c004440c00c5035205 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 611292329 1250 611291079 611291101
    0x9030106091512050c01050d140712050c04030314090a032a06090b03040b1008010e2401080a0b2505070302010f1509020d0e06070c1b0617060109170114 67
    0xf0070001c2c006420a6101411550003a4010400601031180c00900c061118040305a9031384265004000103810107a1020000300d44d010752074210b04d4107110305141c94036599010340600512014126040030100f41c51103540c0e9074541c010700850700040160b0040a0000d150580c044e400322180050441240d00407c129100703040c1001500d5400301c07814a9903ca50700e455082400003084403c8800d400c1001107410a401c0c001d2104084508004100d54403500c0010b028040403070040f0384541405c900100040000003400c0d04025410501025541d2107441038600a82c07101c011001c11907040784502c0d608190701c80000c14409000f130b8001c1040c44c480365000b40070398189955400740090f180700140807251403580207007008003420000248180c4012447c2e0704142088441801084010101d002885441649050802d00c01e50222042500380240544010452148001041301d0341e80010701c985d0180390098050558403910600310441c01000034041e010801a280728805140040707a412424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 611293579 1250 611292329 611292359
    0xe061606230106110a110402090d0203071509120203030a0f050717040302012303060415080610050a0b1227070e01080709110d050403050409050103060209010f021b010f05090301060915 81
    0x100000010044d50f94178108006504582c5c02d156204e08962b10100c01603408018110080412050840032402141c1024201500303d500491a2a0030781040c80010b941c040100e90170b80c00c16003050385203000289012540760040d00f40081107549217826400d202a2a0009081240d100360303955030003041001c101c0d0b001c901c1d0115510090640600115404e03107496041010021084030858052a650705455440c11000356400c203104a0340380300600c03882c1010000710000d80b840c00d64541c5491460441c980c1020030003859204204804010740c04855142110401407482000131100c80d16240e00d10102600002e21500c0440d2190a8001032030250b1030091850560030024142d00f0800d40104050103450001e00483c10028204030120b24048180710b8030740a18080c850050f1078545880001d03081401c950300d450195404419403051001518100c0031242c542860411000d0148000030343d00d9018840b026076140d42481404074804075164418800d4041000404042d02da40d15140081141 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 611294829 1250 611293579 611293583
    0x71e0b0703091208060d0b1f0b040f050402090609120607020106080a052a270a020f07061a06071b050a030210050a020a14060f070e061606230106110a 66
    0x6680a424480c00d4040c00e401399100d44042c1608142c00d00c41ea880391031500f4102d03000e0341614a00d055018052103501103100262011390702031480d0600b000078101401034980315151041d5000100081c90780c558000341d03044250003030081806070110003000e54441004030741c110010740c40e04c100081e540d60300240c40118280c0000c05003050000d00044401840c03000c8440032030488120001405c562613580d400c01066402c06129607165156a50354128220086c00001c0f0150062240483d40040c001c1200e4803a03500800028254080c0403141c0340140601005039485080400c0b10b03001d024a04907807a400051004c01c50040702d40b03880070081c02541034007010b9007140403601d0a510060203400140302d00c581a0041341c11402240c0c1e22131a407240c00c20011927554201e1414450981c4c6401031154000f40e007401d005605020820100d401c41c010700d00b099921001030905e00c806c1c01030903032090200c8a02c41100500c1340740400307010320000d1400e2040d1800500043e0700102c11400225450003419 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 611296079 1250 611294829 611294843
    0x1513050601032d020309010209030f030703082401050a110706180503070b03160c021003020c0c010c150209010c0b180d0e0a050427060b120106030c09050c071e0b070309 74
    0x94880f0103a0001c0d00001c0c0300a015640c204010300c3c0907a07040003d4000f45107210000c50b43d0780c1c0c09143c01000d01c0c1015202400c0d24003842d0b07a000d4550311860055000510a2900c03586030003001e4811100004290647e000034019000d020501e580e2200340f2240368002d10703d0703845c911a87c4000b810356421003485107011144090000c01d031000c00d082c001245541d824030308004d407201d6a4001862000e9000c00d004040383c5e0010320417050300824020310075440000d003007411400400d43c41e4031180c46a202d00301d40000d640007500010300d0303015000c40040c05402ca200070744c4501d041c480704006800c11a60b001024411a800a0f000a101e0003240c000b00f980a01224440361030142400043d0100b20580e20286814400d43e60200c0c00b10302801a0740c501882c000b2880340c0c2c80e8018840c04041d444001200c503414040203001151080c509442101c00d280070010702a0354108450600c0e0244a00c014070104c1c142524a17009101d0329018003145d07001e244000180d456142d01070781101c1d040ea030014801 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 611297329 1250 611296079 611296151
    0x150518040f020d022d090f090601092301090606030501050616110f1804023609010b060a03090605070809062a0a0804050d020102130905151305060103 66
    0x40c02c0c407080b80e8460342d201500ca00080100448907000081c800c141072001036031400c0380171000c1d00d041110b45400192285400081341006c00350b681e04c8010501441064540300ca03a1a200030b0105204d1340401c80c8103480b110429612078510364003426540c851000001c1c10440086164a4003200312049044043d2007990001c1c2a9a5800c50300d00d03c1c900010350040200c00304d011140c44400d404040d02030390100088081c41d0501c1040301d80076480440038002000318241c080300441c0086e0b040c0c5c3d0042d080f00010460790340c1501c41405000c0310b80455421100c003040406c20907415402071320407103104070418401e0307683d0080200d8071010101e0b480a02a840100429620200c840100e50b82141004000e2480f40c0a4001d00390740e64482004840081e103804100410f0010500c091700c80610704d88000e500d8007030301d0750b54100d5460140c064098015680c401040400c86005000b0100c1007016110030540c08420504200a083c02c840d20f5000c02c1c142800e042c1c095503541440b40c10310781410064020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 611298579 1250 611297329 611297333
    0x615050403060c030618051e1605030a15030b09070b0324030703020901080708190c1707030204050c03070f030606050f071106030c040501020d03060807050919150518040f 75
    0x9001c083c110f900c1030554600340482c280c245040b491150b004028408180303802e0101c1d222540361201008185049882d00a0052609041c00c9000c110781b15072420710b85a0b00c852000034001d1417108020041580e90401c00010459050b41c840c1c4600f02c00c20560305e030250303281140f4025100880d40400c1c9104c0050f50580a9006031002c0303c420703031001d0119181207407207a010480d00202078026010f6940800c00c1000708113001c1044540035040b42c2110b48460b00030342e07a00180c1e01c1c0c050084000d0031180d0080c0c8440c03041c0400820005580081007800f640c14900003134140c80d441a503c500c0091030100101c040a400303400f401d4203c400a944461a01036018804d0500340c11410302110804580050000507a07945401355010b00003070124503596074500000a86048180611141450308240f020030142c0307808550281121802c0d20192015075030526949040c034050f03404413400d00e10b070050600940d406412400251002078030526028401c0700300d20007010b601141d00400d401040406080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 611299829 1250 611298579 611298581
    0x5151e01030b0403120501091b03060506181206131205280332130b0105091b1305310218030601090906050f06180402060d090803010801061505040306 66
    0x1900034001d280c090105d10b80210761800f620030a07031002d030155407503041004c415a0b919a401040396410304042002500e80320114400703000345031100d40b40010580d40d8482310384400c07044a10f401f100d131054a126140c00040902e140103224810f44440304000d5030000d001c3d00a2040780d00c2d00000860720000d000e0358490321080c13042e540d004c0a0070951101d40d0711903181100102c00c00c946500c10610b00703202c40d5030300351480c034184000d101c0001004007035404400704500908035810b440041d90a003596540f81c900c00310710103420724036441c001003000a002c9405e08403034280f0020345134200e41c09424401916400301080019007903c0e9001d010340710342c0c8055104103500500143e81000107035402140340c28000b03400c06e00d09901c500c03443d03601c541d0354508000d5103100d50f1340c0c0310105900920b1181809000f09121184040c40c1d8070102e070300c0d80d010805654441080d10a45100a401800b44030b0051a000019400030f108801e00c0d13600b807150102d0800002c04104030021201d665090070146035895980c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 611301079 1250 611299829 611299831
    0x70327110405251e0e060711010e0a0902090907080613150515120c040f06120905010c020c0f0d020f15040321021506151e03010305151e01030b 63
    0x4148035810083c0714800c440958125101400c154464040340c00010114a00108460503801c0c2004800740d51101340e40e40321000c1c2c0398444c0e0083c40c184165115070005a0381450048603a0b6841100c408000401c05441c2d00100401d040030794907034070951038002013510070b0442558a150701035840c4102003000081580101350180f68000d00c4e0126503030fa100070580d1510110081050721000007103040c441e141c1e0100041d0056078181910740340c43e18040030741c2040802401503404004002c080e8944206442e000038000c41c4d005802002080300e030702030180d50340b400e1901e558042c103a1405011a03a15141d00d00a00031034001e00750f111151940750400050555239100400210003e00c00071012903802520015044940c0d1490780764040c0d88140640303010300c560307a64140303404450200b01c500e4807403890040032010560000f90f202c4070313800101e8071030404101c210408800b0120000051220000c6d60300f44490300400c2e03030325864851008410300415500500c466402e000c000420010b01604025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 611302329 1250 611301079 611301091
    0x180105151207090512030901051804020705010e031309090506010510110723240c03040b07111206040503090607020a09050711160608060d06020702030303070327110405 74
    0x28070744070318440342481c000c1003641c0020000c0c842c41018401410302070381c0d02e00c101d0983c0c8011800d00f41240c00003040351040c5108805032060044a184180d02d6603010390390f98981c000700900210761b00031001607907a00a0b400306c0c012050601c0000454074031138400c4040c180c1d0840064840c1c0c5c4e0800c070a104c050380c8a10004410080c403131200300808a0244640c1c0d02512001a5000340c030403080d261983c4c801242c0d00340502c107600076820741c00c94206540c00510b040d00c4041a00d40c40d030303a0a00b074081c114041c41c1c2c0011440080000c00c01d08208080a1820700030500326622006800c1d04011281d072540101c50080c026841000072607020b182810161900318401800c2c0d4034030356110000765054030416204040410381c02032525280789014801101201e50280742c8403541e5142c460001c041500162840f4059a06110041c1c00d220040d01150100c0d0b40107421250307a410003a800800426018821109080a1100c0e0034841d209101382c040f00c0c25006010003045601420400000703040240c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 611303579 1250 611302329 611302369
    0x10906020a11010e1f120b010c020d1b0e0108070b1606050a0b06040b0c0c03190f050f01110309010b09040b070e0a0510030903080609010605031f0f0f0602010b180105 73
    0x1c0d040195600751164199030291000100e86001805c0058022035800300140205800c000c001c1101e41d0b0700c421a145002d40440c1ca540060000c1d0a0604000c10000d00c03c00582d441c0a4001c21142c2d0301030381150481da20142140c988641e650310140f034078040c1e52004003070441d00350071000114455170895a04100700c1039000403024501800680300707601c1540030300741c202008161410402014000000c40040a4024150b50300e42072040e2031005140882c0200148228400b0100b8840200b000c81200c2c40c20a00801c6412020840031810f03400c01c0790102180d600b04000c0c070304d1904280c441d081c000c9600040b082c0d5540c50f119002d031114401e4109040d00003070300351000240c642c1c82d08803000045e40300d914001031412031801c0040403080001d081500401c00e020040140540c000d040300d0f800803911302280200b1600941d01b440e1100c0316400102201f80b01d207804580c01800414000c211035954008200f040405024814a594640c40501003151020010492420048030505c90406100342d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 611304829 1250 611303579 611303597
    0x2c12030c2a10080a0b150a0f020c100e0a08010903080c0901020f12031b09100e01020a0606260607080a0b01090503010f090c080a08030604020a140a021605010906020a1101 75
    0x1c0403600c2c0c0d2219041c09400540c0d14810b10400544c184103907850103c1c2035031091515880c0d60401c0d5034038030442c42403900704609070900102851003440401c00c032100060007a00c000c42ca03080e005000c480900051072144060010001300840144120031140e130789600c80740004e80d100b2400300b4035a00302d949014158002e00700b4a007990b00081c08013144000c0d10b40ca04a40340d04003290001e42d504503a80e24055a01380410040340c547d0b444400c0d0b44103455861403c5100071101100403810954240e0f0000c10060400d6004a03628030640c2801e406220396039441d0203031154a50310b03036070741300c500f9145130000c20700c1e00c0086521441c06420010100606040050142d0b5503640800e08450342002d04001880c1c0e6038865208102d0301c0d4483e4001001203000400c03c1603819103c1140a2201500161240354001003418600740100308030b20706040d00144054035210040006910b41d0741c10100314580d00505000840c8941c041d00c0d01c1011341d1442ea0007004499581c1d51a8840e9802d051126414005280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 611306079 1250 611304829 611304913
    0x103050408040302181f06170a090f0b070807030606080609060105040f08030301080f01050c0a03090c12030c0501240603050c091513140609060a2c12030c 68
    0x140c07003c0144461000c21050303803138407040d07506060780c0700000745040c00c1c10001c04000300340c3e0003520340c602303078810154881d0980c5442e410800100041100104158084000d90040c0000310200f04d00c58022503c1c2c4682c2540c03940750480848546001d1400030418010114100b41050b0f0840f66204406040c080d18091701c4090b4400883c04030350000a080d880040180043780c014042034800a00d0100280710905200030070340e401e40034050202081542e0f420120041c010414500c0d40105511490011074490070b05000f014807021001c00d461640c00c01c96200004000f903112078445054250120308403904100c01240504000783c10304010700e1080c06185c0d1166a0101d124130649850104151303612003e01010002c001c203507004404010242044a03040e484420480d90100000c031030455880c08152070036901e0804201c00044103505484d2000b0261342c01038031a006202049801c10054485055800d54a2103180590381054202405410028410508405100c1110803071491112501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 611307329 1250 611306079 611306089
    0x50c27150c07180e1c1b03030c110610142b030f02010209010507080912070308041a190c02150703080a0e0102091f0c06090b010504050108030a0c020103050408040302 73
    0x1503030321640e15402ca180100b014400f120395a03051204451024444450040991a10381c0009000381e0485016000564011071060003400c0d0003804103042048500d00c141401001040c00d40007440114000044400d080e1500040684c400c91603111529821420810807030750700c00810f4650340e0010002c065018145000e21040f00c00b079820a180c544058400d802d00500540120b4109400d6910401582c40980d901c1001ca543c07175a0080030090390340901002144502140b14945007050146040200030446040018030071514240411400200c090010030070500c540401132040b60703a601c0300550740d6402915650a258002407614062098440d40c40c00030385d11141c82100019a203d0401400085501c507070056140401c008600f07180b59030012840045404d4500700348060590b031011000ea1080b495203070900c1d40f11000303205e0100b981c60211000d110038051540b055003007800104101d4000819206030288641c0c1e0442d0341c01043e00103500034240a041961000e00c00c1001102580300c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 611308579 1250 611307329 611307337
    0xa0314090109020301140f0c0a0c060f0f0f0b21030c030a08160e031f020d02040b0d0b0609010c1202030706020f03090c0a0b120603210a03050c2715 65
    0x400000802c01c8205441010f007141c2039002584a4050003070288028401c0301c0540c40d510800c41094140d89803442c0c182074503000540c00b0010000760411741021304408254102c1d2a80101e051011b0003100828840c09080e0b9a40500b0309420002400301c40020200c042d24555440c070701481542c0c030344584840710605651004000d00e000c10000024015003034452500c4d0700d04142d40e441d05035100e10320000004c7d220f80c0440c240c184c96086020303800d15007034001c1d81117a1910000d8141190b07602d076100070118107504421514003085140106d200202c0c2898000c031140a1340503943c1ca041080542c2d00c0c9401c041c0484086411440103201550006074244000c001141141109944901e07040c020706151105054400d03001c2c035480041017000300f215000f56222840c201890b41120f039500b101184c036010818401d01080c46000c1103400c1043d60020081212142c50794041c00556a40c044440b894440d50000c0c0c600301c06802d09582d1600c000700030484034001300426584401081c2030342c000ca1908 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 611309829 1250 611308579 611308591
    0x5150406031209050d0f0201050304020a080601080a050f0d050a0507060906020a090305010e070503100e0f100507090602060106200109020d110406050906060304022106010e06010f030b0d0201050a0314 88
    0x80c000440c00078054111003c00000c09045440402c20f95a90352160030051010100a040c860007001281c11544c17001c1e100d90142400c5c80480383e00350303501e1005981d80d07802400162020f01400144158000e80407801442030080c0340c80d10b034031b00800c2c070070211010703440800c060300e950740e551f146680003e0003400182001813081c0e8464100e076045040c16030840d000613181c405070703901000c0c00300b146803004103202e100d1141030440001d080d102c01032818140220304080f02c1c40c500602c01102c410700c00c603912a0340039090310365501c1580c0d0340300c01040c0c1e076916081c01544049210080ba4000104160030b00003010125040017145155455012801002d24820101d81d0078400780e642c1500e90a180c441c7c240281001c440c0702c81c60341001f4001c030f682884081e001901076101c0991007603844050f05205005203e454048030810340c0d6501c0381d80300391042035070b0081c0014600d544000d42140310340544050300c04018448038001025074019101680320941c0002416101c142c490340e400c1d80980a184146 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 611311079 1250 611309829 611309843
    0x2060c1203010f0605071a061306031a07090612022b06090513230708100207170703170a0e0d030b0a0e01180903030902060c1f060b0d0515040603 64
    0xd41800100b20303c0c80140d40060741001014080f03039001c150200d10b00045554401d40c03510082d203a41c0c020400b01391400000390551800e0090000400c03070520310000280c04080d8000721542c58610701242d100c1d0851151b4000500c1150241d59500443e5000f01000c100c0c82c007110290000c06a03640000b8880101201c43c055070310b01042081c0385580c01050350001d6001000d0540d0074070350340c80001d6030201e5074401b00b080f000400c080030844400c2100c1d01c00b8040041c00c4800300c81c120500a006075001500c2101c03034000c3c2c540341d008400380f035900b51015540d05032110a1070f12003030100f064045100a05214125890b0103070b02001450a001c0045030840c07517a8007090032601101030026280f02d907400401421024001005614426854585607120410300803a41415a0500314041c0101d101c0c069030180e0002414010312200003110030301c8640800003129140403186070b00f801c0741e10501ca0007070700c8030781005140a543c1103a07000540c012011098019090304440104085594940040b0384d85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 611312329 1250 611311079 611311081
    0xb180705130509011707090b03070308160b240d0305121f0602070f1a040e0907050901150f0e1c050a0506090114130f03120e06070f0e0a050a030f02060c1203 69
    0x1709400340b0080b805041c9503170f800e01c2010160000f0030b903900c034144005400c250000c50a0300c00601c9000e01c00a03116004440c44c0702c9030400300c1e80341c40c030807201081c40c440000b0255040c4800c0e0403d404814005038243c1c6945042081e018928500003100410032440c095607900c0c48a000310b403803a510009405642c1c014484541010841880300700c2a401003411a119400c445258081d51400c8409550140001100a480e250307012072514000e600a164030410540c008a1061025030b9800c99942180c0d60b40d0720080d0000506440384030340325005030340122094903000a4112842503580c1003c1c0700354101c68070885552a05820407000f80d950998594440c041d81d14980b543c81100d54000d0302d0480c03c50000005681c980b44426189040101031145020343c0310110308a82e4032450f800340d03000054421500c0c000f1001000c100c0c0d9051300101182040a03040b146080140e0040c0a880c0d01401c0e80f4119420b58440504e20811441c0480c0d01100030411261030389014001c0341098003102a00d2910303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 611313579 1250 611312329 611312369
    0x6090d0c060807110114180708071401080a090c140607060e0106030b100e040b0a02190e0103060b09030c12030c10050405190b0a1a060a0806040b18070513050901 71
    0x110300460910001d581e040040c544008000d00071b5298000d0011541c10711100448180799040c442e05034403854180c0500c0d040000e0440c00e07030354902c10b140b01c06d0342d80e5200d980d51031141c842198800d00000d0510111400148400e010300c1107111486640107098030b08000c607554460341580c0244508180301e035100c860400410101c01c86007504503010040d5000c07101e00305502c00c0010b47e001400904811560000302d15a50300c0c03a0304480c0022418540d0b076002d540c51000c041c02210b02669082d0000e071410ba000568040340c031040d61499100100035110103042c603003c11030b04212580c800344941c0001c10804000719403c10042c0701010444001040c14070301420130307034148007100d44202c840d81c1550500781c0010b0034035031001303900000d4008000354888080c0c0e0400304102000725510340042c8006580c5401c1500160001e02ca030100311414090390300044c092160301c4641d00802503d02c0c2ca007002242940380900050580da41c040c20802e440b4035030f21000200c2a584c20303400380182c82ea8228401b18 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 611314829 1250 611313579 611313587
    0x4050330030103030c12171e0a0e07030807081228053102101107090c020309060d0f0515030606030703050d051308071e1202010e06090d0c060807 64
    0x410041411a00e60070740d0301d107032405040c401564200502c031070032a00200d80814001c0b14071f40c2a0301008801506646070004002400d40c40868454036030061b0314000071100e82c42c500621941200041c01303809a035145a5600945070001c5004442d80941404100580000240351511550200e210700c5894102480c12844224411480e546140d05003000c0124582d0640e0091030000d0326028100c0d00001640651203c00780c4c3d04d00e0080d03101d01c54400c01408283d00c070000e030503035216101c03d40b1080307580e81d0f0f40030f41140c101e2001003015810a00102400786020303c00f80078011003802001c074603d0140004041129000ca450840d05541e840040c80c0394101001465400340c800d60044c082c441c1186c032407075a01c0408541980c1003110004003218044003071071800c070080219404441c50292035801c01d0120050a01c0b00c490900d0300084001001d24048141210940d01a169604034801541c14401c1c80d902020f6803503003050010410300000391505c0f0008005021647d500c0f840c0d410083c0f8024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 611316079 1250 611314829 611314903
    0x90c0221030106050f09061e04091113060807020f0a0803040309170a0b061203070f0203150c04061815020d03060506120a0207020409020d050304050a06030c020c0d03020102040503 79
    0x5082841840148903c40c2c0240840c0e040d410f01201c2141c0742d04007440010700600c40c0007041c8100c1542010641080b60302000a007041e2103901009000f0000c0c1c04040980d03c1c040d88401c802074140040003040b075980030720000350704600c0e03d206032610804d5620545140c01680c10084a1940b000020801411b42c8034401002401501041903d011104c0700c050340d99100a42009d0554100140868101d94506800860304000c1405480d11415107007800c1b1030101c10320034142e011303004425210a804500c41c8030340b0f1043d0074404c0c940d402d142c101081129000e20400780c1c086032060320407011401840c141d501c408103410942c002c0980355503a45c1e004040e03070b080ba805680100814401c84880440710742010342d00040c100f1005886140034000a07019143c0c900b0003a4002c406d480c07030641072080120040c070a503002940d400980d40ea50b0b0204804603548400d2b5075006812400301d00401d442c0004c58124124000d20000d41025140c100090508017014001c3d10b4002e034008440c01403a43d005a00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 611317329 1250 611316079 611316133
    0x21b0a0f08070305060f1e060316090605040608010c050a030e07051503070e0a080a0611041d010306051e07050904060b03132109051306092d060b0919090c02 69
    0x8400c2c50401c0c0c941d02c41660202881d4292087d9100c00140f19911700704000000f012441c3d01c001c405550f00c0b05060010700140c06800c2c019410294082842001401070b004003030704c41c3d600d07180340c241203010440c010b186000d0280300070300558000054903504c11003690011004881500c0e606d0801120207080889a904000d008807030a0004000208000c40d00100e441e80140000ca52054081c3c159002ca10854200c000d02c0c00350011401041c1a507501624140c0744160010007036902ca0007000001c20103500341310410017104a0000710918840c030003400098074094004125951583c800c3e11054008440c159038400100b407000c0f05008488a00258241075011845103252081d18000c0c40c1101d03902402e0300600c44500030f032a00030b8056105c4002810301070820402921150480f00060f003911126000c3c03c2080031044645c090544036440c119018410068600b1903c1c00034440c040100400405c0341c0d044250000401d080076001c0c0c1c1a5410040d40548403a105201e503480500710ba6181c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 611318579 1250 611317329 611317351
    0x301090b0a0b0907090603020c030d06090c09090b09070c062a0212031009090201170a06030308010801020a080f090307050f0a0201030e030a05030c1b010c0315060e01021b0a0f0807030506 82
    0x1d0010445c1c01c8074003141520340c00d1601683e61540340700340600d90b116200824021528140307001912002e07561014114114599a0100c0503075541d883e04150b0b01200401c1d0f07804503030303000420105400380c0749400581c2c1c4146404141c84001820328040c00f5118000000d48040507905d15000c1c41d4103101c940c3c40c1c4802c3d14850303410750500410300740c044c481c1d9004440030591f54511400a583c09640000200700030034405402070725013108c0001c0070b0141c80c0304c02c8002ca00d5900008c12500018001d03616490801d641e601700e0381d901c8540341c21380500c000d0106c80060108000314400708100780988912010303004000e100324609440014100c071220608200650028040001e8465100049a400c54580c5883c4c0380c40c0c51440c44018910003402610703007050b41c0b03002407074100380d038264200c1885004e040c2c6248120302d50700d140c02d9031a00c035040705050041e040354078001b0a0802e10b0307800010700d00300070f0030101c00251180a4051500340c160007401d01e0380c0c00128100304009041205560090344602 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 611319829 1250 611318579 611318581
    0xc0b04062c1005040203071205010e1006140d020112020705070503060a020307021e01060f17010608060108030906030a0912021b1807030203090c0301021306181a07110301090b0a0b09 80
    0x54584a429540b0110242511440401d0641d902000740001a00000c1c1244003680c2d80e80ca00070f402002c00740144209402900310b4100ca401203841b03800210713034006911003540e07440c102c1046003150004008074103000c3c440c4940700f04281c3e1031000d48002841003000f816654100010503103404801003010f60043d004000b0000101e501007000b5804841e035109a401c0e9200c43c46005001d019143c11005180908585c001001c500e580c0001d03107444e4420340200b0030b26807101348883c1c0b1030009000d01500350b881088108224100341008650041a0385000251051030b50346250190716108419001603000342c6c0c000365540c8020b20100c842d0130b0100c6a00c46424211007102c034113841c0041100081c550302000003590814140840300d01640d000b0002c641d10500301d605084100c1e01c0d801402d0001e2500103840d04504047d00c0741c90156001880c00d419041402c1800c024103600065080303c984d02240c0884009460034080c000c506413042d410200a031800048410494907820300852150441074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 611321079 1250 611319829 611319911
    0x40305070e0a0b100e011b0c050d080702100306030201110c1f05130806101a0702151303030c14032106030c060c06070810060e010f0c0b0406 62
    0x20003904562040240480c1952040c001e02c000b03104031644681c000800b102d43d00000b40e40165181e42045007600e1318030402118494540c01c1c1c69140c54000e02107007104038244000e140400303207480102c0c8903001c030f20302c0c280300396000c105140304407611440030940305e80b014011981c00c202101c04074034400d0700400f000b01e07884000031002c1c0340301c001d18001c8490300721032071f50a10700c242c0458880c802850700071030f241a40c41103401c1e40e8810440b1140383c503015003007010600c3c1c04e6845600e540500c40c002090f041840326000c100403590b40ca0a40109680300300031102c508454a802c10004600036203c0c3c0c1040542c60600d41016060035800c800d283d0803c1050005102c2d005141e8414442041c404000650382d01d80800d1514a540a403903030700c40e0010520300e60101000135024410952903403145a180ca45a407600d0007a1a107008080100e0004001e0031000d52103281c0c01c101c04202850003481c2c140b40c5e600d0b01e10002105641c113407a0036448000c1e480880e091990200d81400c03002520064240c400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 611322329 1250 611321079 611321083
    0xc0c03070614090108040c0e1e0c0408070b09062a0c183913060201060315020a0509060c0d0206091609050a0632010c0312052505090a0506040305 64
    0x322042a041c403d00c003001c213080c010b41047c49001303880101946212814030403d03644088400d206031450502c08100005c03003d00c0b2244c140d4040b20720b400003c0c0b900b00d0600d810f016140e00103440c03045e0030002c18031480d103000341c0c4150804a4400d008080b00c90901d068940542061410301401d4020b00140349216429944403106039801030411619612903029010810002010b00798100066801c0640b02d20540e54810010818280041c40301d400c030598800c416801d8403210320024003040d2820245c190803070007680007055101c3c29490500d2a00501c0800580c0923081520019059486120707019001501041000d81044624000b0503560903202d20090031240f0501400204035254404610401c8807a004880031f0003c4420740148084580240410840c02c02c3c10451780c440320000c00c801c10350081d091400000c0d00b42e0f89a1091004041a2801812016040c2422a4400301d8001603040d85170b4441c0001401c5642c0d5640d5402e0040104001d400f180d4102600c42c0c04200400c00002e480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 611323579 1250 611322329 611322337
    0x60b03060f03010912020d0e0f0906090a06120b01091508030301170c041d0601090b010806010806030c0a06050a110f100c0903080d020301031a041203110c030c0c03070614 75
    0xc00c4420040281042000c41c0c050500918020300111500382d017030a805401094020040405595142032095000b0800c9040e4a50882a94028041034042940c50502d41740460740010785050100380d541da2064030941c402014007050361043e005000506c1a51454040c00e000c2010f08400f01c0895814070943e00c8d100e100600c130382c1500986086490003000b205005801d01c00030014800c01404a1440107851807004d00d08500c8000d0045a0000c036450115101c3e0000005040c6c1d40c2903031a65500c0019201100043d000951600c036003070f24001e495880b0700000010b404161b0351a92201e02404018080c07841c00042c21000d07411442e4129504000003a615104c40405500452100d03a0203200383e50500c05038001400450740051591000304844e0010350480f8032802031003c1d2200c2000a00d01400300079900280507041401d0a03042c0d02e0312031740056480c06290841d00e80703403147c6000d42038655407042058200503002101010704a10302440084002c0c60035061038041d00c0c5a040b805021441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 611324829 1250 611323579 611323591
    0x10e0103061d1b4e0a031409040f0b0307050a0602120a0e03070303053412030b030d02010f0c140a1b0c08031e0412080c032a10060b03 59
    0x803030f0300f110311101c0e078903c3c40c400050582010203da183c50410750306401ca4108540315003200c1303a071000102c1c030700c070440c07605845030040c11000d400c642440b964122114880c04801051010050200116a44d1140704044941c0b4042e50b0014041000d84181410440300da81310034401d28201108001e07954000c1551504005004200b581c0c8031820441564080c001e80d0f901a018851403070088109500140103191041c2140444c140541c1120705c1540c00140112a554010000041020024000410b40004400603040c085503006c503010100c0c1c64007401c1d009c13440040c0e44036100308074882d01d640b140d640300e01e0307841c078040c0300c600e19140f001d4030f142c454082d03a4000c01c60038080080340c14058032130000c48207921070181d0030401d2f03444424540c0c1c0d8000764100180100380414466103c40140100c400b00c484080700c880302111683c4070b0600c2900814081c240d103000c100b015041103200810450009201c05480a41e40c0301030041061500c2d1807651098062460300c001407000030005130659074050303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 611326079 1250 611324829 611324863
    0x41503020c0a240e07360f02090a09050705070305070615060807020d0206041212060504020304061e0e03040e060d021905130b1513080303010e0103061d 67
    0x1a0400c40103458541260005002c000124406940c0d071040c24030b00103180e03041a0401c0c006810312200054a822843c4204500b0211a001510784081c05011140306c00c032013007007090f0000300d1040142040e280080f01a40241d94005007080b050702d07200c501c0d840500301c010340401907441c2901000d003d52044010280a00002023517400c00c000b01900100e0b40000c1590b140c4c000a40d48840160942000b51024005401400c2c691040341d8400901248100d0b000007501c29880c8070034070306a5451a61080b8804000e0319000c0105041d2114002540a00e02c030b004000341034003140360301c403420750207001d018a04641851104030016000109803800d8458481a0b804a501c030070002445481c001c010003034000a41400c100420565050b14008035641502c100200013030202c40308040703a10201c100f41e800301024840640340c0403144050031901c2d0241450910b0143c96191592440d00268410706a00c283c540041c000c004d654001c1e940703070a40805201c03140180d0002c1458481416180d500c0e03240d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 611327329 1250 611326079 611326087
    0x9030b011403071505072f041d011d0c240d0609050f0f0106050903060f130c0f0f0e06100e0102100c0201090512070507230402040b0d1104150302 64
    0x2555090084000920300d40b9130441c0304d00c1c1c5801c800780582e04a288252940300c98010000700000d00c1a0b041c81c40e4000e03600e2401c0b203038034440c410003008140d906281c85180f000d02034600d4003a0b000340300f018824000074182c0d0014003601d0603001c0c80c0c883d004041d2801240c088018000100922003a4111030300543c480d180c0300c19401403210000d0030150301c10012142070005001720482c4408405004900180030100c0983c3c82c0d00054415100318042c0d0354040d482003002a81d00599040c120381c10403210500300320030714101d4031042c0e01e121305a0003001d407200150341c0402000498030203030030040c240b1150a0714140f03801d02c0010480d0240300c203210140070a04c0303207500403a0701c01c1c084c03c0000e00d5401020000503600c5d0360024020485064219418480d4582da6003042003a1400d550300164000c00502d0060300703104180c500d0703011580c107010b401e03028030b442403101d81d45500180c40982960a07002c0d0b25031300c0040116003079480514010696403003c000920200c420440441d400c0b2146050140ea6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 611328579 1250 611327329 611327369
    0x51803030a020d09080a0804050c120a030e0301110319050702070506042916171206100c0204050406020c1c12021303060c05041d01150813052b09030b01 67
    0xa00411318008112002c00100036010315004020203025501038821119000400010b0104160800166040a41c090750703249001034420410400c413200c010b030010600c850781ca03001e0b28094000340d0700b0f001020025942a12082413500c19a507004084c2d200a2003d6407400c8003017141841030b401404d4481701d14400c1c40b1421045800c0e039540c0b00019207a241d544804030080701e4905145c0620071991143d0f110324240001992005440d40900351030720a44864850400f00003120b50a007054005001007400010090ba6440c412203120b240541d101503980c1c02503000f101e0a03e64903106116030524840e0004111503803280f8959920214010b00680d64484200700c2038140d4955400181090f04010b00000c002d40d006018000312101c03030070003900344941504d040071518400d0143c1d021403480c400c04200a60301c00c40056400c030b000d05160000d0b44c03045803a070034100f8917001c103c14403031205070034201c1040c0420300821400303400d070b072404003125421513a6040851006204260000f4040c10803100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 611329829 1250 611328579 611328581
    0xd0e1603030836010b1203030606031303020f06090706090e28090212070303090e01080606012006072001060b04050d060608030c010b01092301030c180f0504051803030a020d 76
    0x90800c49100c502c3c1d4104111510240603040711a0381500440c0007098000400700d000094078040c02c8000c14807411595035880d8241c40c601d00b18800d40440c0300d5900000300d110000d0112138021b58089019120032070a0580c003400345025a841201d411220740200241c0592914000d030860380c80701e110408114000d082940503002032103002e903200e101d0140400c9515400501001220322949411444958901c1102c460740d000b4425156a5000325000a40340d40c442d4040c494910801a641500103880701c0c5201d28029003110400003017868549890900210342255640c0c80c00c0341c00c0240201400c12503264000c0c02203100c0c01d4010242004640204010382e000f1001070009041240d485156880060380a050100d1586002c100503040109800c0c2042e10f0000303542d146200c8611207404900011802008400c06020810181901800f908050001100f00a024030501d000c881418401040202e4801802101c40d43c620a141c501c17103800003100f5254807036075291700103882e030304100d140074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 611330935 1106 611329829 611329891
    0x3081611132319020706090c0e0402240706150306050708011806060f051e0307050d050a02030709030b0705120f091006030b0c09040e030d0e16030308 66
    0x20002403d5034004220440c46200002401c0401c1d45500709100003a0300012500d080c040180030039841c0540c4001e40da0ba054074000c1c84800d03003410182d40c091168210007015607444541d924400d5040100c0e00006540047c811b000074900170703000804c5048240034440c9100c05521032481c1c03106a03032007002c00340d0f041c030b17142c00c048101c60001c103131840e1b000013038503c00766518401d125000032010f0000d58000c400c00e40b038958440c1504e9503e8010354a0052400282c80d1041c0100811240d101ea10325040300d4000a4000c859242e1240466541c0f0a21003100c2042c86c000050006a42c4400d450620603555071043d50304191401020307600350b822611015003c0060300d0080707600500004014601b00200400024070401000d00480c10750304100846c031445c5a840480c250008424064480781c00703c941d100c08095411941c001d003000703401031b00b480c0c2c08001080c03072401120078002c120 = true := by decide +kernel

theorem cover : BRFrame.Cov 611151079 611330935 := by
  have h0 := BRFrame.cov_init 611151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 611151079 ≤ n) (h2 : n < 611330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
