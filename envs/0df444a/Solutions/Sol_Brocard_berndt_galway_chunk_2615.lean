-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2615
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:13:50.541237+00:00
-- url     : https://prove2.me/submissions/c57fd97e-6699-4215-b9a6-e8c551bacafb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 470143884 ≤ n < 470323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 470145134 1250 470143884 470143889
    0xd0f1b03020a0b01080106030305090907020f120919032310061401031a100e060f07050610121502091f081815040b0403030207050f0609150c03070f0306 67
    0x5a64002648528000b03442c0d21000e20141c40d1600340200118031901c040c0f10707040840b0342c50b13190280303004400001c6c0300622a0081c000d40c00d42c0100c0d01301540100d0103015507451015070360302083e505e1007104c00f049100c07440d660541e00040c40c01c080c20b10000708004000c004c102111b0701142007422000e0103062411340e09100411000382130010024031b2a10303e142003280c00c036007620301340448030824036105040c43d100e0004a5000d80c03202c100003241e42c01155454442040a84031038508040c14040f1840313a44a00c0003111190700c46400c101645800003c1c0c0009000f08045094908030fa5854415103200381c400d00d5814140c0c0020045e070580e03a150001d0100a010994101e0904d284000107000c0341c000702c03500751007045540f8003522001004500c0c42010010081000400e07110307510ba85021603070050007202419800c006010204000304010840c80d800e210080c4100e00d030900c0580d091002d1440e48a110b651120b00b4801d41d212240c007500d40c0300001e4500801c46c042009000c60160103a603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 470146384 1250 470145134 470145167
    0xf12170c07050a090509070b2515021206040606080603070e060105040f080f010b011b060b06121303110606180910050115022803050304050f01020d02070204050f090d0f 74
    0x1003c0090890445d4010501c243c1c0e034541a0f650960b41c601600a880c46100a1b1400301103010340c01001c0c0900070b01000040da80595003041c0320041d80701405d0200d0703100001c0c00112002e460100502ea180500845001d8441403030010101d080ca100426a100c40328044e188000c4090340000e40c45911410a40f80103200321201081c101d80d030742600e562140c5200d41c2000e120350a14480b12040d502039130341441800651030403603400c00000d03100e05004140c0980000d40c4400c0410000d101d00c080000d1b814000c201c04031122045407010314018003403100f124503921298101c10200714155940700ca00401c900004180641c06070303101d43c4500c1c20300c28001032121002d85400b001180004000400e603400c50425001c44070010340c441d002088a06544910001011b1780040f584000303841a00030b07507040343c4624111620001c0224007a0b0aa82101c554200c0b215404501242545014010710390001010745030f16207282450741d04180c881c140c0e88480707002d001c0300d62414804107104000510b610b0000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 470147634 1250 470146384 470146399
    0x30305030c1803150a0b1012020c0307050f06070807030605060412060e010507020c030c0405010f05040b010c0b040303050709051206010504020c0f0601030b011707140415050301150f12170c0705 85
    0x1001c0e1007613000400e40d40200c3e000e20f0029415000d0422440e20307016000c0c2c0b9124000d910714005000006507002800000351400301f4003100000440c1000307201001100704000c1e202c82d16040c5001005018000c04030300070181003d03010403850f11140101da064514200c2ca40401c2c0d0361324100040580b03041004480c1075840c150820009a0b0f0202c1c070305002c510114203440314840e0140c01c01003511800c0c0103212800070f000a0400980c81c081e07002c04d2a411040c104507003619102d882c1d401c0c0b240d408aa050380803c1d221000c018243e039001c2884005841c0c2110032095215a00058a82c1c43c541401000d020366400038900b00c04420400c5600d10602414007114031702d68582c5411410f814007849200f40180d00205008824840414114159800c0314182070400e900502000050480543c0710800c1109080000c00c0c0d0f600e003802214400e10482170600342207480d00c050142a040075a10800703000214460080004042044d100382040d003c00c0c0c40390700d81c3d02d81100365003801c54070307800680d0213a00e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 470148884 1250 470147634 470147653
    0xb070201031e0501060f0f08160e0d0c060212070f03180b160605060405041e150615171006030506041103130309060309030c0303020a14210a06030305030c1803 70
    0xc8030f80007141aa40990394001410340403503005e881d02c8400e14416008500340100285101140044c00d0131412418a00482e4004249002c03403203001201750b06845400010405021640d0104622542120040540e600d420590744684180c01010f6400804001003540d46008070380c810050f84010301810042d80e5511710000786401810f0b4203503041218120304001c0000c52902c0d1902c1606d02c500e820560300e46002c040030100140040300c0240c11103101c40007882000c0d03c0d40082c0b140c4005810000f00c071000301d2019941c040c02401c103c071190a41e0190000c200120009105d0000c1c00b00e07902c9082c0480c05446200029010740303003000c6201042040030003041030900c00241351b498518003e4540002d250f4803040c048040e181071600180c045003840c1c040c1d60001e07101c1d81c020040c0c9000362600c6000c07040f01000d107140300ea100c1300800201046016070030321b4000c0c1d04151543c0100c4078410030891185141e4000c0e0031030000038030359046044d0100e85110038070020104c410800f00e0040a807030f148030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 470150134 1250 470148884 470148941
    0x30f080603010f020f0d11040b040308160c0f030302060a11161a0403020a140f1b04090507080c03010c02070503061501090b13031703040b0c030601030608070f080c0303040f0b07020103 81
    0x1000304621111240c10601282481d2611500300d1b41a0b882e40764109c0e25050450b02c2d904503d81c400036009001c4904060403502052044e61349070068695105000ca4070761950500030310303054001d003000031000c3c070f4501c18069184144040342d01c5121110181c003031954042c20403c040364286600148c0d4506038800700801c05a01042090034117104201801d21203e540c2541640e400340118020119801448541030080181403180a01000108003082e0120242e071064100002540600c0c415440700c0c0304000c45260a00a42e603140c01540300030701000703107002c00103682c420004c0d01c110381592080c560411280d00c03404480b000b400c05152010395a10300e1000c40a8820340c00e00c804d556042140c2d00802c0703907407400002c1740e0285402c00e00c1c03803e040e04c42605110385503201801a03030605a0b101400100c08034144036500060601c401c550030030394504a0300a0400c03d2000c0060f01c41c0d0010041440400d10400c1f114064800707807004680c0300e20082c0f0050b0002c05099010800344110b9501182190 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 470151384 1250 470150134 470150137
    0x1e05061c12090f03061506021605130b0409061a0f090411011419180308071b050a08030d0b010207050d0b04060623100206010b091c06020a080f0601020604030f080603010f020f 77
    0x100052071b20f004540e01c11003242c031a60400540381800c040c0c207400f0000c920f8002400010703e001e00303d0000382c0250b000006800c032180d83c401111290b17103e68610404211201011140300001e441e01354100548030b0000c0c1c00002c00400080c50310110301c0c41c44a180e441850b02d048881c80300100c0c40da488011414007907070682c031407403400002580c051020000722071030042d210403280e00000543c207145090b80e40c00108802d1529981d650341e01c0d600c0000e183d036102c0100c60001c10450380503590b205580c0300c8540035944418221750565010441c10480354480c03280040c1c0d01500030904502d242c80307614111000d424294850615503121030700d0f00e800b00806074403c88290000300d5040800d114003030403da840306801d00c260030901005216003402800c00c580d41c0303d403c0c1e402054a10401d1050356a0100b2600301d1905500060404030403c240803044000c05500040e0900080115182550b8020b2410821302407400402900c0e40101d0402d840941000a10000450042d9118200b00041e180c15 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 470152634 1250 470151384 470151401
    0x9010b390304170706050a051204021203040b0a09050d050d0c061506050901032a0c03110d080f0a0615050a020a0507180c030b06090402090a091e05061c12090f0306 72
    0x3c80c0038a8400040705d41c095402c5600d0001540c842030300341042e1014400d08207000404c241e80007031003103441e042e00e044148001c2c03015040c0404010b03296140318400620a140540009000d00c0708400d1440c00f107400041d2030210000036180c04950700d020780c901000130300701200c080486010411301c00310382c558000c405003103640c1080ea010840200b00e800441644d03e40a08481007070540000350750490340c1300301502a28540a82845804c401c24920428a440b20007a8a4030001c2c004d07105100600c0d20756518070f500001d9001d014016a03007002039100d03c0182c00054841072140000711102d42c03a000380240c1401c10307004010f07902c8141d41d400c2058200c00e880010a2030300d5140900c1c036a907003806803045c1202d55101030800b90400f0501d405000c0254080b4070a668003210006000402c85118001c001c402c40025965040c04541160340400b030301c07000b07484140b01c3c100095840103484400c1200e0080d41d50828101c505585001c50240e0340f0080a030841c102d80c0c0300c01d40740401804071603080301d00c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 470153884 1250 470152634 470152679
    0xc060105010807020606010806060f040305120d0b0901030809061c050a240e0621161a07080d09060e0316110306060108010b0c0c061809010b390304 65
    0x10320b550340700c4102c3c5c030340800310307100703030215102c400030500a0a1003c0601412400d44c03805a20f095201d4880790700c0d0130000c00061409400003c0e1a01e881e58845c09041480c10041d07070302c03103055415076491001c14000c0355010380c05440302103000c076001c20010061280c0c10312900800c024505080c3e00711340191448018105c122011031407000317912030b05c42c120142140c500090304070060b10b418041040c4448840d80402103400740c08141a0f0b41e07001400032018a049030241000d07014038003501030320100c1803030b600400c000c24188122804501c030300007100e189200406002491100d9031805c1002009010091b422500c0082003100c1030038941e004050751107028002c00c00c0d014801c50209a0390b028102d50707031350016400d5030040201010500107041500a501c0583e040080c0110204015800c414a5041c02c075030744580440036814810140c5015240c203000803444c2c064910990b203160301c500300901000080c40e040003021510304a200f01c541c09070400070340741e42d9940e4031400c650310120500c800c0c0c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 470155134 1250 470153884 470153897
    0x41503270303020d240302040509011b020a03090608070c031803080301060c0605010504063210050316080411011d040f0b03070602010e070e0408070501090b1801060506190c080c06010501 82
    0x1644000004405c42c4510040014120118115400e200161030301030401805903490f02c1c44100c45040400020407030110030340c010328400c0020305005000c001c4907400801030145030418020302a03405004c030011290141420204114409058060103c1550018119660200001c9030056002da004007e83c0c0c0680e109001d5a40c9070780800c4100c80c0f5510a00307101c002014003c0809030304105640484070b80481e48009024070a00c08644071449094168000400000c104100b08800351125410801140341464071b0785050340e15091080c4000f501d89051003560310100c01010000d00110400c0300e8090000c1c0300d04c0a40709482c81c00b030714017103408500ca03016121012605510500ca00c42817a2440d1000380000d91501149519001020700144e441c81c0c0200308a01c0071503401d000d80030016205003402c0043e0701e460b0f002006d540b00c001501c001e03540d0500da01009590356410a90f98500c1540c0c051500144014809840801a942d40100003080101e02c02c4014100801e100f4102c800070380307842 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 470156384 1250 470155134 470155151
    0xb01090b031005011808060403050d0f090f150e0102040b0a141c0903050904051602060c0a050d0e0304120302060a1103010e0a1d151506041503270303020d 68
    0x112214001150b14000c1a141500b042016601c500d00041c0d40d0f80103035841d0100242c580e4042814540c089078150003140000861900211107072045818140140c0010040d0079429961243d9100c0b1038040a4110141504c0e4090603a00c5a0311401d008500c49000f1951255205400900b5400c1840d00002203441400e050f400b1101c020129018500c0210306216000c09200b4510001c4c070180d0b009400b000340c1404050100d403903034402c4078018000c03820b021941031004800285414001441140c4070303102449905865504102980c0d020a81200c01244026203076100d280b660141780e119031017a10b62440007105044c1c000c82d585014802c00d40c4180700e0390301c108541903000e01c808e2044030034403000080000c46c80c0c40294407040c20078080030100c801c2171200400c41485e1800c09245082c40d001c8070424030800404a00880b444031909807041ca040924007040d20500400340d90f00c5000b407548423140c52140e05001c0c8113a656003481a02103e200042a007001002904404400f162051401551 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 470157634 1250 470156384 470156399
    0x703020d091b15140d060f030b0921090f041808120c0307120903090b041805090c03061605041a0a0201050703090b070c0c05060a05301303021e010b0109 67
    0xb0480d90080781d180c010000ca084c00500641e076100055540c00203940e44400714101e255051203100450050a034920309003055402d490400014803012030b100340c04d50054485140c200c00a035131701500c3c02c07158010f8050300e0102150103000c84030311084d9100e1044103101c04011125015103030101e03041d240700351a90f4445058401c2c1c0c0c40150303511000700d200070b214040000f00541054054900c43e252040041703994003a6100d0940064100c2c1e000000680c10200b060540d9119003a031016038a40202440c081103408030303441d40400b0785108200c0403201400d0211038018000c68000b80f082c0c0c0040c200c4180c800c440f452498002000250055080c500800c103014400d0044141c0d40742c00c60800c076855207448205607014525000112080320986000180a0356000003030041c11000c3e80315203030fa0b0050620920003420480d0040d03031401800440300b070303a105d5550017003550100c0d11351101c8182d5100f608040c0e14203054400d40c0421840703200100010840c041d001504445001e07207e0001c81d0b41c66819 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 470158884 1250 470157634 470157659
    0x901030305270a09051e01080f0d0215061908030307170106020a0201021b130f02070b01050108090c06090d02030a05071505071a180a0b0f0c03130b0703020d091b 71
    0x1640d550005505009100c40c625035031017150806441501300406030440c0c040c0c0e502c2d0040c01d0780000d10b941c02000140d0683c902c14841d89200f4400c42c406010010f0070040300003030061b009800c00340200d0841f010610000d42200c0200b02920041085948a00c3e181c1001058641402c2c1d01c2ca42c13204401c00000b5885000003101d010241c0d05070050030441c000d0742e131504031124400a01c5944020407074060141c000080c89603282d1000c50b2040580c2c0c50500c1d0401d0551280103901060401c0860790401c8090000071407500218002103440c540d0790841744000494481614601a5060180162160070070070005800c40c101c9039001c140282d24a917145040d5150300170400041d1803404034080c140b400c141505101a03002c03a0082a1182c1b01e038649180c0c07464011201002c44144d6429805c7c48020402026104d520001c00c000030f43c0b461822684100b4411500c110040c890008540411810ba02a4058459010700c091040009403403a0820006100214501140603030035001e011513800079080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 470160134 1250 470158884 470158957
    0x1415150901170a06050604170f03070c150c021c060501080d20030c0a120206060307050f0d0321091403070c0e04171602100c03020705010e0607020901030305 69
    0x854441c904080c55020590042d002801c0c000d80d1a581d070f80210f40c69840a01801c040e040e0407901000b03001c8a50003640c41c040248001c04c00f20f40c4180580c40c0010010b003113041c1510482041410380039492107041d80e101c40e095200942c42809a0b0310343e181c582c1b152400624650107000b052015903658100c55071680c021040820015201c408250703516843c0f00101203596503500f04403458400901c0c02d040c2440040f20080b112135480784802500b21381c2c1009441c0d0090801c4018204803840c0c034000503804200f48924038051444c00a514040c14020080c8480414030075003100243d4140368002030007401c1222048510034181d540f00182c0c81000010740d0102c50380503255400c02ca090803402d1384039000003001200c1c0c01c80326000031140800d0240103059403240504400803508014030402c00e401e00300b1a054002c1100b01c0200601103175000401404413070003801c003801c032003140c1d0010816038807401c54081d400100e4000000105607010004101e0180181d814015202040e40400078642100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 470161384 1250 470160134 470160137
    0x501050414280f1401120c11160801060b1c020c120409051005013f1103071b08030403180302120601030b0a060b0301090905011415150901 61
    0x30302040c8070100c1402580701030490010011040b0502805500e6402440310440314002d0100100030030009a0161418000e0100710000100c41c16041000030811040e582000161984850a01c1c456600800a54002c98506d10035181c103003420034124100340034603108045d10380d803a02c0b0300001da425000050b51260f41c0490300038400c0740c00f03c54440340a900070003a41c1c4164083e45040c1d0011400080c020700003460840f0000c1002c0c903045000c4007a000003580034030b06000c0140d800b0714640b69101e500b190000201000d0b0882e455400418015a140742c124031400c2501c0c18030328031141c0c0050005588100c0e10759641c164aa8101c1e942e07062144914000208050310600100300000d000c1e211802d03040340c603040311130f464642d00c0d0000356104540160b04007590300008014014040072284842d03201000650901c103452412110360545c0c441403041c50790155031381403000100242034000704e8580e101d4070100d804a0900d0311071000803519500c461407180c0c0e05041d0804a201e00801624102d0805 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 470162634 1250 470161384 470161387
    0x306030b010807120b070e090109060305010c0e0105030f15040e03090a09020a080f060105070605070507050c030601080a141501062a0812040507030212030a09140d1506050307090218040501050105 86
    0x55603209400c0c1d05d40540170a086c05045c01e00040b15840d2800d10310300a001151000c00c2031895400c040307084500c0d4100c81c008000c042031b604041c1e40d802104494000b802051102e1180d683c5468012141022801c05130b400b074148140319845410000241c410240b007100c640e80b9072a03440301c80394100e1040c214007070f012440355800189089641c08005601001c10304000780703081c0301581c4450807140204c170360001081e40803542e03900740801044800040041900240300d654101003a0075551840c010004080781041c0c1e54002c0f0004082c81004c040e9002940c116000b0b5842e0758000c1e040c9102626220201181c07440138859040c02d190440c8202c0b9009564213251411356450391010140040048d81c062203404d030f0004c0141c03107040c0900ca41103148000f03162640548500140120f22642c0061224000e102000c00183d0b180c1c02c1012090358400c1400c0e076003824641115000d0421070740030f40d52502840c0303000140b80390a5002011107020340103064100100c00300030007048034001c0c0106800140b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 470163884 1250 470162634 470162669
    0xf010f030b090c0301020720010311030c0702010c0b1305100507080109090f0215031e27070f08160b0a0f11030c0106031505091c051305060a0306030b010807 69
    0xd205445070b42107004030b4241c6105440800210f800da0b400310604403050700c41c0000e502554100e2460b003c400c02c40c03d00e0144011640908100e040d4000030301030081c40b500008040f021680900d007138001d6613030301404610b00340c50417a0a184003001d0b1403030203030750501400c4914042c0c00f119210b494030403031113600c6203455a401c1003540c50007400000c1d01102d100b0a200c11040250759444052004100481b0995039245400d00d017400b00c0c60000016590240000c1e010320540403208021040c400902c4541191040c1c1d0b80180c692401c0360079031040b1a1013003000c0b404118604040307100c40c0040001314690020b26504c0c24465414131820800034005805a0a04108940309400382c200e0700d40c4600459080c00c1c04031000358215840c5601c1101d9803450115001c01c40c107502e008041e40100688007a00c0e100022140144650b01c001d8185400c102000400c060015820052040544400390469480e1f00a40001400503c69800305840c0710080c0c0000146d80300000414005807003885456000a02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 470165134 1250 470163884 470163893
    0x905030a090e042d050303150411070f0f020a0b07060b030c09070f080a15140f0105030405060406180b040602090108010509060a05060705030c0f070f06170f0a0626060f010f03 77
    0x1c90811035006260303090b104c040811000c0002c0c500502c08030921094426925003080101c8041a00030054180207000017030105e490080900a03858204140d003014070300d00d10000d01a02d13031a401c404415880403c0c42818800e040e0311416a000301901240d0035220100100146031101700c80104c00039511036170b140641c500c6101b90a4200c40700601c04210a58046c1d003240c118040c640000014010b00300c5880614944500b00000f00c61080c02c0a91030340c04c103a1580e5072a024001d00180520342c548181d1005034044200c1c4814280c0c0103104062070341010b144c00c202943c4602031040c005140413001182c20f01c0d141d00c1440c01404000c1c0140a258a800140849034100341e07410b650a00050250251088040c00b1034022010f103c0c0240c00b000d07040c0841207143c4140c5800c910b0800c203941030302c00d04100c03046050540042082e0500c030116550f84500f0409041c1c20380000d0103060268907003200000c0c1c1c074038191f00c4070000c450030349285641e8414502c0280a091142407030886031401d0030004038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 470166384 1250 470165134 470165183
    0x209150a09090902130e100c020a0b0c0f0a110c0904081206090c090f0307050904030e100216330503100509160c050f030c0304030611190e03100905030a090e04 70
    0x307207200042d1522144a074080000f141c50718230a040160b0800703000340c0204001038082c0f80d0b110303100d0a1a64140b8400580e058201d00400d11300c4c02c14402d40790810209079104010f00422034100030000100351525142c08001908000080b0b01c82000c03000118640d403802004061003005c0310a130560030b0a01140070040c82d0802c1d192080c2c0c15001d008000300d02601c2d8a5000f5103e036000740c0b10310442d02c0b100824080c54405d9001c0d80c3d400c6411440c90034018541c3c1070725003400c564022040c3c404031907100702e45c94155198010510010340004900e6071225401c10080c0d44505400404104910b40c0c0700f0034446800801c4541034440080b141c04400c20900a11340b01c2041070044048034a00d0f104010310710319640c8405040d159a9001041c07c104100b06030041ca2440130b0b488030180d01380000002d00812411f0302c0a001c8007406420024480741f82c034100884040044211010300000e0700e24240580c603540420002400a040c07100041803985004500b140940e503c005001040c0c60030747e81d0750880 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 470167634 1250 470166384 470166401
    0x1020123130f0602030405150f0c0310091d100c050f16020d11040b040b1c03050904091109060102030f042309041b0503060603070b0d0209150a0909090213 68
    0xc40d41d15400d400496802d540c8841082c0c407804005a6904140c1032651600110310049040c00c99a4001c001c54600385086440c0c10003501030040d80c6079100d6003c40080c03c9000d421030011540b60140600e04140300039000c541b480200700554981c00d004402000030394013905010800302e9000c00c01e040e1a000350900807c84200f00c10380e10302145500b0f60014000c091150b40955a8880414418404e4a8a03209044007450125410020314807903502203440b2504c030340740303020b81e08541c07600c00c00034980200b0450b500c160005008010880702480c105200b0079441d01c17403034000d0100f400041c0c41c55000108441030840803014842c1014607048481514070700901d01d00071403070074008400000e5201c03440c00f14021031158018090841d0990845004210303d5840f01703102c2d038001d038144002501c0c089241d100341c80051820700e0b0b4403001c0f5413032000030344a41103140cac0e00031000c04403105011a0440151100c01c2140c4e0321880700c0e5a445c0d1001c42031f1900340c1406035000c01d00b065045948421039209007407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 470168884 1250 470167634 470167651
    0xc0b0705040b0412050a02030102120a060b040f05010503100503120a03140603030708160206040311030c15031303090f060207030506090a12050d151e0e0420011101061508010501020123 81
    0x1c40d606c99030100e403d9800411178503034205488014044c00030428061800070340074000a031400c244c07824a80385c24191240c480c103418424004081010042500001c1c1c0190101034216000940c030208031050315400f4000d030300300080c5011203c400d0407150b0241c8502a00c0020000c1d030400c07025031a00c201b298890900c5140322041d2480650040c0c4035200a00001c0d4094503110303203c06544020706051654035100349100e076140c0185414008810420759030444000848407020303800c0d91405586a081c1d581214440c00280d180025101c4e0740000c12070f0542e07204d0743c1a15040e0b16000c40d245d40d42c0750a4000182048001c04541c0c801030712580281c82e00342400e03240400d904405d400c0c258505905900b117101c0c0600000400008903c10038402c40013020384c56a9071045151a4a880103440010f240c60b0601842c6090311480c40d81c4144000440d01441c00002c0084a80d0742e12100204801d00f0f600e02e001c51a14000000c140d03006204184113000034803d0900c540e00c200140c0581034200400648 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 470170134 1250 470168884 470168893
    0x714071115131211060a1d0a031a150d03020606100912150c0203040506070f050a080f03090715170703061701060f0906030c06030203091005070c0b0705040b041205 72
    0x4019201c0003854002403543c245041e002c0007260400034403269201505600950040280350b08042e40050381c5006004507074602030b400d040e02400500304810a0380098800082c1801d80321804141d0010280100213504490710441c441d20700384140140046030240c00340c2c106c0c030001051030810320102c0016500d10302e401b1013115210706885600c40000c20069480030128055040400103074801c1c1000800d85000541c201441c2800240c403078404d02030010300f1000b020b6a880e040040822000e20182d40c040315154942c0c401c5000400a0b420403160049a4802c1080000e5000145400d9441d10316070b41e99031651913031310400740712161a0080c0c00f00b020181c3d1140e000810301002e0718140007000782c1c2d400109400380f410788100709640c07981d040145000c0ca40700c42040007951141c01e0200701c4030103050153322039444080311420031030350704110000c29052100f003005250784004095012403240380c2c280115156081c0458181c0913134041d10402c030b20200001d01c140741009a8412080f4030810845 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 470171384 1250 470170134 470170147
    0x50103120e04090c0608090601080f030403030e041808071208041a060d02060f0406090503030f040e0c1c091a0c0904110904020d05090d0f0e040b0f04050405060714071115 75
    0x301603440150320600c00101c01b101404411582441032900500c020401400510172030103a103607ca1040344002014044640c0c0120780540725900016002100c0300200306043d40941886000759002c08400c42d25040e0f8881c0105074a40940d88160040390000204800103280703c42c1c0344504a07001d0800d5500003c2c0501e0180142e50300002021010a44d90040c0e85651034404040d14046403504054429001401042d025080784000d80381180c817101140941521040c0c01c08020b4420320320f1508003880b04003041e08641050fa04030320b0043c2c0c0b003290103c0a13000c60207020021660140c4202d001e941003000b92405514060300072044180320803050a280103170202c009402c0360712000e80e1944541e01e44d402c00c0074883d004c0c45019400e000f98103250401041c140f000400c0c1a491540d03a0303108030340d114a020302c151904030070b80c43c01080192040010b821f003424050360b00d00f03003201c00030001340c505052040002415010f0380d081503445268ac9d80301000c1901000380c02c1b0f00c007032040c00e401d88041c05035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 470172634 1250 470171384 470171393
    0x170106090e03041701180206073201060905010305100c1b060c0809030a200c03011b090b0a020a121b0605040606090204051f0c0b011502060a0c0e01030c030e0f01020913050103120e0409 81
    0x111044005101c0c141840c1c2b205544c85003507031041e5002e00a42c42c50f200040011420110340f110442a080000080680c403d081c140d451b03907551000c00c5210444d9031110003c011032684201e410038206d071104042ca503200c0070b078140e0f2480740519480005078090b900ca4018a0b40a030701010880c00d10055520340881e00010030b084501c41422503540d10b1140d070030341c5850ba4000446101910301c50355902d00d031a01b503041c041e60313400460304000d100d2010184580b4045205042002e0400c029501007040c07a480e50401001528050f07400b502c0180c40e00b007000800411502c01c840031100003401400940e800e00540810f62000040e815060001d461480000207a540c44494040e00403869010205114403000a1400000800d03400c62103207803209185003241c00c80c000c1071803c0340034130340402c0b2111418802c801400344070411075100e04c40d50044801410064000d40441b82068680c40640700c00016504141c0d07200b840081c0421021180c60300c1468032030010301900c45006000458889400c0d510b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 470173884 1250 470172634 470172683
    0x801110f0a031518050114120607050315060304081b0303060d0b0a02130b0a1e050403061d010509010b130c0905130908180906031501170106090e0304170118020607 72
    0x1300c144a542e9580c00600c11900e02060f9060072000507508020600000c00c012070b035444025022509001000c800100d4803c04000a0ba40b85000034003500c2d160305251400c03030f4817500107180d4040415201051000b01c114004252441203500501924542200d600c40445001c00600301d10342158003000074400d2868101003007002072808004803503036003e13004030061807840c800c1502c03c1e001e28000c2c0c0301d840065100c015a0107681d042440040c0c0185405440340b00745584a610101650a160400503902019485998010810764100b01900342d8221440c00703c803d01c4c1c0c02d6402080810700305201d03604040248a101007240c0c4030002e114041783c0c807003505580260103e290360783c009504500c40c078100402c2160304070501380c005000355454110181100c1005000c3d81d80c1e0400c0c90760604045481c2501300c900241820402003054440501440d52a540302d409605041640b04a190140c080144a22080900220b614020300001c40d0701304034480e4040c0c1001d450480e100901d00c210004083e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 470175134 1250 470173884 470173919
    0x1c0e0d06023903030c0d0b0105071704140a120b07020723010e010c0506040303021e16020901170607030209010e061305090a020c06010e0603030c160801110f0a0315 72
    0xc0700c000440c01c42d00da82c94141204840c2c1e00c041c0390003d10501506001700815a8a1005142c1c030200340310010300012907540c000c0c0d003005440255010140700002031203900420a44030a216421194054081880103100c078600c5000f404540400d02640410400e0344030036007211491041d207510982c0d9220541041485d60221008840300a039171681da036030424811110784e00207003862041882e0039201c058a59a0080001e0185600026a94041d041640700e541c16800c0c9001c589843d4011941610690300815030124040c4c0800000410b05003c0640c0680401504000800f01c076569204100d020b90002d10119040c0100202280c4107541c408001e4128845a94810200d4030b142c041046410440a0301080d1000d10402400d8020180403d0711415501c2c11035205c0c8598a901e00424030b0b40c41007078100c0500f8000c5115400150300103182d1001121000310007486000c2c0403a5540c0224402c600000380618010044010524080c0e0481e1140fa0704903001c07841125031726558101d8000008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 470176384 1250 470175134 470175187
    0x150c14070c060806102003040b121605030903041e03020a0b0901022107020904020a05060f07031d1c140706030c11030a050906130902040b09031c0e0d0602 68
    0x2910512101d07512004244e8048000c50310001010280e03800a8041c0c1d001c10b607100c00200c203016140800c100208200c800810304400702a6032540354540112072440151542c03149150b9441c400400c2d58850f400340c030300a21004001e9444c00d464040000002c1c07412101400908a41840c0080540c3e0380d150f5202c010030f141e41910303503107603145e4000a081c030000c03140c0c10700c2e0602048035000a4594890541d01519410b0718181081c2c0c0326400011088401c0b90b011551020001426194001050380038014176442074942d01080807075040342140480e4100c0c0c401d5006421031030366103503a000e0b0510400707140d80507540c02008801502201c1c0d04000c5590440d5001c40c0e228458044060340c82511820400c14171070156040000d410b900425520904444620500c80801c961484450040301e8400400c400a000c550341d46d5980c85020740c90b0031190302e1521034010911b5a50581d600c1509114a2016641e0b078803481440700001c001545801c940180e407141c1c5d00784250148101d80c00200c42513034880 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 470177634 1250 470176384 470176403
    0x9010819110304030908010b0a08100f0b0a030609030215150d0320010606091a0a0e030709060806060a09020309100203090a1b05090c1206040f0f02070b090c01050403150c1407 77
    0x400100307d0a40b0042104a802502e00d07100420400c9400700e000304522402d4840440d60012001284020300450703114640e01c21140580001003013a00c0d440002094071a030261400807075404a0b003141d00d1030407280d1060768031038809a002d2910304005011000391290421883c40000005080d05502e00c4c1103280c031450703541d02414044a41c02020751707401070990502403c1a0324031340289a2f90390091210210074041003000d007464a640c1408060090080c0c14400c0110341d5880420966414081d15154010b1140b2000400c191095008a910800804006200d01c4a104104030029407005000707a040340140c1c609140002c04010b042c0040c02c40840c00648981d040c175042110303054014200e00c0050000b0002d520342d8180b04403000343d00c100203ca0000340740907007413480c90282020180207044248002181000c011450052501450709542143c0b5048903c000648a038070903404040c2002e15050f400000c244040c1e005400900011300e40801c1000d078802020106401030601240c50842 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 470178884 1250 470177634 470177639
    0x1212d020f03013615020406140f16020103021e1c0902030d08060102010906020a110106051203073c0501050f1b030a142703090108191103040309 64
    0x2454001160014012070080080080001201c9410304401c59407000b01c840041e4038021080d1804080d0400940003482c0500000c1782042c000c2c000e50040c01040003203100c8501b051a0070f8214000d4811050030080c5052500842c800c030b0390080ca215910407410035408200b80120003a03c45e2011040c2102c2e4030145489420305515070b0800c150702000700148500e08451900540d40015150380b04901d141072100458031281c0040f80540014600940480d0001500c143c401da400344a101c2c1c542c000c0c000800c030040c0c4403410050311002804031004150300900c050000702e051007107404840c446080b51020000c41104403440085140311045408590500111301804400e02403540d00c81c1c4011030040280c0307825a81c000142c4000e1556840c0090b000c400240040301a42c000c0044203144003101b1818503012507203615980b1480144039543c4441c10045c904140300005a920120050315108240d0b941c2080b03a07423002d2507044000d001191a140110100c8001200542c060342c082d0740c960340100e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 470180134 1250 470178884 470178889
    0x406051810030f110702032806051005090a050f060f0a03050703060618020f0d0c020c1f0906090f06050a0219030315050913081303020306090f0d020601212d02 70
    0x1c0490b540100d4442d01004040c0042ea40810720321920400e00d00894423004602d50110003130403880500030000e41c80c01c03060040f051031003907000c822200102d620660560329201903009898065030300070b000a0b48000495018078200700b600031340c0e04028000441141d0b9a8a60358a0b0000700d0b442540c50380d40e115400c0c4040c503455480006903421848066180c1203201599090785d10480004088030340c0d80308920410584284400c04401d10000c4c0720300904e0186210b072904003403546c56407102082c0c90f060f00094080c040c49100c0e003210703000340c182403d0b00d14010056899034030001d078080840c02841c05180b0315180141e02d01d044280030307540003c0c1c1c1d00c46d421609440821a608101e01c01c10010040048074404ca03a400720590f503005140745c0d100d0b54514001540c911054000a5043c05203204000d00c10a0004c0d0803140c1107602011110b10002448041c0c0e00d4003420300030903010010041800080210544541d245507200c0e050740b0401841911030039680c901c81d03044000c51031096041d402c0562 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 470181384 1250 470180134 470180141
    0x3031803121201030f03030b100905030606010f021209060c0f03070c050a03020f0d020f0a090b03010506091003171c0902030106050901060c060e0c03060702151b0406051810030f 78
    0xa0200c0c0442458110a204044482d01d414800103168260f03502090342014804e030404080d4203009031000c0117042d100140a00450014003481d4000c0c4107a41c0000c0c5c0700d40c45514000d00504054000c0d108045c0c00d0001d281d840d500c1400010b41182c0104441e10411504000e181550b00d50310024684401151800d81d14810a40d40128030410700d103141400580d59000450340f80c4481100d10036040201d07440031403100781c034441e41244d100360521400201421960815400c4c46030490003081190303600d204001d11140183c0b00080f500341c0c1e00e01c00f0300c0040d000403402c00d25a50a80d05160410090916600521581a0340e4002c02c03516140e0072400c6050901440000d8641210041001d41c1007030070017008090084000b50110792604001e0a1a4205000404010700081c050340c1180c5040b0700013030b41d00c50302c0420426088503403034001116105504040524089540b41052402c4c1c5040701c02c0f42d081e0040b03418101c01e46826a40e000d83d9954512484584031040c4d140400c00140010b4000102c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 470182634 1250 470181384 470181403
    0xd031806050301030b010501110f1606090e090607110c150a030e1507050d060b0f040e0702010207020d0b07020c03060403020607120504022103040f0f030c0503150a05090c03031803 79
    0xd001d014070041c4002a059900c650540d0704c280783c8200e004807102c1d5458509074a8a000384014014218201084001071840780700313072216615840304055480c8122005040700322003172000c6030002408a010144900543c1c4006041e02c07040311000b0300e060001507200e00486c00f43c081a03450010b20f004040e5018060401d207400020003808c06011031030009450f0340c9008001000b0020005100c80b41181c581d40080080c20b41200c1c2c4980315031100c43c510301154403a02034103801803c0c41c0d0001b00414414000c07510740c580d0140c091a11700645903100c0c440301c6000751041c001e40c0107141c200c0368691010032078544910301980c000c2c11103080001c0301030b1200c0000c0d1051040719080c00c04000c096101e017080196074070301d20740401008030141e0400b035003540902c1c0c01030314112203903210024086424440e4401034038000c0304440c64003651802003554078481231014840014190000405c1008039138001a440034414042ea4a16425440000e0455014110580150901e154054107078202017262085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 470183884 1250 470182634 470182637
    0x1605040f1214012319020c01020c010e030f0406080c0d1406010908010603030903020d03090f03061a010807120f020c010207060f0608151602011805030d050a02031909110d031806 78
    0x249580211042042655241c071051244000c004600501100c90361001c5d003100e044421501c95400030461030103944000e94402041d800d11035424200c1a01100f22940c01c5420440700785000d2801c80c0c10368102c6070040a6506402045c40000300050180c01400b0051031070040796402c5182110014000200d680c00070395250707150a00510010360865a608152501255800382c4600e0503d03007210042c1541e000320643d0250030000108011b6a0303040721072101c00300c610f05010300003403e0044a000000f00c46001c00218841141000c40c84181e02001c11206010310151800e14507000f00b600707a90100c03104030b8144d075a582e1245403860461054501a0007460040c0c075880c07c148801b40707032820018182d1b00000e0504c00c40718200034001d41c0202c0010068040c032115900060528ad80c0302d07000360801c4084182400000b030802030062084070300ca1154600030210150341c840342c0c04018a03407030004984001c60009500b03ca640d40c1550164502d229584d10740c3d03403d503c2c1c090030030100380303642c00b680 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 470185134 1250 470183884 470183891
    0x2104020a09050a1e06060512270718181b08010c05090f10020a080a170106030207030e011e0c0201051b03030603070902090f01140d06030b01090605010203121605040f121401 76
    0x580d0300038221180c4a90710406109070ba10340c500100d02c1c6900400c9c6082c5440c00108400300040c84c04200b80048034003030301080c80000380ca848543c00340c0d690318034000342c0241c2121102c0009034019910041f100c7c0e501940544142d1108140b50031141007143c40c1010400202d00300e01c052824688004950750240c030448030500b56644040d5a60222900c010814a00800c0d0702c030701203105542c1e84820381508070f000102565a440c005c2c1c002c0d03004480680004904440c8000a54028100c0d1440301c04201c0082030071a00400c0215054100300d0012030400c10200402280109003030192014002e40d04051940c13414048201481c1c0b5070300e40e01c4031281500500c48504156100e44104a003040e082c00c04946080041c12055018890511801c604138940440030051103000c8102a0603113110711403c1020320380302c000590380c074010403034003491003105040080d0801c004098550400049800e0190502e506c65000710004036050304180600340010b041201400056203110405458000080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 470186384 1250 470185134 470185139
    0x9060c0809071d041707060204031112010c090b0d060e150307050306310602030a06030204200d020f09060c100b01050403080d0b03030c01020a080117032104020a09050a1e06 76
    0x1007031540140080d08144001012645c003051a404031420315a10003030071580caa44a103030141e406440020154040c0031040c415842c116014407480218480b1a222440040e2a200040c030255005209080f18242c0b19940000e1a24826072a907000c0c0e1907400c852800340c80640c092600d000041d40c40640309500000910101e1b10010618030184d0500e28584a42e103201d404030316103080713085000140071500c000104004911158810815a1301c22141806401e061854204100c19008034181c00c6810801900101c2580c41d4010010303461440e01c003500300070305e2900103240c0b50024014801141c00c204806c18002c4078520032440c1da03031003d00b0060b04090964503a0b0760907001b00300d42c00000e00c1d6990030380c5882c0da07030800a580111500000a564609240e0001047c0403008e200d40a00c01d0306100d071146003101c0100560f030382e482485c0155a1001d007200f0280ba10740401410990300305040e500041003003116809a0780c4260724030800460484000000f80354070040c00c0b0018816185407107420b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 470187634 1250 470186384 470186429
    0xa08030f0c0a09060302160209040807172a010b1804030809011104030303020d11040801020a020705030118030f1103121f03170a031b02011b0908060408030a09060c080907 75
    0x50307006503404c0c0d10700140c41d80901402046211030b000c0001c2c0d07200c8503038000c1104208aa10041803070b03600c203000c410380781e12075403011b18101d0013086211807201c12054000c01c410803800c1e020000b41d039840c000220310b100800c00850401003900d04070380e0202c200c40c010081456088a54585c00c01502c1e00200300d0141521200c800ea0b010701d0100904241d000a2100a03860040d00000c103031148603080b840d03980b40e88200960003035011140c45d0f40540280480003c00d440c040c07150b0500c0000c2003c03040004100c03a40e04480030300c2c8004032601445544030601031006020800351090389801045c40c107031820130740d034011f1002482e42d904105400a2060900010f20007064101c1600c02c1c800086441c0c950a0710160007800e0799083c09140c7c903403980f100341d4182c2d50542255644c0c242c541c2d00381449884031101202d4151041c020110704c1da1081d00403400085100006690000c40d01e94005070420b1682e8418003525094a602c1002640724414443d0b55003080c080034000b0004c4403214042c01c00410003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 470188884 1250 470187634 470187647
    0x60f180307080a020102221418040602030606190801030627030810210b060603040c05100509130912050705300f0304030305010e0f06040b01030b030a08030f0c0a 71
    0x1004202d64000b0900d80e6815000350161424840d0301140c0b1910048240d425840501d0b60340308a20702ca52400740151440c1c140f14040c42d000c45104004c03584260f44940320007000e0350011301010340003c420484e00418280581d4400404205569003244035403440c1408004e0350820341a444456061075942d400c13611010720345e52519035041c10b04040301e0744e4040d0780300b4980280342d00801d600781c02d803050303181d40b0030f00c968010807030030b100c2c3c0003807400741d10b6041c10312016001c100d500500d808806071084c0024074042900c08582c07581480c20f28500b8501c1000705e6a07400d10f40b0100c90b41c403501c0d00c3c200c3c030402100b801c221004051901e8258200300c0c182d01c40c1581c07031a58910740307952007003800881d0008402005101a0402c0c14008140d680d81c040205220f0036882181d042d40001d00c0c010002c154460341c0c581940c000e0f404064200c0317603501c420f070800000b043c41a03007440c149643ca03610a034030382c2c070240542d801042c0100245501c9203885074051711000002020129006070401000b42c1541d040314 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 470190134 1250 470188884 470188897
    0x3091501080a1101030608071d1518150d150c052104050307050105010e07090f0b030601081302031204052806051b060c03090c010f0905010c0c17060f1803 68
    0x610400f40090b010040e00100075542281c59207028590002c00c481c10703c02c04500c040c03070700622107040c19902c0f036070340807101054411884e80c440c1d115801d10700c0703208101240c282c0101d409640c600e0703175140580c002003807400740000031910f01c03241c0e2082d5698070501b44100da42d8507200c2d0501e02d241030411049624418512017501c008014814046404d011040003981d508a6101008015a50310b600340c64441d074004481c0100003031001c2d03901083e80304000d44c03c0000c40b00c01c001d0300c6003980c0314407005482c0c401c1c004000910720401003882c1e4015aa04100300c1420b4903174007403625929802d2206214810050000d0348400544250541410110311019902141c2480c0f4145e0f4650180c2080502407012040c50804540b140341d091000c511249070046019880300f904031100000c03503400540e50044484160804694151420446940106215400300f4842e442c20b045260f200d4084500200208000c1e001c2a484041000b030b180c0c2c80302c1e040540000c0d042c46414040c2c05d078151855500d03c501c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 470191384 1250 470190134 470190143
    0xf0507090b070c1203022b02030a050906070f060f150b0a140f070c0f080d080109020d110705030310050d1104090f020909100c141801020312040803091501080a 70
    0x1031101d0030f000070074418201900e10440f100c00034002505000759280c1d0700500303219248440801e40002e1482d42502c9000c09032607034001d1420080c0c4440c0030343c0c0036007000403100e801040c100301c8074000601400d00140710b148540c40014000d000b45e802c070001c40f8401028072482c0580b40409001d008001c2d030907500450b4451401e09080c80d803075100d0351200d00038400c0c0c80c214001d0205a1400300108100001c0030303a00307402c6006446a030344038902030396002c0103012400403d00c044010300001b44c041c0c005140c1819a0701010402280101041450750b1000340300740d0b12604040300303001200d1074803c1c1d07043c01010102d8000c0840384080d03c86108403c603030720409110340d40c1c03900103c2c1040f035103102c035401017a00107007903206174500707680b00d20b032940d508540c9070110030f15011030200100c0c0126003001c54205801f1030039080c81500490100b026070304909103419803009103e1404400b03c2000c40348c0c0304c0c2e44100301a0b600c0b070506210541c9050604100100300c4001000144001000041e540ba60207030807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 470192634 1250 470191384 470191387
    0x307080a06050a020403021c120302090603150f03031c20041206141513150b030c040b03010b0703090902030103080a081009021b241303022b030f0507090b 68
    0x503c0080070003485541d00017500800312a9420010b802ca440000f40c2d8280522144c104064500c08101e040b88100c0e00c0103a8030070400e201080500c0c011784e0440031040c40c007a24601c0c44603d03101c0040d18641025070702c280210034524901d00440034074001c001008041d500d8480748800e140d0300c100054012805415415006000c2d903006020b496000745059042520b400c12940c14070003030350710501c8580c81d8401d00414800810041d884030354801d110000400c0c3c0324810b12217007401c000c4c1c0015400a49484075195042c400400c600c00741000a40c0249005d00e2025501c94003880d001d007141d5207a40c40080417074412320041011a501c0340c21920003c543c0d01c1c1c6002d06603100780701c5001d001d02076040300e07031520b01c04540c204510800e8542c081e15520f4160854500700030038003880401c1c1c0307041c0d240016594a004007003010008030440340305a0314401d00541c0c501b50320350100040040c00306925100c05180b43d480344046a80c05104180ca000c1e2811001e100314030307105038082c140f20200d224005103d00d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 470193884 1250 470192634 470192641
    0xe130203070e10170715080133120b120d09060503040305041517090d0e041b0305101505030a0c03051528030803060a081f02070f05150a06050307080a0605 68
    0x205003c800040c1c006c0c15000140540402c10040c4181c03001d0087c04150620391100c0040f68485c101403800400300c3c16011402503c3c1407000301c2d114060015103101058403a65440603a6998201d00c20f40c0450000081c4000fa111003001004600e1035848001400010010701000c80e0740001140e040d9030000c000c0316036100d20a0402c41d00320522000444041c160704040c00301d010381c08203400b10410000c1e6200451f0f0700e4007001300412034040ca0398082402e209070305125144c41c040d030000c9031302c814203040e0344644540d5072310f44407841c4d1544034541c070014000200300080f540440c0f090590140340ca00c0c04200e41c3c580b030917103013800c07504c5002d409110700f5149907040840c103203103546903642d02500e400c255461340c0e82c5d182c6819541c100351000c502c03682c840326002c200c616000521180803010904414545610001c0740c400960006900340c552188003200c0d80040b030f80400c2080c1d40803120100c4401d107442c0c45006102114100c3d0483c600c2500107910030403100100061301c1007403540201c000142a10b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 470195134 1250 470193884 470193929
    0x11010f050c07061d10030b0108010b091e0d05070f1d090c012f0307051203060303040b0d0b09070f03050610020a03080c190507050705030106230103060e130203070e10 73
    0x442051260301180c40c00a1170505036164006903010300c0700380c076010003030313621907040d4040c40c0101400c060300300e0081c80400d400d202803580c0070040014007905240d552403040d21500e040900541140344988440d10081000c14400e4185189080318000c07101520305003042000c0e02c03403044980c52130401c00d00c640329128462001521040a40880d0b550041c0e84680034050351b12074005000c207540314080c0e8490810726807084800c59204500040c061440c0c5400c0440000f400d41180d0003180300107540381424012619241c40650041001d0384401900c8028001c009068400092800c0d0041c40f00c00000f5458580000300c0d81c0d94990b05040c5059140d55920071a0700c54001d102c40600002000141032003201e4001008000f000c3c042c50507910802d071103000313040c00d0711500c0c0b0548414150301203410502809140a071100400305140201d20b0b6541c40c0c90001c0d4404040d202c1400c2c1015241d0003808600d800c020160013000e060140c0c450524281038030981071000d51044c00c4888080714402800781 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 470196384 1250 470195134 470195177
    0xc09090c0b1b03030703060f08010603030519110d080109051f091d011505030616140a02030c1e0f010e031b0f06040b070306060c0c030201050c01110711010f050c0706 73
    0x503442c41c0116620707450a80001000b070102c510178002aaa507944012030303080c00c1030040300b007a00d400d42c0710245042030004011070200161101141003084400c20000401e4040c81600107002440d0b96a000d00c0d41050320010072204041c00b10540720f040150500b8418070202d03c000b0440e5501100000c01050305000300d10b4224440219001ca546048a0425100d040249113025540300303600311001962544804a902480e4038805004111170001941030000d40f10700034072186041d4030581e401c00900140f040d1410803985440c0b0000008c5142003c00c9820801c21560305031040740080c404960b56100a649030321411554060100b8440405110103030108104465690321000311030359443c00781030246001d4030681d0380d00d00103424000c0010b8518460b000c0100d10036002500185074074a0741e8015100f07a40400406000c0f9500d4220320310808502c0d4001d005094010910100142d0204000420083c051503060080c4038083c070401010410019020080e2841e40c01d00d409901c0340010000c262 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 470197634 1250 470196384 470196427
    0x115050706020c03071704030b0c07030908100f0c050f090910150f090608040803060d17070f0c0603060303051603050d090515060109081209060409180c09090c0b 71
    0x9060000450f801034a80002c003c0c04a140940000c2010001814a000c0c0d41c0c46207102c0a4041c00141e000300e2030080040d8000c1c115540300303007000b03c0700719a6078010a0911000c95508030340b80f0b070385200d01c0c0d554000a000c0c4080d0081c8a00e0300d10301d48180b18007010341343e000c0c224405009682a00010b0705001141c0c1c10000503108580d00d1200740441c4403001410030050310200d000103441404001280ca000740174030390013554000511400d40d6034100506c03910036118481035415134030140f10743d01a04458030040c0490b078000e07910720f1651212810450788811195000e0b4042618000080000c02e600c1000d58030b0a0544581c0200180103e003001c407064020784041d1010f25142152032000c00000265102124101c9101100195070741e4005581d0703c202c0c0c2c883c099090300300c400d80300345000c0984000c02c200103000302581d0409440708144801c990301071034200e1080161425031030500500040080041443d85024481c100490390303144d150401c2132060f40001000450f203504070b10400040002c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 470198884 1250 470197634 470197643
    0x9050412030f0f091218151d06070f141f0c0e100504030203060c040f03140f071409060a030b07030b0d1401020703080a06060507030518090a061a0c1e0313060e0907031401150507 78
    0x46801d440d04284004202f110401c4400c4022585100d2446501140d02c4cc01c0d400c00c403001640d200a0b04031000d002d4150000f4000400100500c200300c56510326802d080000a0faa0740c15848606610505184c520003800520319002d040c0070800142c0001321100d41a61380c04007008051910380f80403103180403081e428510050003020302c08150350480510412440300110b90354205a1210401d00614001c0c500000e06110031110020740140d009800c13a034010000680288071001294541c400100c8034449018080e9400090610501d984028229000b002081c2c0c104202440c109000e0401d101d444801014420040784132600140782d1014181107500141100d68039180004000009049901490400354040c42c0d201e00d81100f0314056480c1c0030b002034010303c3d20080303100e00c407070485542120198072071004210701944400c9486500004080c0754483c00e00300c070103100070445444001000c5804062618412154041005001c1ca0440350180c4801042215900040b03a091290f250041d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 470200134 1250 470198884 470198887
    0xe1504030e130f0902010f030b0a0501031d070801051602121c1413060c05040506030c0304230a02040c05160b060303040503030c060108060109050412030f0f091218151d06 75
    0x32502e0640d1381000b000346100366200c1200c0c4800c00e409404079140c0d48030141c0c0110010f501400254082d510a000c00843d4030004003180901900141c6802141d80040415944660920825200481384a61032a20324006071810300d01d100100d240c07600424014006403640d0b5901140310881d9a48105000395004640030715902e408400000391010707440c03044a110b032070018003003407991240050701d0581e0002000b480c55501c0700c240c2d251441e00041c106603040c22440700612010400700300c0d20580c1c91340941c0508503040c02801084101d40c007010240050001c1040764045601c2c0c28403c1e000704e41d902150700308154442c800403d1031809280c1119415210009015a1841d00040c08a040b290b5460456099070780314507100f03060b40c10543d8020300100c460314403840b0140c040c0d000f404d404100220b0009041d50b95002e140c0907106500382c20307a04600401030481481c0c3c4d0241203101c0141040340f946d803615181803241581409000c2500d42004070041048216070080550311118090080ca5903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 470201384 1250 470200134 470200151
    0x317040b0a18090e0d170702030405040b030106090207150b0409020913060603081b0111040609170a201008070207150e060d020307110106290c1606030e1504030e13 72
    0x1039a0361400740042101040d461b8442c940821146044140324440d140e0195044c01d1800c0184405095042122030303240d501c2e4080810a0030041c4007801c90395018401850030f41100d0080c8204450003402e078640510f060140020240e1240d11146030004112603d0155200781e60610380021710aa4100a00c52500004c1021f040e01d8100194a28441540002c00101d20040c01300c03e43d620691180d1000f05031070704010001110388034984c0146036041070070f4628180300c641d0380e142d5101342c440c0741c803201c22a01c8140d0821802d2640e1301a59100315810203103164103110001035039407151442070304a18405c2046000320386120f0448040b1022015240310b440c1c644a0a40401941003211400300003021540900640c5005000303280448901a004000c0010149066011020044000d80c600d090400000640740410012800155041c0740003043c2242060001800e5883c4110148403079480b14400c1c071042c50310000078039003090303160500c1071100c040c000105aa00030f000000112407450000c12 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 470202634 1250 470201384 470201411
    0xf110c0901031506060306050a06030c0504152a11040f021e0405011e0507170c030706060315060810020901180905041b08100b0609100201060317040b0a1809 69
    0x3d207420501200c00d01860381c4543d000c40484045110300d9610001c00700d02045103500940c88003040650f40d24080d071505484040c403000071203401c3d05540c0051001580049014a5041c44034142c010341540f80c1c1c41d11030651244e0800341d0b41720000750321a03641e4038031101442140d42d0484800c102c451520207401c034840d14101c00e50790030600c2801d0200b507590070410020a0008490038410015817151030500000b42c66541040d6007028100d500900e0800084060400420280c01d0b03203481100003003000c03030543c94001c000b03046403018081c00904044051010b22408202e0031824801540010f86038002100105c442210210f044c0340d1940d5003000101c1c000a280c1c0042d40310724002c1c040c40c507082c200b4500d400180000e9202d0600d80f03801c8002d001c06040d20580103100030a00c0102403030b00b4140c0500c000f90000b60203010090141c0c1d501c180400410204081c0318802e05022030041c0d040a02c1e00340440d55034806d40d090360040240303111000300c280d45500e10241c06002141c50030045d000d0314040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 470203884 1250 470202634 470202653
    0x120c080105040e01050115030b210319021b01120b120f01050c03060d120e060f040e0108030408340306061e080717030f0c0d0f050a0f110c090103 64
    0x7220300690400e021410112414083c1604a801010b070003010150500011002460303d1000342d039011041c404484d010041c0c5900746c18441d602500996034401e402d900041c29200444010f2066402c40800e2180454107071012466002c1d0031b00b00034000c5641c001c00c2800a119200206620102c03e9105e024481d5001414a8969400b51300801c0903441308800400c242c0070840d445944144034066400c0081c801e104204901c00040c2488444070000328000750f1039400035170011410f107402043c108800c024801c3c0003401089000055890542484070f1036844d1018082c41001c0c8424403000040810000509488140030444079404407a4480c601800605417510499200c070304002d00942d00460395a6080003100c1c0c1c03043c02001c0162400448824404040030180303418001849040d603000d11000040000c8580f0030050042580520f2005e03102c195500201d034100f00c001e100d03209c01c1c00c0d00644000741c0103c41e4200022500407004540d450901c2c1c91300001c1e00118000000030402c1203101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 470205134 1250 470203884 470203889
    0xd1803020312070c0c0504020d0e0f0c190b1b030d020a03050f1e150105070204021306020d0f0212130305011e0e0c0306400501060905160f120c0801 65
    0x1c410003440c0c3c860140c1116500307490a0082d240504a12081080786099401231004c1001c00f040070174548410318030725041082d508915526030300f1200042c1d0b071510f840e03e60344206044036021000c02d1400c0c1a000207460080c52103124003180044505060b0340400c10544060312a456030a641d00c80c0802c2c0300502074030b4140e69810042c0340c41008200409203039070680d1402c0b51022102c07100c40e99500c142206410b0588503281c140641002a100583c407180020f02002001d80c00d00f04d04a4941030000340303040000034074041040381d441e404000a50303000c540e0300a41c00d8000031254949607445a03103401c45085600003481586040701828140c2c2d11400c1e01c0003e0f4003000e03020080704140d4010552182100e041d02c0f0b0381768016400007040b58004010740d09044881c11905849402c1605090110114412014003c0c020b0100014100a0b00b40038401c0604948401448281000010031000c2400104018107100074154424985031244a01040b0b280c0d40c0942484001c20b10b48015202e0502070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 470206384 1250 470205134 470205157
    0x20010e07060f0e0f06041e1503091e051c0e0306071b0303051e09060405010e03071101080702120412030e060a050906031f0303030f1a030c060d18030203 67
    0x808006401c601842c0d00e01180541510b40e0389a6080140412100c1e000d14070180e60300120600001c2034003881a5201000000380081808030303c0d080880d50070400da0a0440c480030181000162000a644100d0480c030010381041c08035841e13102072520b6414404181000302140d030382c620344500b910380d01400710004c8120603026100f191702e501c0703012141d05a544041d6424030181200e4900000c2c800c1d8400b580c05040c410095003d40b0a030556207181d0303032050300c03504081d038440414042400028420561058602c0006500c1d0000c150b50b07000610020a20540c10310400da40059013441c0240820100c0d02d000f03005807592503032100b03511030100c408180d00760009140711083c1c2c485403c0110440c0d03115081c5484040c1420b401c10200302c2c140c0e00c010030100740c0d080300111600c48a604100b080000d584684c5000c00c1c103c5804010004943c0b007001074074404103a030700030907103281c40c081801d561181c02a5232555a50024021550180c41980c0700c00b80348070850040300081c1039001c8060150001c030f4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 470207634 1250 470206384 470206393
    0xb03030d091b032406030203010c080610091a090433060c0b0112150c0f0806060a090e06280f0608010e0c0a112e14040602030720010e 59
    0x25800020b075010309400002c00c000006803040d260700c48040d09200040003401c074003081541d242c2d03012a0940d4440c48810300882d05c1d040911880f0702c0c0407990400c9170700c80351070005602c0d4501400c0c0071110030160030200ca090300c0001c5141007621550490700d043c0403c00a00c242100c4800c100c192040800d00c0095403001c42c3c1e00c00495020301ca5050010041d41010b03160b4210f90900a9001e00038a41c00710486480b401a080003201c1c89940c0103260660f03610391506032004510450141001350002c2c0002e10410b01044109416500100790b182958000110480309503a201c0c0410503a4043c01b040203010b00440700e0342c070300b525144080b9500b51780211180024107a99200195803114003070244164024482d00025040c12a010103084945524503141e0807030704903c50700a013080c03405030804c010740c1c00d448400040710b00b04010b2a036000300400010401d0f08034001854400400150008000c10f8000001c510a00d01c00c0034131243c0114074242c1010145051100103008008812001c4168000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 470208884 1250 470207634 470207663
    0x121a010806030a0503090f0a03020d050c212e1103010510020109031b080403080f0904151a0d06080303180609010b01050901050703090e010b07020103060801050411060d0b03030d09 79
    0x14082030343c203405540a0001c0d4203040c1424200480503010100b2260405822100000540c0d5402c500d001c8242c01080900010918402800b0505030340f178812600d00b00c000c0343c05000000001501050160003240c2c0542100000000791010201003030398070702d000782040741d40f01d215000c1c2c3c0001c1d030482d4000c5030200d0841c1719200082c0d00b43c50400704054042803070405a5066000d1b4010003050580c41461210714180d102d640d00003058020098404c2041008100c401890415201d540b0300b01200c41200c03481c40389008128900c00b510900000c4403400086452030b1080c159401280140c101c10080c1c90f2207181c00341c140c0c21980b40a20340e00c0c14504c1104080781c60707039a0621402006000c181c0d51980f0b00000003005541c1548100400c408000981600060b0141e9425449018101a121055640b6043d000041c196201c80c0c01c41030a036403401d0148000141c016500b0403404d40b0545280c1d0700c0d895218885002408495090b5405000c00a40455030083d542c1c8a0b5201078421241c8011070107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 470210134 1250 470208884 470208889
    0x140901050a08030304140309100801051809070b0a030e1c1704020a0506090612010e0108070b1201120f0c0609090e1506040e0c03030c06070201060605030907090c121a010806 76
    0x21150302c68151541c004002060205000a4903d9241c62510701101d203010001d42c00300c1c01e881c001a04ca480040c00c40e10061009190012008a000a4401c04c45109040801c190b544804140c8240b4010040004400407130078069080b0344415006441030706c9a207546010185100b0b010010040001000500b10400c1c10340100030103030003580c0103010380f85500e01700414414640d200d4602968450010701400d10495207140c0480d010345456050301e00b05503d080c05407498400d0342e80110340e40a038103001d0305041c400c0c1d14003014110b8403100304d007009400c250305151269654800e005002540290b401142c0f0a801a581c08125004203a08000010721000d030242c886803040c00c03140c00307100601e011a42902d000d03001411807002c0c0c4415520030705524400245150f020031400031080d08800c0401c40c041e41c0a216070720003001b01d418072510f03624141e10001c0c0c23204560301602c0080f0303a03540c00c2006894896075140d5480004001c007002055260001c45900e0540342203210700107000d42c0001481c60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 470211384 1250 470210134 470210149
    0x4050915190605120d14070b06090c1e0c070f060203090d020310020d09020906040b0108040f05010b090a02120106262e08010b09042f060414090105 65
    0x4010300c080029440e120034000d80303100c04580d00074585003516400d011800c2d5885503c082d020004010003440d421045400c042d148180180804020710414044031011803810040603900a00495001006036158455605103000714104849d82806404100c000420b01c4401802c402c0b812808849089549101c0603520b0800f60051030300580040c00010000d040c02c84818107510301c018140d414280300400408100d80208403582000c546a0b0138140075400d00007021500910148e0b000e1048035821400a80410f174003410052000000b00604424071800307610121000c20018441c4800742002500c06019400071944014100c03421800016954000e2021400d101c80380c1910303060500c0a11705100501c4001081340c544a5160114891341500b03e03440b941c03070f100170780c684407079240d08195840782120741c01342c4014005c03120741c4140800b04407170a20f040c81c2580e10815a501c803550110500101300c42000c805e5410543c040303008194130366816008025048280c0d009283c0ea0303618010030851 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 470212634 1250 470211384 470211403
    0x7030308090c06031510021005150906040506010507080c160b0301030b2412030409090b010305101404290a020c12071707051e0d26070806010e0d06020306040509 71
    0x100400c906080303040c182e0050400011b28016101c41001c00c6401c981500d4088620300c000c0c20010721007c3c00c03860300d0503a1a0b0400742c240c504010f5442c0407000a010b6200390800944030100200d1711461020082180c0010f2000740160001110b40d944050f6940e60420b0004881130b10319100010007040010396142c040210b01c0e024031075002d191405006180b6140503403441c1c140170402000c54211454060305444a106040114240d8903504002e814103040b900210051810980040200d1010711600c54216030412a074503460150a608200d062001c00300000c0740c0f0810408102e2030452030307400342024504800139607103080780a580d12031440c4502c1d48014503291940415000414100002d0006284100102c84901c141c500d2403034441c07100601441c045911145245000540c421706c00342d40c19070050050300140c0b800c04040c003030070f5000600280400c400f610029005a1040c81156003045000c0e2100350441100c4c2070100280d44119403180c051400d050200e9040b41000462181c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 470213884 1250 470212634 470212651
    0x8030f0f1302060307020106320307120809040e0a12030612030512040602120c0903010f0c0c11011b030207030209011e03030509061e1c05060604032307030308090c0603 74
    0x6154180d42000095000034000008541d6101c08c0400c501d00300f042d85d0b401c841280d01320160305a80c40340800c0001ea6119240034061f402c169130401c400c64104060034401e0780e200800ba038881c0c888001017401080280360a50071032040690b2070b8180051000110103010056900380207154840c00b00500d5400c004000030006442000b132960f000d42e0079458960000e10540c0d01600e0041e00c07a0901c0c8042d001075408036a07a14001420031941d14091241f00f0b10900d0206061200501d0400d000c0d115072600c400181c840024940d074082107070f02c50880c5098001c00100901001c15188c24000d5450b569800101c0c028001d00001140405001617506000d080d0019156902c5003103560488054010b00c04981c1c10240c1440840031400202c00e0f0800402070305409240c40c0d001340b58804c0c05105400303010170307603682c60704017441a1500c41100b11030960307411007042e000b902c5441d40c1615030041e030700b800210039010700c0d040070082590107070035a0b00403100030040703c09252810301000881c0c44107480051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 470215134 1250 470213884 470213911
    0x601080f060a0e0901060801110a030614010c150e07090b040e0303010806070c1e0f1e0816080403171315050313030c060501060809010c1107060c08041208030f0f 71
    0xb00540f00629161311443c0c080000c13034120380d240070090071f54000350124030380e651001c60012059941882040010020329580150100c104070001e840207090410180c800f07100560306904421054008049000030001207801103541c070030405009226108100b44501d00701102c80c40d00003000026203042ea0744c8a40644000c1d26213400554900080030300c1242c640d10802e8420f010039080da64030000090080c3c5216404108a1606030500b0041c0f0342c0501c03100c0b450a10403c0070a0360b00054910f1925003124250818143c1d0418101d50302566100601203801c04903000d1800e610f01001d020841d42580c81c020b0150749a18202c44000c82403064003000503402d0000890000b00d40d803028808030702904140000c1240b60300d8100c1542c500341c00c4403010565480c140406000b00344a01d181011542c070308040c85980350901c035902e40c403441c403900003009000d5520b6414450200300b114005d00b101085614012450310304204c454000701e0302c26488000090000f1803010664001c10301c80d150000400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 470216384 1250 470215134 470215139
    0xb04050105060d0b120a030e120a0302100e1023090d05030a021303060203090604030f05040806152d0f010c020603280c020a1b0f061b0c03030302030601080f060a 71
    0x900050139010b400a61200003014140d0b490801403081042c29130003580c408810004031030078081d141a441258080581c8410a0b0b58082036020a8601c0241001a030100d80080900300702171510100e00915002e01d8a00b40c04400301080d8251081840d0361042c03014460f0340c1d44c005030b550b101d04640450070b0106004000013401c18400d07a00911201300f0003203694100d0380d02e9480d2a001ca81003110341c20266032010f421310043c1360b000b0480c0140d021a41c5400d91505044c10500c6444a41c040d050700304101c03841c0840002542d07050340c501041040030340d0710752201c05c0f8054807040c2124404515405104120405260340d449419a2124140c0181050f0300e15214402404101c030001e124001413000e4109104088014030b00407040b0b608520f50041c204003040e414010008071441c080e030664641074101c108a240c45225904048903a2800c0268044141c400020000540140001c04890300c1071301c04030401da0554041d50080780c00b80d8803040d1554071403c17588501301043d01c800f944801e181604 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 470217634 1250 470216384 470216407
    0x507050a0c02042c060606180d0221030d0b030c0105040e040507032901090c0207030b1003061d010c02010605030c040b0105091906140a1706030a05100f0b0405010506 73
    0x40c18030700351010b400007130302c94200c0d01901c2c1c22800c071440c4240c19103003010b00249046410800715821200807aa12450000500750700720b20110418034842c0520b02042c81d43c82503695900c8849034801c000a0500300c0d0b0b54610f40750315103d5101e540c0004005d4035102c1044064100040e146281d01c80c10b84035249007a041000c00b100031600208211414800c865001c0002080202962072150284002c1c02841c81d40700408803400c0c00503005840c0191420206035041c0c1c0d80054000c040703c0d040500c0c00b00c5607d139401215108030494001038034032801c00c1103008400c0700015013400d203c61804000c00c0a091079420407030a90b903043c031411717505600584c0c01d8240c600e172a40c880d61042d04141001d034a0000004045128240b02c100c0603101001182010401e464014481c9003865045003242850a215400003410b90501a42c0042c111140e1000043d042d403010000014203903045000c580300320b02c44054920241c601400d07190212414021412104e05080c050325042e00d40c0140900c0c10320088104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 470218884 1250 470217634 470217647
    0x3011716050a0501031e0e030406120203041721090606010e01020303191a03011a04140f0721020c06010503100908090603070311040f030218070c2010120f0507050a 72
    0x31640e0400c9a5008906c1e40703400244500d0740c62119401c040c5885902d0401d001c1e1528221000180d0801c0c010020400002d07031b0040050005440c0d01c0055840c0c09440350841c0c071140c1d85012480d48080100207000320208005010313403043c482661a0894007a0b0700d0b00490f144e01055401c040846408007004a04640641148401c580711007520814107441c040040e00b0341329001026910702803503100301440c5041130302070703080341c9616181e0001d02400c00540d070003610362004000c403040100d1003244034645100ca494040450514040c195260740d1041189a200e40d400c1c46180c9c4a441440f61a00300e44100d400364071001604a00c43e58200b403040c000b17200a0703a000529002c00c142d0756030758661000482d00003800250404000100c00c2c00e04507c148640c012403a201440700740074007401c101c4455841030207a00f100350301c0490b12601081da030200d158220410390b115580413201c0f100102484d84d0148022001d0254a50180300c8113042541d15400c80700b081d501400002c9081020508042c000c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 470220134 1250 470218884 470218901
    0x302030a020d2103091a0c0409050c09060d0c230403031d03060f0a0b01090f0b07020a0504060b09030615150f0f12010311031f0f02070803011716050a050103 69
    0x4082c12040c070358120203c10803140300d4403441c0801e0340d41080001b4400c0008040d85c4008a800c800300d118241801c501005000354803d201c081900c80e00080e1460f4000700990703a424002811164461400c80102c0001c1c3c4084120240064103105c40d55842018040042030910f00d18400e0620705420368404460306854022092400110307205205403607103080116074072807800014014080d0078088140c03810b45a4a009050400c200e05100f8049101d002c0d480c50110b070b208000740c0d59201d50b42d2010544010a580c0101d9119151000004d0805c0b000ca0081181d400c00720103603502070347c03140380341c081e14100c003000c030758000b0900e1100f03030b0002e004274008200010201c4440b030700b00020280e414046034000b05568500130340b40801081000390f80324100880c1c0710100d014041540400f440e080d2854403d9100880755a26030b00700c1103003100c0036411600c1858201c90078554a40e140c2486c1d98005081c5c07501110b0038800c0010603082c03051204002015100700a0040c0b1026180c031004401526015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 470221384 1250 470220134 470220143
    0x90606030218180c0915010c05010f02091003020f04050603071106090a0201090b120a02090d08130e0c1206060702010302160c030308010b0406120207050c03070612050c040302030a020d 81
    0x10500400941d490140d14002c081c840b62420540d07250980c4910b40c41002d03a1419003e55115034105021541c0351002503a210444020190b60000140c2c01210440407201c80a4055464076152181540c80c40d001000019820740d000d210101034400e0031402c074030446084040301102484180000d261040c011038010030286012030340300b00d160001c0da0410a00f07607403408507944108450b00443d60090180740003020308012880c100308019494402c038290050034210007640c0020008100d030341c0c0c4044086210340083d0314a449520000c5000d200c00d059014a20213030595400140001189000b201c1441c0c42985a0740b040d5102c6c5024001d03190800401203050640038015079070250700d0b44d05c580000031700543d41511221310b076080203000380380c06030081814207904000512042c0d4000b0800480c240500c0e000685c1c91503e42086030400001003000c543c54000c100340064540d51000c0c8404403d0a80d840c2009951105404600d2a120303c0c4002505500407910000262074501009441c0e80e000303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 470222634 1250 470221384 470221391
    0xf0b060118090e0c1305010905070302091f050409020a0503180a080f0306040605060304030816110a0213020c030f03090c03011b03021b0607021e070302061605010212040f2609040906 80
    0x60713002400a00300f10580081042e41c80e801002688114042c09400c0700b4203041c2140b03801c3c020b6000c83c030101455804c2c11030081c06168010389562150044034002d1540340011501c0c4d22900e007004056510544945070440300c08018842070a40c0413804008a03070b840806180340030180813001c0c00c503410003000c441d840356a07001e0001d01074854400035031241d4402e68070030007245022500303182a00d10030b0003a41d042020f0f500f07103840000000130300d10354410f070104c8040d0016230083c02c4020291041c10085801400301003443d0a140c103d0601642c0920003400a9075203030b10015090500b2119044c444003c0900205801c606a81c000da000700f1000c182841d5403255000314414091800405640400060f440030b209014044000f480b9240010380600207050220310303540015850340134400c0ea1224641d0849203001c1004004d5048500480740303401283c0041c5054108403c400b01205004d0310361030311f8480801e8441c000000201c8440800584103401d00c0d00c2c504c14000140f11621044038910756 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 470223884 1250 470222634 470222653
    0x1103130b0a060906031101021b09060f06130305010c090902130608040201180e150a0e01032301050411130203091b0315100305070b0403030512130f0f0b060118090e 72
    0x3e043c0140c401a40c06505a8044a0000e5000902c3c240940c584003510f04203590560541d80d407501c07040d40e0000401c81d410004d01d941c0500140c120720425013005100c07049241c00004012064114000640d120303161034032681d9540b80144242c0c030404410042a841440301405a64007404038190414010314000c42c0400154800715003001040d0407030803000c8484010001c14165036500040c94100560311042c40e0351900809900450041c0001000b0602c14859007801c000f01d00030740c0003040f00c40300080c0b020b41898245076190084e0034030000c1c000d0f06130780d20701d90b40b51895008a03070003001081c00824450321500e0100028000c0c000020350b2500031010034800f0100105200e6010f5111812006003040c030f549001464030400354003014502c0f0007030008101190f0804140c07456601281c0c04100169120001c5551401d80c40130001c011510720fa02050a100502d401c03410940e01c51201004140c80f00401520a420a20414048940c40d1401070241c51b0140d00030159007600442118030446 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 470225134 1250 470223884 470223899
    0x1b1e0a0204180b1f120209010920160303141302130e2b02150a0b04020f030c0a0305061c2006040312170c18180a0905011103130b0a06 59
    0x654040d0040c0b26003e1503420752600e030604010042c50280d01400102d0350036408107150030300500c0727041c00042c9e0b030314142c0361032a800c100f40354401c0051304c01d844c0d5240c4c542c60604c1d004010b000d070290300003490680c00c40011003205015601404800d0b4601c4510000380c1d00708104990700348810603800780c45074110005584100044644890113400041810000681c1100c1030500016a001154401001c0103106602081c1d4160050030101d000300b440c6002d00c01050292161400303c811200b000410080c110888402405a4054a90742445641c407860104000b034540501913801c49a000f0b482c400c006107060f500711003100b0004484070078602c0e00d103000840640203580291210380382803c414001c3c650240e0105410384e00c00c9802c54850404c2d6086030f2950095400b4000c0741903051091400b5684c44002c11845a12080d500460b02d02d00504070401400700d83e201140c3c550300b410368500d00740380c50b81c0c180d0344103d0601e01d0003040c8035141d1701daa01a044016003100e1040c3d40c1d0701c40208514 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 470226384 1250 470225134 470225153
    0x1b040512160f05090615120705130315050a090b240312040f061103040605090d0f2a030b0a05040c0f08010c0e030c0a0504150b1b1e0a020418 62
    0x6190060b40d245240b0300c0d0030107000c480e1000402082c407515400002c0340405840f50191451449400081a0241c0d680036040e955881a510522211001c1d0f000000c00c1005c4224904007076220180148059181c504119080c2c90b1240802451070f6072100018240d01004807803035005c14500f000b441c031126041404a0300345450801c0c944100040082c00f07100d000c00c4a0412170003000ca51a25031102211103041e00d440340250f00801e0104180099411015510b1048449038103402030b042d01d416544502d0101117681c07061408a24140c0d020b4030030310b800b8102156050449802c040354106d296900320500004001c02401100c0c0b0802d41480800c1d4817800c224548c0240050307a00000380c4071070810b8045d000c1201c11a849100e030340400104400d03502e416220314204c1e0300c1541d0200300c401c9001c5041c402402d454019608003000810208000321240802e00c0e00000d001050b2031144101c1300070580011401c0f2420382903648080c2030140142002d40c00b008078800549515441004503581d580a41c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 470227634 1250 470226384 470226389
    0x9050d06020c06070c11010c1a1501020f03040303120504050a05100203070e0f0d03080a0f020d1a01080c0301120807021305070807020d0c060203091e0303040b1b04051216 75
    0x200c0398085164441458100051504000c15080c9020058184d907940e0182038004400c45041000c0720342e001082221140344401c135035119003541c12807464020001c0c503599444050f07140c0144640c051801103010080115400e503500759403000319102c101d0141802030200a40101c51074030901044c0004500c007405240c494000d040c03400f680d07030b061100b8010300145e400007015226502d000703850b4046036107100a00900942c5400c1105171581d40d4030103c001024000548440c7c0741c00001d4000000b001503000c001140629242501001e0205004482c036000403500000040400c00040c0100b8184039014070500e885881c03c540381c82e03004d60208040d03140035200c58202c95101c10600c030000e504901e103641c0c015128030041070302d100b0f0140d00404055507000080c0a41c3c1c0c7c00008242c41c101c0c01e20031400d00a1640002040103400b107400d081e81ea0f401145d0a07200395a4210100d50310f00c103030301c00f0b002c241e80f104514141003a0038542001f00d80c8a00310703410202c51040000c440c40451250710304000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 470228884 1250 470227634 470227643
    0x414030a0c0c05061606090c030c08100609060e040f0c08010f09060f05040302030a0c02030f03070c08070e0402030c22110406030b030105060a0608070c0b0f190207030207060f09050d 80
    0xc44000500d40b081c0d5a80300c03600014490f54050100c200300842c00407024142540122001c6020744903070424240d07211040e00054401e4900f8080407814031130000d0780b150890300c01042003260030b503240103440482c0c1c241d010300b0b52107107a01000b0402058012041072003540c0200c40e21032409980301083c0d802c4500b203405c2450034540b6540c484050017130b0b40c0f0803940d0701002c006062000d8503103950000d4591142181407014010015060b80540d201040707400051104081169070b502c409040020051101c0e00c1481c00a120300100410840c00740e255560241d42d02600410001820342c0800008072615425800c40804030283e05141d10800c1c05103202000202101079951414864010180c1e50110074090013681820107200c1079840d04030100b800c840c12032418030129200c0c82c40c1120540891341c40a003102d10840140410541c103405c03494040d404010080303d0044d07080140380180e00680e08050f0240e00003001c03c11005002d00c0b03000041e40c460f4500340326503603120b00004041d070050030800e46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 470230134 1250 470228884 470228897
    0x6060f0d1a040e030c0706050f12040b10055d010b010302160f0c15090603050114031507030e0109030c02030706050c060a0c0e12161703040e0414030a 66
    0x45090801d480b451807280c55040145181102c0544c000340d69a400b8442c00c020412300180d0189080704090955400d00580b012724503490520307061007842c04400b034801c00f405803040c000010703040c980f0320594107064154004200c0c03881102c0750303083e10070036041c821803000541070542c00802a1380f44424400d01281c030034100c0440594525000d0840300d0545d5201e05251041191b8035034441507a0100f003a003548031186605a40d480d20b4441c40ca141c0650060880c00441182036a4950300304a0001c113982c510769003044160b0781c0d020000c41c1c2412a414031030b0581c124a0354000e0340d0b17000d0310990764059423504001c607000848035015421944146015800204084d084400710700d41405084020030790303494400d08002020f0140c0b40c4416010b499107c17103035501c000e043d0080c0d0041c22200c1000d0b0008048000c0c942c4040320180d00e0344c024940740c050b446044000814481410100b9409040a43c4001c604050034090561141c0704064010f6403001d204440e41d09007204100001d01259041e0382c0c828 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 470231384 1250 470230134 470230181
    0xa0c0b07020d020f03090f0f06070602070317060405070f2f0d030501080d0905130f020f09130c1b0302070302150406110a0f061d010f0b030c0108060906060f0d 70
    0xe0500c404403080c204241c00800101b21346555546181d800e80c4000c030341408005135110001b030154415028001c4c001303800414480203042c1c02c0100e104d0340500d8001640445d0f560103042100300e420440b0744402090304641444812486071076900ca08404c615000c41c0480c030030402107a0450301d1903a8001d0b260b4812208080000c0c4c0c98010705004040b904028032082950580103002d100300c038001c483c0140600c80c210b900d0f4640701d800118003602860380465440d40080425200c5030b00c40350507903029800c10303102405400c40c03500c14140032640981d030300c2800b904441d00038600c00f209040305408500c9030800200140c0d0741d00038010340c50100c450ba0b1940e030f140381590240101000c401c60303408c141c10100c220800310b100460042d140035403000000a4074480111260341024008902486e15880d0400c028002e0685601040003501d00300c04a941c3c441090340111000078040311013541000f50000460710900700007000c1c107801710541e40390780d080003000440e030000c5501111301d5003505448417101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 470232634 1250 470231384 470231387
    0x3060c0905180703021e13051c170901020703051203100e01080a0809060c030c07090605220b1f02060601080f160c0602040b0c15090d140a0c0b07020d 66
    0x1010040a00351980790400107031802c540e206800040035802403680009185805103042500840c1d0700c06111070b40794542c00480d02d90a2000741030b01600d4003032034400340c940c2c0c00e2407039030071b490a036682c2d00c007c0410310800c10301351000440d0000030000741548121000400014800d114032401403581c09c251a8491515101094200c0d4550344803010140814005001801003c03031180a03540c0c21480e070303d0381e80103014042005d0340324082c48109540004030b1100c0e80f50314041691001c55480c000d00340a01ca407a81d00300440c4103840c00ea550b041100320180140010026086140d441c4001095414180c03094050f6400c03200b2224030300c41c01a0040340400a840d80c0180e4070030b0b004040cc1a91050500e4004811100004035140940600c20031002040c00c110440d01182c0c050040d402c9078030b448421040d00b9907a0380005800905501c441c900000e4542c06000a00c140341d0b0a00d5502c0801c0c1c0c03c07201d2002c0c0c440764040d04800040100707424040010507021901d840c06031342541c2c01895195040c040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 470233884 1250 470232634 470232647
    0x303030f0c030c0f110a0803040506160212040608090106120b040326071b0c0603020c0c1504030b0a0603020607080307180e15030a0c0b1306080601090b1b0703060c 72
    0x1c250080c58a0020580446680640011035069540c102104030f00c40042c3c042e480c20001031300060206000008000c00c006c00801e0709401008023195003035003c4003c8905076150020b42d05050855481480300b040075610911907039400000c940000030f44140c0ba400d2985c3e172003003284010750b81d540b0414184002c150b40001c074408660310034074114603c0b28001003440b91241c1e01901320010030080e00804a8000300b00c90300b010721594010305041c00281d80d610040c0c0030f900400c40d0302384a0700866500004505084003095008242d0028003840c06085903210300c0c5031f05006d000d01c1c10040d44c0d20030100050701c500004005182c001c10a5030b480780f505000061005200b02401e4607001318001d03007002116118210950044807052158074100c51000c00300340b50040f80d20002d4680c1c0c0b103c1000040d001c83c020010400c0c00400009084440d480e1801601c020300700b5035030f541c0010112442042000c2044c409402000540c10810b030007005140341d0039160141c0741c3c000b034600c40c0c0d44021081d030494001b003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 470235134 1250 470233884 470233901
    0x5103050d050a080f0c09030f0c0f180708090f24010909170315091806090708070e06120d020106090e0a030806040207230606030d140a0c0804050a0303030f 68
    0x107452031600201c1200102034140280c0b94000440c0000e0200c0c501d950b03148107941160f84040c08903004010021441030751038440d907883c180110444030541d50f407410600725070603140580d643c00d0401626400c0c0212503508001740f02d0200d0703002d5220744650743c110610138055801c2e90039034001010112501c1d4150326030010703400203210b1442c1900b1007000806600a0139102c00015a003951240d65152a0200943c5500007442d4803141002c104440644220000100808810211991a40c41c0180d4541d2600d82c2d014201c3e10742c1c0329140400c40c50305071181859000102078908066480a121803e140401c1c0c5c0301c1e1080540d460f6201888041414480c141c00460180000c141c400b0280d20050640c1c0006400f20740070b150002021401d101d91a136060000c00300d510b502100b407407080402a915003000781c40a030304c240603900050030100e1041d981c1d00016100700800354502000b4100c140d0701884a100122024001403000050560741e020400300254020f0310045000300201d0441c00c1200c2124 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 470236384 1250 470235134 470235137
    0x703081206040204050d060c050d02070507080106090504050624060309060a0b030d23090a08060103120503240409050303010f0f0f0806130c03021c020f045103050d 72
    0x140300401c5076071b440010a203261078220000141d0f100c03900d40200c1c1c881c80380381000b5000c54000100442001000039044003250141002009042d490b080c29805460007924050640d901110100d80a0007410030140501e0500c07a403122090f0f8910401701c0d026400c100d81040198005000b00440c0800500402c64031a200f00c4c080c1c80544840003000c0e09a4506400e80e90340c1100c9081d0740407024030680215111034070020070310a8819540d044003075172145c00f4002110a0466078550f81c80c451b02407010b5a02a24000f24191188407604000e501c03070140080c541c50340591103010400220f031040c4021400380002118244210f400c102500140e160f040d481800d0b074070072212007000303114404144190410f000e21706021303d8500c1420030408841113500040c1d8030948035001d02038105040c4c0751401d00c05100352090382c6007000201c01c200480b90640301c0900710800c0001032042034458440d1b80103200c2440c042040f000c0d41404040f400790b0300c01950094082003149810300c1031240420010040455a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 470237634 1250 470236384 470236387
    0x110105070c030504092c071e0e010308030406020d1b0207060908060f06030703060507090f140907030507090906030828140d02160b0a0c05120f07020f07030812060402 73
    0x21a54003c243d072080344134100010341e4511103500301d401002c0d282150304200000798521003524680950300c0b510f46108160f00302c40f00c64034246e500313108c6a0405084502c12920340b50268656140c89410f680010400c503546a802c12580c10911f00e50300c2410810007610b55015001600b0441c080c3c0303043d031280c111100b40920000100a00c400c00942075601840700340380e9800c0b544685d00441d00e00702290b0001445942000304001001da4800140c04c200c0300301d14080318016070b6a550546642d124030300c045030024840d9001071380d41070198020540280440c03502c074408503036a00740f000440d01a50401c9404560000305401060400003818440031440308800e0b400c5075504a01a00174014030700345429511002c9189643c2201e00e0b81501d9010500035a004007018007440c0c8182d91080448480b0485850400d55092071840f6034141c0300c0701c50318186130b09440c1d11002108600014002c048804500c01d96898540000e01401500029480b6580c2d10b13031240076030440c0c800545e8009203428002c910 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 470238884 1250 470237634 470237657
    0x1a1f030e011a04110f030c1309020a050a0c0c05060d0905010b030105252105040c08010501050d110a05100503040c080a0b0f180d0507170f0f0a031b11010507 69
    0xb00429444440070045034009048040012551001d000c2c009064044807800700810182d510705e0b00040c1102c00e102255441000e44840070181240501c8180c840000c0080c405803810394002d40d1120b4106010703c42d5080c4803039030b03040041c40320b070f021a1448542c113858810000400609024000e0401001ca00900c400d181100e101c80071504084002c45204854080407040c840c0184001810b81244e280c00c068003185174040c08000d45415101140d030b04c00c02240002c0c240700c2c1885118140c4200808403800602e05884807162000c807051629031040081000040654800c0100404001c903611440d07100e241c1400c0080b40b8088a511640098210040c400002103520903e642d200c0c90100c464615603c41c0740140700030100181d1042e445101e6605502e091940040280408910a82c80c10691202c846400401406400300213007146000388509a00e01005101070108095030380b4002807081000b0515004800703c2911280118070342d1802c50150201c203001d6141d005001342441080300d03e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 470240134 1250 470238884 470238911
    0x108161a0912031332010c11031c1e02060c070204020405100306170a0203120304050c0301050c0c100e0c04020a05130902090906010f0c1104060e01090507090509040804091a1f030e01 80
    0x8021700180d042103052900007003001031140b450034044202908480d0700d1b00320340707011407082c03090f0b0104040400e007140d03042a04542100f281640460513039016081989464031092419000704100b280e100e9021711002c50305488818070000c00007019a000b0450500c1d2a03041d02c5100b803503c00c050400c0d04081009400f5072000078032000d40011258142d80c0d40e55517410140e00f8914810a0306905500b400103004651107a080582940b40400003500c100007601c01e14141203d403080f54101468201c1499520f00d854994050500c400b501e080481c9005031842382c400100c400d6030016055180c0c08100000306080c540c070601d41c451020f0034032080c040907140024010005d030f00002080303001040845403c0e9110b680104004028404030b01c840365845500903805004126003000020303200002c005101d15014003090f00494004d0f00881c5400c1c10401e041d0301800c0e510110354081054826020015129601c41e8100c8401c29814601640d05d517070f80090a494500e40380544681c14064a100d000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 470241384 1250 470240134 470240219
    0x11e0608010b0a0c050f0615060a08040f2604081902090f0603071205060f060406051f0915030e0601050f0a140301090209040b0108161a09120313 64
    0x16940100b080f511103589110868462840a200a115000701d4415001598000890f1405212519030140d030002d0308400f442054000d22003100002000d20700030070702086080c0e040c048458001c2007200321201524514005900c1d0140d01020748180004003081402c0013030281001d081e02e100d03000c601128840e0005001090064054a014410200461031580d810414100181030107100c40801c9200da09003076446482c100d804100c00b5083c0c5001880d54078240c82280140c400c01809108005042c4600017110000381a0310760030b02c000c8510115885140d03401c1e0711aa45c8031a40c0101c1c0004c15a0a01c9040c414182c3c00180942171280c1100400c2e9582041070050ba0324202080702d0100d85a0002405882407450180d00f0586500520041c4500303c03c405041e40c400904907440602002c00c0e20b103400c88e00380b1811130000d1644160110149000c1c0041c05103610050262001d124245d070002d0841c0d0142c0e0400003012050801000541400f0b074400200707248000401c1050044a041064174 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 470242634 1250 470241384 470241389
    0x9120c1e03081815100e0a06031205030a0209150405031b10030b03120307030902090f070203030402120a02031516080603030706020c070b070c031703090c041a031203011e060801 78
    0x44141c0800c0180460008024041e200f40c4c1543c82001c1a040c10441c004c61030b80c0a00442c04440320707407800241c10000a000320004c0380e0340004062203a0702c000c00100d906800c0548004038282c1c00300000b085541e1107010301e80c50a20807890071652640741030b041514281210301082c141803600c0003400415904c2c2c804500c100c0d00741c0d0034040741040d03c40000904114952030b100307107285008000e20000c107500d54000301c4010b10070380f503281061302e4808001540c104121381d80f03001a84104005401410f004c9043d8640c500c0d038a003201c0881e009540000d052200e4420f00003046847c202c02c1003e40c4a80c1544003820079160304141740139040800100340c60f44910b12018000301e4000500300e41d58041041046c0c010f107142d03a03440e6111416407901c01c07821080c902c400d4481d05124250103944585002c101e0303003d01081030040001300c0d21b0406200140c00000101c1c07041580a011250480c1c405002d00164240241411581c82d03051050300041000e107652142030003402da0350113006458000519606 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 470243884 1250 470242634 470242651
    0x50f0d150e0f040302071802040b030108100612050622050109140c0f09010b03071e02030901020c060906090d110d0803160f05120606310501050c03180409120c1e0308 73
    0x204686021f940e01a00c5690b00441e121000000000351169011480302004400c482081c005d45655416003032901a03a1940a0100c1d001070002c21510075841420601c4450200c60b60402583c20752281403c40f580340005403504520524001b030340704810300520681200885108488117a101d000c500134103070500a101002c2e40000c0412400c6026071300100303101c078480c3c86003444c1c0204034000075101e4000458160141c4034089100000c2c1c606041910291100070b813056003030503400e100308060700314025406d0701c4400f03101400c914144c952401648200e4041e50005541e401d020b680803c600424001003c1001498080d6440c0700764082c080b01c00010b010b18220189407501c0000412920034803840c202c0850700003040b0035035400f14000d0b11030b030131480103c4031004551b00c80041d070789441500da000845400400a1602d0f01c1e411710074100c10b40070f000d800022400f015503150390715000d10060340008a0540d20601080001d0303048c0c840c01ca2103109142c561035440580c0e0152150001038079824 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 470245134 1250 470243884 470243909
    0x1f020702030a0f1a010b0a080406020d0f060f030b0c0307021c35060f010e01030e010605090103081902010e060a0e1510050f040b0d0201050f0d150e0f04030207 70
    0x159a410000a03440356005a0714007005840b6140a81030001c130030140c8010101004000181c0110303080641d01c1959254440d60341e02c0e13480703a4401c00254000e104c0302c1000756440480100031281d40c03140001a01800c0813541c906411030501c403040050080103411f10391410802c1001c2075601061414030350040484d40c0700451180041560f90152402d1916400c19001e2030381182ca102d190210103080c0030000a034151512084240440f0402502065001c9215820064410b501c240e00c404007005030003000140481d11400018043c05080e80182e4040c00045195642070810342c07080b0221450320300003007000b001c4d0354940a84070070009054105644d522021000203070401d0102c2a0105041041c00005103080708441c0c1a0707000c50302540e40103408841c1810344d6030410740725841064800031300000d00c00d82c00354011141c0354001000103504803024060b0891010039401a180c0300920111950510341c1090288a5035080041c1600d00221103402480f0120750007060030341c1030381c0342c2c1070401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 470246384 1250 470245134 470245147
    0x403080706022113030306050f091801060905150301060602072102040b060a020f0c0f030a2d0b0103050d0e0d06050408090a0e10050d0512071b08011a031f02 69
    0x100c0b68030b040c0100c002540a03c0d010466200c07005a0303c00d00b258800d450070406542c031602880880300854013003a0b000000350f0003090b80b020300003a400160203c40000800ca02da200c409030006d80c0c0381680d000d28520030a0341ca10140d443d081c0030b0003000d010b80d40b00801c001171602e0074024401c56040c0f03c1c1642c0e2150310748060207544480d00b20040d1480c01800c0740d40c1d900d0503024025542c2401c01e05042580c05501800d000503e003004404602480040082850032460f8503100301c1c480e004ca0002c8601d640d01c01c1100450020213500b00b10385409082e002040d5855030030014140350040c01d03914200a0521560701695542c04818009103401107800034090351340d490050003502c1442d0056038401d56245d0009140350b046140c6910640d4803900300748041341d403441840006140c5100040071500701c007682040c1403801d43c001d481130a0049032000141c80b4000da000d072003000c19800200c00d913511004d1104514200100801d5034038403e400904003080181d41c640d404238121428520300d650000340f003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 470247634 1250 470246384 470246407
    0xe061309030504030204110309010b060a0e120f0d0f09090203010312050306010c08031302210303042004090309061b030203190e03061003170702090f0702160b040911040308070602 79
    0x3079030f000c0e580c0600100301c010388494810b0b049400444201c80d40d50300300420465142815419144d43c3c0c0701c1602c07481802c1d0042d00401c00003001d10300b4000f000d80301e4165a07032449001000001400c20f207503100c2d5000640b42c0304006104118a0300801d101d117004000400010f8284148000a9149171402036125150310004131210901c3d201c010b0001d2101209008a100503c0041605140b01b200e03000960895507000c4030602c003602d02003078040c0d002440040e0118150341550700200180c880300140c10303080131000070210784c0f60580c258005100e043c2d041c407445400510100750085a03003da01803080c19654029070b0313441040004003a548000c260f541041d4054500140074400040c02e136105480c0009011110425920094800c44605210b13141c0c62341c4240110fa07015600070f4034a1080ea5140030000c0c44406015083e80114400c0b460b025022051010903031006e000031000559446141c60781141c142c0b0b04440e5106554103007004100300041d800000c46001c140e000c1c41c0542c4a15400c002c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 470248884 1250 470247634 470247637
    0x10030f080d14010b09120c0d0b0702031b060f010b2b090804090903030c050f0a0503190c0207030510060e0112020402090d0302070603050c09010e130f0c02070f0e0613090305 76
    0x1000e030000380000b000468400c0742c0a014000d20304080d60490350003010701c4c1c8071586c0c690040030350582041d0010988000b00700e10942003035000e2903500460713240513060181d07102c0c12039481413040c900e50821000c0c1311960030381c0d401040c0144642180141002d601119a040f521409555404019040010450000c6580e080480b511b60840096503c66a40703210000141611040480000740390088a003580703405482640e900307080e0300880904140408138195059400500134a24690342e0000244070001c9500501ca90a80e640c1c0c09001c602c6c0c69446d01c189411500d44290700040d00300700007442802d15460740241101d520300280d042d98081800468020721074602c0c840c1e044512400040141600042c0b010101c40700ca030350400990b95000184066801140c698070b0015250300550452490541200076043c3e080000c002214030b2481c00d804121102940b6810258220190030004002c42c040c030350008102080141d001e5284c02000108030710742d42450848030070b42d551050824103100f00f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 470250134 1250 470248884 470248901
    0x905010308340b0f0106020a0804060507020a03150207061409030a14070206030915060109050a030803100807080a2d082808011401020c03101a0303030a1410030f080d 73
    0xb0348074a0500c20b820301968041d8200c4801c01280c44400000400c0c510005511040c0d17a0070070314460500d42420011606540040402d070f90203080b010021000c1124440c01c81841c0d240d1210040e903820452500f5400c0c1c450300e03228411010000d00401882d404080111400080d2070710b01925006100d01074940203008105029420210200030090040c50010325105481044141e80d00306546d204011107001003507004030754114030010800c00c00100c403000516001a002c00c01421650703181c020040c60082075500c1603c5540c01003507500244400540301585014951100034000c0451018442122400000041403024000303014800360700515803164070552500d1007170100348030801005007107040070b01410102d8650071604445940c0005050421400c0c098080d109003c80c0358043c50003001c882000c2c040110180c018101580d41c140f00030340c401c0041c444000386481e10b4400302002c1e09001040d01403001344001051002c5010340b40e00358001c4d6800604a50340b01103400e20200600f1901 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 470251384 1250 470250134 470250217
    0x111309022701260a030f080f060a0b0a0e0d1b060804020604260706030c090803270d051f0e030301211103060f010602010f151206060b130f0905010308 66
    0x51004c1d0080540c0110040c03028a103581d41c018050300d400c4480f4910300e8064a0742a448881e00004200c66184600a0038801c60942001c4000c2e1000c28086881d44000c0b42080b25150012882c0500c0000e500704d13200082c100910b042081071030143c3c04251144605d0050750710000c841c1e408090803001841d1801440400c14080d520019a51240a03020300082e01e840030100c0c49800c400f013824400081942c07045d0380c1c20f0041149000c0081c00d02e6101c010071080c07407608103e6194185011030401c1100030300108021010f003800c0081010071004813000b6801002e02500200010805485020130b01d9688002c1a400e0340c020100901d06101521460004140c05000750410001170074511480c0c2412a04142c000b8068000d01c039490300c0466070f111400d440401401c031003d20241502034281549588100c00001c1c000d41c40e00d00078802c980040c1040c0401e40e0000400388000210204ca100c02003c40070030601c019411540c0f500c2c0c5031b0090030011009804110020850102d007107188081103003d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 470252634 1250 470251384 470251393
    0x30a150204050d06021206040b01020a0204050903041509050415030c03081809040b06010e06031b0708130f080f011404061e0609020d0e0705010807080411130902270126 74
    0x3c41c40c0007030180d00115542c04200e80080005250360500d802064465038050780a8443e4564075800c220041c64054038000e4284400c0c03201150850940303103d950f004689807074101495240100f00000c0e1402d140c030b41a2030f4a04104200000707180b00000c00c040c0c0754001c40d2180c96400100702941c02070b103004055a0321040500901007031201110700700740a07a000381d1314000d800c0d242c101030280720b20081c0d5104003a0b441c2a4816401c100c0c20a019145440c811044a03260802540d0701003488a102d8210300d80500c04660204010001006061703071114941c4024480328180120301c048a40008002400858646290100d02c03422070f081095080300d03081d81004000d0309c84094200941041c20140d0300649046181d400c0044006191002c44405039541d07401543c442c00101c07942e00b0042c2040b10307001d0b5070301e000c41c0040c2d03950f004d00e400300d100714440024203540c540104040503042c140780400c407007141c8101c0d4441d80380044006041d02c0e108240300400d141020b03651031604200c821a03070b40c030307026 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 470253884 1250 470252634 470252659
    0x60b130e070c0512030108010506010e03100b18010815130309140102010e0610090e03070503031303050d0e24090a03030c17040606051504081c030e1f1802030a15020405 74
    0xc13240041c5059940610080185544420040d1005009a1512989a4421165003800f0b415940103600340f0030000c0e050190307201c2c402d1540c4100400a070031000264000d40a42d140f0607002c030845990110304070b540b01a010030540c0b405000407013280110741030b081d10000d5020199000350080c0f8010300c140340c22505145000c144a184004135401060086d03403c7c000c0f582c5004100106803082e80740c100000d5807a40d1681800f81c81c10000714401242880740c103001c0c40303200c5c010500c0380082c0202800060140d06210b0b10034010700c1c5402a0b0421801981c02081c8212050b0000d60002c8190349814005001c14140406580395012a141c0b0703103402c26404100000c0100d1900100c1c200c903026190f80c1500c03243c600380808035004074051002a98010b0142070300d81d0707815581c51303c0003c00904000403210194007810b030900d200b40c2c4a4401c201441107a080412415204401400200e03101e61420300c00f5690000361907140ba004058a1400600b2008609076240d904440007004001c005411150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 470255134 1250 470253884 470253913
    0x50c1b01050906070507020f040b0a031e1e0f0201080a1d0c0f06030105280506120711011b08090c0301020c1e010b0f19090f0f060b130e070c05 63
    0x4402c5440e0b030314074040e18001c100058000d00a480312254004c7c42108000c00788410f0100500d07500e00480d9124600f4400040458007003141c4260368200020300c40e444100c1c1d81400700d4611002c0b4580d09200419520180100318181c080070001682468001e1242c1c44002e4114042d104a010100250b031182003c8001d00388002444481c500d41560b10b07560518140c01000140c0c0030034410141c200d00403121094140d20980486425202c4c00020505665212030104410b5004502d0400ca480c40020901040e142c0100e111140405240001d208031710b0340c1088400d1b035112808104091089800c0401d002000500000000d80002b40085440f00c0255116990b110100c16504440340b804010f640d42c0c41006000d828000c82c8003501240c910040d03001032014291400c0902e50f00005000c0c40424140300c0e0f4007640940c05007250010900030814240c0d0000c40c1d4887e44100b1515904000c00e005c0800003042440884004202c400c480d50f0328000f051b50031203844540105180614079036070b003051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 470256384 1250 470255134 470255141
    0x260a120903140a05120c030408010f02030103140a170a050d05040c03120f08010b070303090c0605040810050f06090601020a08040e1023062212030e01170604050c1b01 73
    0x142c0c0030315500400241600c407581d440d16030b0400e010303040c0d410441603105042c03000001840780203000c50403685842d6590300d8080c21103607521000700a40e40c00100400901c507402000b24100540d4102038200c0765625a2107840700c90407500c540f0998031001c80c4d41c000881c001e0054414010465409200c107150a1030055004d0b100c0740070807540e1960311820380c103806214400002c0801c2c0a03448031061039081640842260300000f004604240e00d4440ca44001491840208018105a2100c0f52960308003a505404c115500b044500c1c064601020440e03c2c4828406140d000351094031b00c00340340d0f182c03500101c6c01e0681103100903040a50001d000103c030f84175000214030919001c5c161a0b00541c88007800b5480d041201c00b03d441e40d48804011302191b2070140014241169001a10403040c0d1420700071000366030665104c3d860700c85130010940141600b100702198030150074039010b00503006815203400c400401801a40c080d5507500e00160f030700300301a8222012302d000e03c0d03c071181805540038020b018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 470257634 1250 470256384 470256389
    0x161b0506030901200711210f06102102120c060708071a010e061021150504020a0813060f0504050606010e0913140a080703050a08060901260a1209 64
    0x70120484c1600c2c0c03100d46001d0740da20640c46010000b0a0301440100820710a445111844801d054410306222101c00c204061046003c0780142c841d61801c011702d1035030184071354040b0f04004645580740c11546283e02011402caa81221070800c180e0541e2402490020b0348948203400010010701203050040d44000740100d18070488403042c5624500c201e0300c40d036003801c0c850344201c40c09010210b421440c158848185908a0f072414001880044800310701c4004038a0300d42c008a81d55550b000b94071001c50070240058401030b1425441e041361040f005010b50001010040300c45401ca0401c410440190000294004030b400c007401130307050500b400742d15410706072096408070b9611200c00e80e0383d08061a0083c45200c135001c2e14080010f460f200d848a0901c20101c202c040d000d440c1040c000110f505c4003074100b81e80207950fa1500c07142d000c4400b51000c80c001d0542841404017030010405105490382c04d24041040701000c104140241311080c0c0703006103203000280741915034440c0c21201075100c2d800804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 470258884 1250 470257634 470257661
    0x9150403060f060f1202130c12050c09090c0f070503070b16080903191701060305100609050d02010c020f120d02010617070302270403021b0402161b0506030901 70
    0x1040b8010704446080fa2410b204000d1040a030140c100942105110120521400030344040c0d03c10701116500400c48400e0180e2101040f04080f05c206103520602ca140c0c1d01c1303241c8041c4946040310310380003d080040000c05007400380d000054410711103031505050391455503014040740e48480562504c444116011a5010a02240e00130241c01c41f520500c4141e001c0d041c02c0024502d41602c252803051003480520081040c0185000c00002c000301c0d0080c036034024040c0c2d80d4005050304016050500d4580a54412020030440c1e070001c5c001950740c00083d0003030a5090030101604840c5201091888400d00402c99200700020014482d1150101c0da90400b000c46600802401d622001021150300d00c01c01c204c1c2c15030744102c0007030006092800308644410b6181c0d000d0f0402c0d003040c1440f4074245104aa003100140c10629a40c80c0c90010100604501c0c0d41c121015410403803d00341c036100c0000c040401404603129240300b0892007060b840e84402420001d00b44603a207260854000d4084d2010008825 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 470260134 1250 470258884 470258891
    0x603070306020a05270d080c0f06040f0c1502070506031509100e0106020304030c090203070908060c0c010501060e01170c0c12091309020619200d0f0201020406020309150915040306 79
    0x14090840171071030140000001d024100b0800140c48078000d9400c507810b82451071082801d000501c01c0c0801c41144520720031030181804401034504441341420b10b5021848000c0400101c00c41e594003c621075081c0c034400c2d96020303280d60350310101903c14502c01030360702c0d00002c0e42c1050010340841d0326005001e5510700c03058200c0c3e503660b07418104e07521b201e03910015100320700524050003120315a400651304183c035441c00440003911070b60142e04200c0c0568445030140400070b0041680c440a0242c07a00502d540d0601c11039895041001030601c814113100028210a07210000f2407a04000041d1240394018608035900e940c1d819070005d046a000718038051040310318910121040840d402a140410f5010700030504181a40210320308a0483d051104240f145203a000c2e46d45c18811150010302400900082002500c040000381100c07940080345002c590040000f0721040360000110340c0504002c1d184005000340301c40c0d56003081d00071040c07004e41c01410340340100710445e013400240007541d001d04801c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 470261384 1250 470260134 470260177
    0x6210309060810030623010608041202060105010e060313052a100f0f09030b0f15010c08160302030705010212010e0a09030903060b0126070224010e0603070306020a05 73
    0x203642d00300e402c0300e403081d000f0074007503003800055655040000c2c01c0040044001010700300001d0b04100540907080070700010027000800040c4122000b41404c0f260003030000d8a07a95051072300007007070003464003d120302401000010a80c00100300450035007458001050310840200c50302c0150362042150460089070709801900403441c9800c03421041c1c410002c1d29900000e201500302600c241c0168001c4800748540f02800201243c0d00750027441c0300d410744c200e10a800f45402c41003012500340c81002c01d41004207848102c0000f51810086031413400300c800d44c40d660b1821900e4200c1c9540b017401c100420783c0d400814045002e5111f540744030f042e20f4000d09401d4444d540c1d06214000ca840302e41014000880d21036003040410002c0d8020f101c1000306140910700c81002159000340d0792048403500007940e8641c8104035489a05000d51100154555920081e51444641ca000e41c5c50040c0604100d0085070740201d440c0ba0b804100a2000b103038001c10a54071008182d80c00f403d0b6400070040c401d031207400700955 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 470262634 1250 470261384 470261387
    0x90a050405010e0a0c050c061515180f130e06090c1017221208061c08090d05070e16111e031629010602060f06040621030906 55
    0xe503070580300003140920895544083c0c10000d40100d105172400d200d0100059441000c0030300c083c5105000b5040c0140b00609540e043c003803580000710001d03005c0032040c05001500d0b01c001008442146003190380581c02000c550000b290a40c41c10440c1d09680c0c50a1200000d01c580031079014800c0400d00203580b140c1d0208014410b1507050804480000383c901c2c006181d031038604940c0d06401c0038038240d030102d50480110103840024015074007624011040c5554001c00c075800002e450703002c1410f90300b10f4884841d0f20f42e0403a040200c50743c028880100810f03000314581721031100704031007a04842103d9181d42c0d00c2d050b85104a5007030310141466040659250609405092060380404048006082000c900b03501d50903845140c43d0b21107441e000800505c070888903842203800416004d0685c2d41d000002c241c1c4008001a0b80400c0c0f0710142c428500100110f0303402280c0e05d40d015010703103802c100350303695800001c0003429143c000403807922040c00c0780c9140245200e03002c0f4049201e52180b401e4161150380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 470263884 1250 470262634 470262641
    0x302030601090b131a0904140105070201110409021e1908060d1101210c0f030b0a050609240703030507170609060d050109080d0b1309030504090b1306030305090a0504 73
    0x1441030300070300500402802c120b413561103110a5002021120b072003d01d002e001441502085c0c5c0c0565084144402180707010b07900f0311902d034008116000810501c18a101d076800d4a0240c1d214a240032507001c203807006101c88050b5006030808894031420750f1522584194811030100c0d04404002840000c00500b41d0b0070005070809403070341c2018103a0380c1407547c003004544000360110440498511013541d005543c00c035000391100e4400039110345e8000c41d200c51008084881e0b14290520134601c2280c200420340382c1c2021070705040016a580d80c080c400d00000d020701144c10400340d0b11078400c00200c2d007040c10307070562050303028001da80d03154052449440d218002c420802e45a807039000700710348042207640c6028240d1013119481440082801c001d1030b150a05160800c00003060300c80d84500b80b00f0f1551402c00340c4902c40c0d81c4292020004d1281c1502c0c001c24600460190300c1035a81d44420b07400c00d59503860940180050b1000c0306005440d05c03841d00801e00c0d00000e441600611079020041717658900b900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 470265134 1250 470263884 470263901
    0x2d20010e0a14071e030227090f150606030a051003240f090b0a0e19050c01091715060105040905041119051c02010e120d020610080c130f1401030203060109 68
    0x240b40281d10f1741140c0070440c44c18448030b4450a0b200010003aa002d080e040c03021148508002c002400d800908031643d94204403250001d01031901049040110ba69500020703203400c045690130000703265441105180d646002c135000178025014100c03d0881c145240515400e203000520400c2c05044150030028003651a1408020140c0d0400c1d030008180360016409041c0804810b02100ca480e000728400700040300d00060180da182c0c00802b809405c950300050b0790740081940381052003c42006a44c0c8548401070120156488580d990200d900f6a1045041d17030b002d00041e5008109030b00303103407502c043d1014003400c1480c01001d490035804c1c032655036050007408489014164029406400c07442107011009003078224180840f1008031041d0344c85a41c481d17013104804000a000d03903c00140d0183c94080c0c0200303500b0010011120521400c80007007100c0b0700039101950740a419004801d03400010740141e22018129500e03210000c8102204540f07514120790095042d0b03451640c84400b404251035010303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 470266384 1250 470265134 470265179
    0x501060e041a1201020409110c2404060b03210c0d180b091801060504030512041202010e010903080c0109021905030c061b06072d20010e0a1407 63
    0x2c2550482d0b4246407003003500030300d038403400103142c69180d0811408960f00a29600e880080120741d1101c4502d08000200c200540d00c09140007140b2140c1d5a640300c3d0000920041c01c2c01e40b5a4082d9100340c404124403580c40640e100300c003a5101074509541419001a049012513208a0204404e00c80c010101002020304041c0069121814811446a1507010404454001e151540883c1b102c2440300d0000d8041d00f0b0a6441c00d59480c514108103141020000c214001804100300401404400848050703220f6070a02700342c0c82c81a445401650900d50651000e000e00d0000501c0c0c211403c010362100758180e2084858035504055808918444002030240b1038055000110035581450030801a003000203441380c0d080c40d020694110301713082c280144c80600c0440c00c900000b03902685550080341e40c00da5210f4081c1d04600039044014003140b8140d64001001d0b821001040c1c004400f90070000c00030700860101c44502c0480c0c5804c56a035055251340c51441d006440002c5aa0b0b0245c4030703009220b1040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 470267634 1250 470266384 470266421
    0xd110601090e0304180207150b030303010e0604020c060405010c0f1e0302071b030c0608010e09150c070209011d010f060c030e0f030a060b0418051c0e030f010501060e04 74
    0x904101d50000c181d029a0103903244000d100004502c1c42809142c425002090005622200c0764540140c4000140b00c1d10001300341091101302007620000240c80c1100c1101444162a40703517003004c5802485414a542d1040c000c40d005c000c140a01504020a00105503075230303041c09820048102c4100740b43c0c010315428085907000480246102c5d8000d061107a01952008610300401c0302c10308a151416402299090405403040007019049180c290040210391820685481d0410185e603e0b0204582254000202e50300400c803c041c500e81030303800c80743c0e003e00b84ca016540c540c103100e009041d404c1e5038592016600d800120304a01e02441000803900540c541c600708100030341d02620405d50a030105504200d5041d200e4030301d9541004001e44940c000d06000409512400601c000d56483c89107640e10100c02038a2240007520000c0c24692003100380713980350500b264011046520042c2d1300c1903140e140c41200381241041034194400d504803845501da00e202d03201c0741d0081c002034610700c1000d0383e103c120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 470268884 1250 470267634 470267639
    0xe0c07030e0906011e081906050906091b040602031c15030803041704180e0303010f090518120309190b040f141b010806030a110d1401021207020d110601 67
    0x60070107100f0340140d41418613180301d007450708180f11078030b0200c0921400600c00e04188520701800e40715181c4101c042c04030074044941090086070321180081c2807140504145000501540c00f0b000c2d901e1301100e03d044025640e0707680d5501c000c0d40e98000e44080d88085400705a0340d0300c101d51501c03401002c0c60a2041e00746981c1d01d15103d4a002d900010010703145460030170605070654640a00a00140506004200714001d1362107141e0101c5200c0c56031a2169442040144040000303800c2c0c0c002280c07070381da001054603915000c641d0204020b81040127410301c19619070307101d91021000a10301ca40c4154081b60010720030034203115402080c200307001e0409000b600100f80810804c00c18004940d000e04845201050300315511032602001e0054650001e010340c200c011035684c80010960000c02c00c9000701852299604c2d04081078080f51009441480d407400501c0400011060304a00140680300841d243c000000ea07140941c2e10484500005000c0c0c00741c207805040c02030040e85902c1c00400c0041c01544e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 470270134 1250 470268884 470268889
    0x22030f030f1701030f0308060a140d170711190b091c02030d020f0f0303221704090603060b011d09060d0c080307140d0c080d0f05040506010e0c07030e 66
    0x80c070900c80d004114003020003051408074955a00d00961013001829a07117141d40c2001402540b01a080c644102e030010010007400001c2c048111030078000b124001c06030341c098504210582194110040c4480000c9005402d201c4200703181d0001c50703019a4103c3d003404c00c84103002c400907607038000d200118034217000c006441d04005598807540c142d0350744460441c0000da0006840c2041c0404a0801a0b10400c194141310609010041d411000c2500460540c2000212000c030120360048508059160500d84010b01c20303503500c00c0344580c81c80502155119207811911026118500080c0c1e005030501c000d12106512039400c02c1a000100ba0748049071081190811808480c080c1135070741d2003a1002e00500105040120f03400c002c02242c0c00951f92699145440303280d40c3c03003550f00303200385802649181111030f400202614046034044d030140c1c4e0342e01000c080a4000d101c000700c0791003458038040420080242c001100c0307041e281c28111111a940d074401d909402446803550003000102c10000000e10f50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 470271384 1250 470270134 470270147
    0x110d03090201051c09110105071110031e0c091a07030806030102040504060626010506340302161505070602070606030203061f14060f09040b12010222030f03 69
    0x2284149002860319500740340091454000421410081da0749139180c1007049008440c0d17000950080c01d28504120f152b46443c800101390705981809642103561340700c0c2c040d01c2680301d41444800441a80031034030142c080c580080800c0f840c0703040800c13201c81001c202484250041c901d400761020700c041c50458142c0c2c048564030400f13802c80d0b41544d024000401c03265540e01034000a81141c1d0754070382c4807031005880380d5555681d51030760410380f25800c4018040c90311884101c0d29605816802c0505401d02e0000200c440107940d054404c64183d900401c80c10940c1c00304d102e902c40030b43e40988000598880c0998220b1045002d400400300d0010811900040d80c140c000c1c2c00002c0c02410002070720303550394001c80e042202c12548a00345562402101701c8003a00c044000c1e018045000c3c01c058001100c40c0401d440e8420400c80d15400040451505c25658442d004140c030030b80041c1c85007040e00c00e40f440242c040d421a0700040c8410300030304050a1441500703000e05044a400c072800780c041807443c1e00c05075100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 470272634 1250 470271384 470271401
    0x807140d0810230a230d02010207060507030509040903052106060a0e0d0204090303091e0503070204020714070806011716060311310b030402010c0b090a0605011e0501110d03 76
    0x100e03c6240c4204140c1d072128032100003442850105500c0343e41001c2c40c072030300c541c040702034900c07607070100c81c601001d030368002880c906a408504290b0350b1160300e824150f501d4020201d200d94443e0030140004100359100c07001d804840f02698034440140c1e05421680d4a44c28119001d0350000024040b11244038800c0c5a103078090003014010410841d895000301b0251092a0411307030200e41c480b01c40c072080004011106a40440e071518000802c519560740544a00c9411001f0303105c0c5030082181c1c402e01c40c0740c0042c4205d00c414441100d50f00b41d52024042d465080074403c4112942c90002c01c42060100881d5540107840c04000400b840f5080c90b03800d130010002c0d10340c0c0c00c600842c01e110015004034881e40b2145004801610324250748401c0418220854141c1c12840d0300320418800d200060742c201c5007801c0216440200c110a60f030320b03004841e140050011001d00110b081c0800001c05034854481260707424105040380c288c1d070780c881c801514411142e40103009507500c24111401304503c2035200018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 470273884 1250 470272634 470272679
    0xe0102061b090a0f0e010f15020a0803180303090f06090703030503040204110408120711011b02040e0f01140115020c031b040906090605070806040b0f01080a02070807140d0810 77
    0x501c81d2905030761084c190302500450070041c0c0c5000184a003031511112000208414a41102c0f03c0300341070302c001e4541c0209080204070318004408150f550301c5085100304078080d028200d07a03c901c1e159001d0b61381c0d85c0d500507002c891800b4000104491042c007003032800a880e01a11298910b0311607500b800002c005400d880a00a070051002082d01c68003845071002c42c000d02242d15490301c2003800d0400c01d000c10040b03000d05025144010425005902d80500c51050301150009103400003d14480d00b0102c8506004005510b0008060205002d44125a06075408803540c0700d40d0198144041c6c1c5c0d100000c418180e0b0590109000148003101031000104070303013010b000440c1002c2d03203503214070548002c0d01d001c8515617114820081d105a120081c02c0c1e01120494040c0441d46100f40441c10345905058440d041045900025100690607012681d280e80e002240c5643d504640c20030484507180ca2505402900034004080714480c420300c480c0303020b1a03001c00e001c0310f0645071103501003c00e03081c1401e801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 470275134 1250 470273884 470273899
    0x121802090c04050414041209060c030c0f080d090b0603010e0c0909010b090c0a030e06060604120c1806030b1503030a0804020d020909070906050114073c030e0102061b09 74
    0xe804d480b00d0017a038240c40e200c00c5d0591032500b07091801c91119000c400000d810014446010400568000059a10780c2d4250070f140002800e1400c00c4217500070f03942400b034291040050000f9101b0165440301071a035000394090007040d20746904046c00c0e50f00d483e00581c81c40d03005000034803040c0b52140900750004610f6000044440c510710100f1744200d030480304000501c5002c104101c40766014050448103100c00d4000e858645030610010305140030740d00400380918000c110003010000340c0070191015003000315a848030400805440303405852a400203e44030340141c404655840403454010b146d041000b0040c41c200000000c08030f079041c0c001441aa07100429003074134400350700e4a0034402e00030b44149000d04815400e01003c1d0042d0741c2c00d40d100700d04002d038688000c000c140c4128240d810003a408400d03001e184a0701074550110f50b805000072034054540704004103400c0801000c203401c044c4203865004c4119102030069840d880c080b100f58841c5282c41d9a1908001c404c200107003040c8400a2204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 470276384 1250 470275134 470275139
    0x115032a03120302120105014404050708150f0103080a03021215030607051222210206070804020f040b0111030d0509100207240f05040f03121802090c04 67
    0x5200c0000e00b102c44501090340025404103000c0d80031a05070141000382001070003540c0442e20a007400c104241c030f17104890088582e1101031040300d90061508038102d1a54106400c090505944894052181c00117a102c0c284000590000c43c90507140b14040c0c1c441e407640c00e6840c640311819507600520740d0b4800c1650800075002c1c07031100400c159010300c62006201d4401c0c141c1805151410402808000600c10244035071480744210b2140258480c204484041403441502c407a80e010f503480309402007000b14000d1103040000b81d1198604000c10759917007180c029440e510b030305540101c0241c40182d0000c0000a043c03040c0c7c1010b0300184492801032404659003030021086038159040140707403078001f1b40c41d0300a1266480080240124049508a0843c0307401140d81e10310b10140a03080d04005100d044070310540f11104035034040003800454038002c7c80700740703050300e032040300503440305000c60118220710121400708526100341c010702e0320701c00e9203255100e00c0c0307808001f24000d0040a40c0310360701c01000702 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 470277634 1250 470276384 470276393
    0xb130b01021c030911030309031902030c0d0b04060b0613060c1a010909050c04020a0923060a0302040608071806031d0d09030302100c0e0609131d0115032a03 69
    0x4000c400e42c0b50366000403042c1c2d080c40d000f0912801d0030001441b0340d0040c030821550340d80c0822080c5a084c2e605261211405452012031304005074800440c2d800003050b007060060285005509200d1886500104800840c4a041040c0350088004a0b00c0e141481741742400124000d19060744528050a280104000411454203030200241c20112215860303052180400108000140842d01304031400d40c01e0000720680207020326158856000c105818001404941440c880c1d4880035800150100c1d0f6201c10020028010b9480392041e240010040e20008030550701c208401c5030000f008004e0328251500d0084110054120f10031504c4820219464401540004202040003e401078880500003455401d029042c03a281d11180d0b900c1c1d5040ca050300103065030040b00c006044604541c1a034a0704410808101e02c007030b05900c0340181620b010f8600c804200700381e0035082801c0002d40244010348525620702d200c00d18500c001040e8210003000000011514500d00d0b511050010070b40003800d90380d0b02c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 470278884 1250 470277634 470277673
    0x70b09061c050408091003060506071113090f02010905010c0f120504050a09090c0b0403080412060b030d02150714090603090312040318050a0b19020309101107090b130b0102 76
    0x908403507841c0700003036109860614003504540d401e01400d0400402745010040f40c500c2c030410360020400c0e01c2c40a007880003596000702074001118040d00402c1003000030b00c0c2040c1d01441c0040142c2c082080c0c0c0038000381c20b6200e07080354009680e21800d0107202410540e43d00300e01490751201401404028400030501d610b035541100300400600801180d1400c0c142415642804180c0010010a00400051010421030b00440c1d00300e404607800d040041801d400d20400400c611101603926024000b28860788982c0000c45104075014181c2400460b142c010003034922a18001241c4130a000503c0403c075980350a00203913a0040201054a1030404100708401c4421001c0310204c000c03448462138207411501007c10700010b0541900d54595940c101000b0030511300449840800c45001003401e1800d10344203006544a480c0007411040c4d5503403480c1c50207804861044010150346c030038072100240481190055411041029014100030b216501d103200190501122070b0f4158402d1401040d1541041e00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 470280134 1250 470278884 470278891
    0x20a1b0b0d0614040e0703111804050303090c0f010c02010c0f0f080d060f0506040b2a0c0108090a02180901140a0e0c03150a0b12011d0d02070b09061c05 67
    0x180001d940b42881d000207900d403c0c82c50203034007032480e10000403100b010024a150541e6080851103112400c41400618440c0386484aa41444081010300c020041c000003e076019480050039501c0041100303040c02140d0799410400c41c00101109610000340d401500c24a440700c0c00354880108600203a100d10030b030311278024421541000300140d04d0001161620804001e00fa11a5041c08110310300800280c4c1030045000d0f402c0d00500008040101d10581801082c41c005000303004141c10040340036044d122042d820300130740441e0941c0002007288501080c0254000e0740184450178005ca01c50314124403041c001e150005944d614038002c900c5040d900b09081c41400700d60350220b808040c0e0600281001454a40d86000c0c0c0e0150100c12010342c5500070b1140e03c884030030340000d1000d442030f0016a0702403031007044482c4c5520300140107904254900d440d100d4403000d102200d105e0700c07507444220703502e60441c40348564171001888000040d25001c1c00524240c00506144007880c0f020781c00c0e0310b04403031069 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 470281384 1250 470280134 470280157
    0x2f01022203031d0102070605030612070b041a0408030409020703120906090218070807050904020f1210080601060c020d1121060903040e06040905071d0105180403020a1b0b 75
    0x106040080503441080314207012041c00c3c560019903603080010356101c1d01c1d070080b8403d000c1c01000240098559214010780c11513480101ea40c1c0da130342c4081002059100340508a84c00c10780241c065603500d003600c111012070315010002d40c941841c10307002030008d40000104070100324902a4040015070039005a00125010740400601008030f88100300205000d042c060a076042c54000f0401203030f4121040c254010140d0034103035942d03224407002500a01c9959104c80c944107003c00c4224107140d402800a204031001404c10b10000e840703084241d542d01c1f0034031500001803040840900141411803041024500c2802411055032810700080e65600c17031004003058911894100d1404040b040128640200c0201c000d94035044c2021090710450000420301070049032104204001c0040c200040e40081ca0030b0f0480c032030351900710305800ca905102071040a00c41c1c6506e00c2c200c03116402e0f8943c054061030b855002895051169540c0f03545c01b003281d00803918408080f400001d070048107040100441c0705e00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 470282634 1250 470281384 470281447
    0x10e06040524120129090d110a0b0405030105070309021005221503050a0506011d03070e07050705010b010306060c0308181f0608010501080304170705030a11040c2f0102 74
    0x145170041c1480c0c0114138641201c0c24420312040c1280c0391100440d040c0d0f15082e00d900b0f228071382c41e080c84880500101a000d40110001c01c000036005014030241c01030300c100314003d100c15103c3d801e049052300c0008002030f50100c4480e017480c2000307002c0c8006002d40c1c400340800c12204201c180301044881c1e000da00c09a841c20344280c0304640306038584207003035101403100c104100ca820424002071141c800307030b05081c032000302c1c0c84142d203240d540c1040048000c10040040b404940340c0600f0090080c0c101900c200da00c1d40c01e00e00d5400d001e41c043d00965043e6207490750b40c1104c0d820140c5044920660150424510200c489031628102ca030031f120300b40303a007001e510600500071507001e00d003022038085c0e503c81032940e4507240040c07107140305c0441203c044510402005071404001c002c41030610070107a01640e45841042c8041c810028220945800e21a044404001e10813600c1c409880f80ba194211040480405203200da00e4815448a00d600341c0302c400d000103040c1038020038885c5000311440103c2d25000321 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 470283884 1250 470282634 470282639
    0x706080703050f0f060d081207020d021006060e0f0112060f0f0f080309010e0a081b091e0414070806010902040f0602070317070609150911010e060405241201 69
    0x401d400b0356030700240071080d4603081d494003240c0200245409030200b0320a0800c10b042e9400c2c05240d030b05030f42c0f40f0320b40260761203907500301300c4400303903035901e94098140260250740204283d4440c0e512945003202c055807610003604120780200003500c01110030b034605004200c00400030740c400358460709000c0d050b405d8a1a07551400c0101c0e07030011012036881510450620501400950000300603204904802c2c00c042d01314031029400a007140038640c01001007131003044181042213140c509005011042070f9018040c640b1508541d580041249440c503041012400209000841c0016134000822085043d02c0d5402d4513003481a06114083e440f115440350003007020300c4400c00310791810380101840c0c00181103031841e541c0c440385d40484010310480c4003940400d046092102c41e81004681e5071340030b10300780c0300ca404034074042005054400040d070f4420b46420100c0e0055010f0303012030b003e841e4000c0280e41800c0c50700c0c0800a0418010507145040000240d1020720300b9136420203401c582c408601102150360 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 470285134 1250 470283884 470283887
    0x6061c0e0c060f040e0717090a0b0c0a0206040f03090911070215070215091507050610050306060307230a0b0703171b030421020304090b090c0406110f07060807 70
    0x310190300c0c841c40b80b00c082004511560340d1100700e4046901c5001504025664204c09444030380006d4401119100d2200070001d2a41021070301466151089103d09200e44803110401147d0260900c18009a40001c012034040762200c1228000503100346003d9299071348420f40001a100c1c8101c600d0031110020400d038046192030b040c81c1a44e0f01c0c2d00341c80b071802d07c015070300001c2d80107074101c0704080545400102e8041c0d98030790714001607006a405040b181d07240d50a141c0142d460000719400c1c10a0040d441010807545408500c0d203006880050080811a04003240707052038541c003100c3c40e481a0210020b0f034409854214512004002500c0c26580700c072441d0030081c1008203018444800c1d808010308000c020303555060400c0241904650254072a680e502e0001d00002452000c070284090b0140d01c1c1e0401d9070700000500030380f20303c10350038444900c043d4117200c802c0745c01341ca0b5406540781c00d01c81800030310710a020000c07280c9840412283d000c0d0358805000d00b04100c0d6005000000c04c031030200082036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 470286384 1250 470285134 470285143
    0xc01111902192f04050f0712090213020a020a0f0b0402180c0f0f0c061f0501031107110a18090b13030f030e010b041404060e060c0405010806061c0e 65
    0x520040403401060007a5a4500c0d003120508240046940c624020581983c03802001c02c480f040405802040b071400c14540e0404c1001c41141d030320380020341c00340c00d04440d80d0070b60180b007600c07680c0580300001c10b000e88c000c2c0a01940190b002c882c114484d00c0800b10110301c0c3e01c140f800700035006801b00f0100c0d0600780148502c1d4036155565020305c0400c0d105000c0d80c42d4100d03007110f444819684005890b4100c1c0022610f5070310500b010f401d801d1041c841844007107030310021006149044c0c01d001c000056039450042d81503580741d540030140101c00380b04680104030100b4020869400003803250b840252119170403c09101e90368140300c0d44690f14200c1c042007104100b0144c0d08505107003a00790307050195540040c400e40c11010100e00709501c1da182c00700111425000064070070030007001800500311040d2546c0001c40304860558540d401c0c00c004000c0c541010451601900082003580d24080c1080c00650b0b015801410ba00e4001108001b0110f008018600c41e4140d0410000046010f003294011549070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 470287634 1250 470286384 470286403
    0x2070c09050702030a0c020f0d24150501050f03151c061503152a0c020f09010609090b030a080f0d050105060f0a11010e0f072108030c0c01111902 64
    0x1550b00402c805c540302900100039405280d4100c600b00240c205000124105942a82004024a80a06811180f80301895502c0c144124443e001c0045007688490381d10800b0141c45494080380040004960f0003001000450303010300000341007803e022545000c10304031100940c0c02c00ca681682401402084000c2c043c0c100c102c075041d8140e8254900f1611403201c00a2200c14040d8496521600d184100c07200b03c40c04e01402490b840b00d4080152114805059941d0414040744203031882d404202062030b095141506880305503840202c6075003402c850000810305400c0060380b601c10040f44c0740014060394001c1030030b21000c0c007245456a912404150136100103070486841402c2c28400820340301c03840000e4030003030b2038240750281d940c040740c10744180180712507016080c80d07004110040c6540701000541c18121a1000b000703210041c60000c01c500303c5292000014800a820400314000d96240400342150384880d500001e4a00340100028021b90f0002071210103002c01900440f00258040c03200347e16 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 470288884 1250 470287634 470287637
    0xa030e04020f03130203010603050105090c03060108060702070b0a09230f09040b060105070f0503040b0c07090903050a03090219090c090b16060c050c071e0504090b0106050306010e0402070c090507 86
    0x52802d000041001404000c10365814480d8540b00b01003550303801d420240055070000020030042c242944495100c00c0c00305072403402881500c00014141d00000b800758414186503002d009007500b410140b82c0c9070b40c00b401c112000c20411560208504030642140c01a60201e440b640019003490018491441094600c941c0700c0c941810422022400044c101a4800c0d400d1030100d540c1c0015180c40e1280980f500c030003501c0c03444007040100d000d01d0004000d004010b07200c0f0450705002d9613600040d080c2d50f00c6903070080008000380043c6404d0790103078100641c0d162005101207141e1f00c00ba0b8030b01d542002564442c0b01c0c00c0d503c60b910480005d8102c4030050103003c90194180c50136501c110032252040682000504a581e07405400c50018411426601c075a10340c0070a513990903641d400300d10072041e017007030340090020840c010006613890301d4466224459440b686100c020383c0303130040595483e00002d0090781800300c2c00b205400b85c0d5466100070302807940320711610600d8905104100d002c41d20700a14800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 470290134 1250 470288884 470288887
    0x8190509120f1e0a0605010b0a08062e120f06090f0b010917030c0a15050c0c060a1e020f0d050c0309120d1401060f0e090118050a060302060703020a030e0402 69
    0xc61280c00800d5044004202ca42c000100001e01030010f031900851351409841c0a18000002c00d00c14048401001c0340c1811759038600f03450b110740c000c00120704070024034280c00841d019184141561030180003c004102c0303041049071103148140c2501955518110101819035070341d01400030768980d2141c480d00102c007070020854107a040c0c1c0080e10790344035070090110011448054034080c032000c008070381c00d444a0f2010303588114514600300c28590441041d12080d5400c00000604c1c202c6c0c594103460480700928001d10f40d80d15014075420051520b1414021856034262070225042c2e0180020025900c00c4503005a44040d00307003641c401c840000d001c080d0400810424816001c1000900d101c40c000201d10141d6107107815001da10051000038918682c26000300300001e86150010505404440c0d180c03905055090b0000c100000304401340103544800601c0c1c4200c2010380f1142c1d1095903c070000810010b4140c0d10707074000640079007007844100c0069000c00b05150070541d1000701400905000d80d82075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 470291384 1250 470290134 470290153
    0x180309100e04020403050d050711030d0f030207050f0715110a0f08030a02091509130e06072102040801240f09090f0f0501240806130819050912 63
    0x6104005910034003007044034078202000c00d40d48660407a0000c59000c030807100342019001c00a003250300000d406868104040041180900707001c1030203040c000d4141e03941c02d440c42e8154810b034000d40028005030b40c144120f034540050328070200b2086000d0040100c802a898090050040c01402031203103c5045030020690300c8001a0300b600900300c4c41d503010305801d441e45c0d50305408500a00541c2c45440d80041d10b900d101e220301010500900f0003440541d035603044401c0d5a454502510648804104207600c4540061303007051040c1c0c18503000300401c2131074004114680c842041a41c0083d0098000760f55100b4805c800301520424080b030508034040120303000c5140c54001203c021980c030075003032040e44800c2840204100521284902030f0b101160a1413004941030950080420130448106408600809030503c0c1003100070108841c965401441070341d49130540220540b5000e003081325100c10500030003039408400340100c0542c82c89a904c55032078085480c00c01809074103044528586030008d1000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 470292634 1250 470291384 470291389
    0xa05060405150d0227010203070209061e060f040906080610060302280804021e031902010314010e150405040503090f1201020a0215101203080408120c03180309 70
    0x40d00d0464100b151500030040324100d035510140300c0c202c040c06445100085003800042e03c905103e6a030348203d1603c2522004039070042e682c2e80305040b4043e5200c01418009640392920250b04030350020f0892004c6410758904010580740c1e000080d000c1210440030401b80a46001d5208040081c844200101514288094400b288201c0f13070140c0c10030150000364039200050654400d07070a40039185408850003070802001070584030f041d1003c0f403040c200720b101c400301610302041e503560706035000f0040c1c00d06404164245001d00c020620803410b16848502000740c504000c800315009120784515400d546c544043c04034800c080c048031342c900c0b80d468036080c4008290300105607408848107131040503109c8400070001c0c1c248803d541030300c0d81c00d40c00019498540c960200350788043c3c44480e81e950341a07449141d02c550702030801d40a4200206680c101e681c010901c03c07041d4030340080c01020054944510400e003e0071050040703c034488101c0d000014440940c0c3c2e0a40c145c408060214055070a00404c20b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 470293884 1250 470292634 470292637
    0x5130f08090d020603070816030c090509100306061203030c02010c050909070c0503030903040602190321021e07030f0305061f021f061509030b01030f050a0c0803030a0b0a0506 77
    0x802408040d00440c0901c2142c03552000c807110325030028101a200d2422000c02004010204c9040080c242c005500004140c028041c2c02a5000c00340c4401c00210b00300414403407800802003c2d40c50f6040030b508000302041c0a445101d019000c9a00940400b41407410003405031600c18041d0411685401071012a40d54804203071a80304008032240c143c5500c41d01c0d002c543c1c034801c980b40038169000003c28400303120030020040046803016026070b0301240441c41c204000c07003d00000640407a03030094889030f00c030b00f10030829a0540d90a090040c00c2083d900c0c0d600c024183e0100000558140028401042c0350b040445600190918581401545804000300740ca0840e1460390700852103e20282c01c07040b50080c0200031560800b0100503003002d0071010650080d20395845a08040c4c1c4001d000c420f203403480364040b24140d0750000094003840c0d1035075441c084034001c44181524680030300128a0002100f080100c001000002d00854490030310420880445012680e064420150b4250400c600d81341c210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 470295134 1250 470293884 470293913
    0x30601140a260d0305012c0a0b12160906090e0715120e0a030809060903040b16020909010f0b0307050d110604030c08030a091505090d06020904060e0105040513 70
    0x800c1c0406554107003800701000c9158070751075110300510f00070444055040c0d001034100d4040310164a01e02c8a02203440c4041004400700f464000c2241c07000400020564000300c1e6404009800000703400d2600c15000e0a1644500d1010616080b140d410004407546014400103803146403010070880000400c2c0c0c03961544030744160032101d254031800301070440c050201e0a5403074001c2d101c107101e00300d0200c00305500c41e0004401140450a10790200303032020380006590b480b030203c1000652505081146e403111540040e95040032421a90000f800140c551080c0507001311800000441c0003804c49003290152009421164000c4d40100e600304142d0395010050242c040c3c0107981800703040382c00c0010408601c07940e000902459140c1100081c4198004014a40028181d580c61116a114600700a036100c05100010004109206001c039514100300e411110074410b4500529045040000c45c0560b0043e5000c600d072039801c4401003040c0d0402e409000d922180380e02a80b00b03108410b40d03881d203045501780c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 470296384 1250 470295134 470295149
    0x280e010609060e0f040204051809070b030702030d091104140f0105031902130b06030702030c0111120106080718120c080a0b01060c060902060f1b010e1207031803060209030601140a 79
    0x101e0b8165074417039604507805090050003078550740210400c03a011110090720b40c0c0c00d2074892180c00291140134001035900401d1594042d42c40c0c501400ca0490242107400803d82d8400401c0b400740406a496202c0d44030f44810740818900140b034080011114004140c0c0070324002e40118010050310141c1050113000250304803203501a032400f5200b02401007480c07410b840c2e0440000000d00480c00d030000301a001c2c00c240c2e10002e001c0707900640c09503001c50083c0701030000f0500d03000005000c614041c40c40541c1c014000d143c5070807151304c07004419414242540c000721070492045440d0061040710194000541034101c0240000c02941c1e594007500c40c2e051041004208005a0207000c101c081d4028580301600140382300d80300e0280175a0389900d58000341e070106200c0803040c00032111550601503410021100c1d4003902c1c0c0c20641104a81844c0d1201030308030100050b01c220444541c140310b144602550040000580300c03401c1e03070107040c5006010b070410690200206200401940e4410508d0241c0d200c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 470297634 1250 470296384 470296399
    0x90b060904080f0c0a0204020c151302030d0809100c0305090f120a08060319060209011e090510030e0105090d18080c0d032f0706050406050d0b280e010609060e 70
    0x95001d807400c2174654007000b0b5025000240802c4400710010307019001c45984010f1300312544407000d100c03102e00c100140c001c3d015003040030000d00c858001d114540e4000f82d44010b8130800c580c018010b100f02c0c0c8000b00c03500d000c17907582c01c04d20900c00000c010011070901441c00400035800e0162045549010b100510340400802c0800503040c0c3d14140114000d910b5040140d0003041c071145451000b1b500804801030014400400ca43d03c0c01e10251118415040140c69161010b420107084c0304036000380440542c01d043d04c40305400340c40c1000b4865184200d050030054480c0403050030300101404000310f440035042140400601007000b010a07000000d043c1240c1410000103180303010b51b0030940c500c003042841000c85108500043c25020b1006498400d80d0a6601460702c40e0810f84940c0220301862000074018084c2d4880e07080240d010300c20000004100c0c51070440d031842c0b0403480c24111490704a40c52135405040200000c0490002d0150205081c1420780b2410000000c25901d4148840752281c0758 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 470298884 1250 470297634 470297647
    0x15021f0e03120a0609050705071101030c03110403080409050f060a0b070f1203090309080102180418050105010621061d1009060f080601051c0b0903040b0a03090b060904080f 76
    0x70000c9903000c5401041c2d80c241c03440c2c80c5070400020000b034420070142600b86400a505144038400319201968031100f1251031600e164011001041c400c500d0380c05059440342844010324032180504011762180c002d8030f40c0c89041c080210b0071b42c1c1c0b0103807400c0d20390302460040c014682c2d01c2c0d800040940d83c01203032003502c0d0308250410540003011004064400e50864408060703003540358100c0d09000d80292138031805d496588030101d080f841500c0b544c900c0600701c03085891243c0b5041d00000c0407180c1341b2503251940052a1100d9085400c2a40f10501184640e22021083c0c1c5000003100d01165124208114040c44d1a00d45040b078007007110158118002032000524120345003914038041c2600020402030309460f41170000111105000300c082e00d21401e400010f06192400c0413440103510200000100d0950f80d941c1841039401908485c030318002844040384182001c00035009040d00399801084000c61070078454902600680001d016080040c10840401c500808403429208060b100710b54624 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 470300134 1250 470298884 470298911
    0x4030206340f020f030a0c05041a031c080f0601020c1005070f080d0e06060312070203120d06090e030a1403070c0b01030b04060e1b040b01090b0d050115021f 69
    0x284980c0565a95550710072551003400303070758505404070307a01c03e46151080d0300e44103040640d41c1001e0b40c0020902d454008040c803040c1841d801101048445032181812012403200080c00d002070035803584419020400000325259001c082c2c9508030105038401c4a890802c1c2c40000d444000c201c00c00d50244102898428601c0c3c41b4004480b803541d0088102d0728070100c14507100304c8a51100c4070b581003850400741d040a038800c000c01d00500841c8000c0043c100240c26a0600d10160400ca00c20381e07050040d90001040d41c3c403401c000380441d0454120004800f401c0c06541004c82e198200b951246030310600c100c014036504614545a07001700481204c0e1071f9980c40004848100500c40001c1c60200500c000004000704210890301551181d002408540100034840c0c2d9207a903542e0010101000c80468014181066401102c0100040c5400300741d660320783c5c038010015885145144040b0359100c00400415505401c1000d0f8600588003400440010920b501c4a20b10003170a8009800e07958a108400752 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 470301384 1250 470300134 470300197
    0xb0f061c03050a1e1d0109080a0b04030c05060937230d0e18070c1401060b040305030c01060b040b04031506090903090f0816171006170c0604030206 65
    0x2100700411103900c400d450134008000220034644984800c440c1d03424581998010104041034031213080c0140342d022402d40720104020405001030781440301042c3d101000c2001402854030a040c0100249885807080c424850714074424540d00061801d0a1204c004110b56030030010041a0000c3c0aa84410601c0c00f040e08050364040c0255058400c88221244e506e800c00070200b02c140d401ca03030444900e5000c0d908441000c0f411140d00c0d0005030f0100c590b07000104281017a5004000c1080009950368841c14004c607158400e420540e1070703038804510341001c41c03c24050000034061101055080c00e140c6186e0404600440c00000d0501c0c9010b1a0320000862542c0300400070201d4050038800440e01d400c1c0075064407000e015504910f8152038000c42c00718000104507440302114403038121441e1600b130399640348114240451f0514000c1c80850301c0d40d43d101d80200380207403000310742504810500d001c0c558603245211303d0441c000d50f0103000c01c00159071108107440d03505002d051004201041180103400310f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 470302634 1250 470301384 470301407
    0x1a0d0203150a0b04060b0427020c060c040323061503011506030b130506060a03270305040602070e1509040309090e03030105210a022b0b0f061c03050a 66
    0x6070302240003008001c590700c0c0c01903039503020155000c1241c81d807a40500c103ea441103028801400c1005210800021030301a0304020910b901e82c0018201500c1c0c0c6d441500b8600f080c1d0704005c0c000000b09084c814414507194041a11043c00d0780b000300c1e2400440790310344554009060f400e13080b8400c04e1f07801c0301c4e4500b904504501e01000c054000c48035181d4802800030300e07130502e8450085915500c2c034964080c540c8141c50256400425840c01e21201080440151400ca02140b400b90544104014001c0760341e008100c00743d229444040e140ea04212000b858820705910810003040d8041c1482221403541400c96400201915442103139a1582020b9039409007a03030040304c40600d001c1000c0310080000c00958140c4104031191010030b400003584007441400c1c000c0d03642460304551002c00062406c1202034121143c000740c1d40d05c903145c0140701c016548045400646014501c5420021200c0748610701690004088884110010844043d2104504010001010701c040003a6254056001c2c9005000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 470303884 1250 470302634 470302663
    0xd0608010509060106030c02030a0518040e0604060506130b01080a200c0304060e06181909090b04050d0206010b04090b040b0a03030302091302030c0a0c0f0219080d031a0d0203 77
    0x155040a442d40d903075a01d000d00c00c900c0000c2c1380c8444004101d2021040310419002c55031500d003001c158001800142c100c05901740e500c41e07500c0c2c502850f01041881800e100d28000c540c000340c0e51600000b88081c60281c00d4000c1100c501c0d1600780106682c01c51300d800c0d0020090400080d0b0b2046001c5202041a007880350119940808280001d01a400000400644d0200e948035460007154a060001900804200b842d8078440c0c08807001540c10021071a10851980311400044180e42e280344008880b00100c1c1503801042e80410032050100030440402802c500d403008200340e40c504226084540954090881c446456081c085004d95881c0c101c07800300c00c0010120340c00e5a40ea490060000d500000a250258070741201280c0fa4100031f2094a10401ca1081300d546004100301040700e41444040084031a60301c0c0201440c050307115100e1954422103400401100141050055460403030061446330405090903811203880c0c3e80c0d80c0c00f401246809552640a02c1d903030303100107030400c0720701c0303101c3c08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 470305134 1250 470303884 470303891
    0x1141012061503020a030c060f02030a0507020f18131e020102060601050a1e11010b0d0203072d0b12090109021f2309010905040209091f030b090601090e0a050d050d060801 75
    0x11f1114903440d50044030314075101c0e81901e86040006a80328010000c64174042201401940c015007009142c086a0640061010400034144d0b4100d044000c0180c642c80b44c2c104902c4006000c00041c1000000903041031404045104201c3d40005d5541c23000038480b81c100b000100e0b050008a005a00b0307841c00c00028a02d4071080310708103100501d030600004c6451110f60030007080044030b00706100e545a2654018024100d52428140d03a95410f182d8034900c514000c241510480000c0104030500c006006107802032580d4901103031160350030003805040151981d140600d90300050b0b0b1040b010035101c038100560380d400010384150984520810012042100c44107502024603040104010296400b0903203c0003820703a01c07001448124011800300369001080e2a001c83e61100280c80800b080c20395004815840c55142d07038034501e1508050703420788610340c44803005101c10200c03409483c0c8228441401007001c0c10322919015940c0c01e6441542e0300b40440040d182c252034003150060400340c8107450091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 470306384 1250 470305134 470305139
    0x6180703210f1d122d010c26061f030501030c0f0f17120a0507060b270613062c04080a05090102070509070201141012061503020a 57
    0x40820940c484011000100105403002a4a0140814100140901035540c04918500c0309002c0c2c4840800f03000050b0344135403102c1030681810b06042c0580f80a48a00e622035011400034102c6c29900040300700f2007441154070740c1048107001e2100d2004150303041c003400d10990b254140400da800d501d44884450001c12408940c03440354054000d03a04903403041c200c0e211030540e5030448110308030903400749512102e07400e0801c0010041c1c0064890300c09170134405881103184104042c0000327a1214001c0d00210340041500c50030b00450307102d054100c2905840c1829040996505165880383d440c400300c5083d0201070218045885090048442d0168103404000c555180c0d050b040d01c000300c55040c41d41e414018101c2ca250090b52140b031501450741300f51400c1c2040c40ac00016201c2d0f0f0800d100719411803251040c0001e07681d40d03420506004041c150000200c420040c80701c1225410020711000d640c04101000700411201d642c2c01b082ca0580003c000104c1e07801e03580704607a0f26102640041d5124000f003801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 470307634 1250 470306384 470306423
    0x10b011211040b03270706020d0809250f050619080a091725020f0d03020c271003020307061b060504140d020c03070303111f062606180703 61
    0x5041c003583c0e881c100d184400749031105c199907504c041e00071540160425074540c200140642e204030341001586065503482220305940c0c894081003000c0c1205020002c0c00e08100f106000c00c80c03503018040c241d55980c07914036100f006840c000d090620300002c0001c220005410130030541e004000d0203901c00c40443d01c4480350014100740e908482d908010100c0e410a01c200200700101c0309003200c50b405404d4004941202d010071403102e03010481641035000d00301c41c040309070f6502500201e541046400f40121001c01a64001d41628010141d60400a109405002507030f4001940341c00c4501034540381802d10a40f103020102c06109100003800d1909200030701c410803c4c882040c1c1c03002286a001c40702c46608401041b652512103650b00380d01500807100600c0864410300d00355000007a0001201d840039030104c5180355880301075a60040145e5282002c2c460741c040403108000400f440b002021a0740d081d00700540d00c40d00c1c054886981954090128522441d0600c0510000e680040380e00700c3d00c4e243c1d4040e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 470308884 1250 470307634 470307661
    0x1803100204080114060a171011030126070312020307060e0106141815010c0b0f1906180504030c0804061815020604020d0201030e01060b070c08010b011211040b03 71
    0x160394043d402c050301d01c144803d020040911843c8020b160525440c980011401250200003100c40300380980001140512951301804241080c0c900007103682e0361500f44144a000c02088981d00305291000c1c0e4560001c600242c104242c0350409001400780400c01c030168030f0341c844c5e003000130105401e0014503400080103600c008102c0380300200e0301f0f0203003182e4410000d100040908281030001c81c01c02103904190000003111488c0418145806d01245d5902c2d43c0100440c202c83c5101034030321260810440c0741c0340740700d0020800c0c070503c0c00740001802d20340c0c01e19521a00303201030380ca456a14000503050510404042c200f0702e0b013049105542e00d4031101c00410608840248400c1041e0901300043c1d00102d110380c030724600301c2030f502400b0151120b90800c1124014140c0507070400d52111801d140000b82031280100a1514140140d0b56504518212249003041c0d8070a40b00ca0345450858200d40e40c22a0081196000015000801c074110604a8000f07000390b800008200c0302c04170402120701c42c003c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 470310134 1250 470308884 470308889
    0x8070b07060606090602030d150308030901091505070e011103120408130501050a1d011101050a140f1b0703050705011407020f1f0e0c0d0b160207080c061803100204 72
    0xc07414000103803a02c2c002d8440762414452040164810000090001415440302d0105100002c034900e03c0783c0d0342c1e1a1a82190010344584415954030141842000074202d001440043c500c2818800c500e0544806090050b0550845050180c1c00c0d5031000307810010300440c0d0341c8079181280110941040c3c14290700030380060007813860241200c900401d06601410a44a10394410f40e1805031503180b0001c0009103141500344a030501c00541c002108046080c000d003403051500d80300000ea01106007a4400703007001c018180940c00c040302c03c140010403107018441c1c044003207291000b9079030307214618080303900d845521405400340d441c08000a44040321115014080e0401c1e030700701d40c2d81d180a401c0043d07d400801c0035030b401c48a045d4440c0940080340350042190381c040307902034640c600210030102e0003144104900b110000c4140081001d04505208103400100080c070050034120308080c2e0242d82d40f0403105150303120380b0000c41c090414604200740e1121002c80a826208800402d0319030001070b401c84e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 470311384 1250 470310134 470310143
    0x10902091609080a08030c09040b100206160306151421190509150903040317070b1b03070e062b050703141602070e250e030a02040b010908070b07 64
    0x10a40066001e8001a02c030480e180c101d100071b451521109204e00311503012003081500a920380700d28162541d104440c01c045002c007500a8007035450017000228250100d060f1110038145040001e20aa11070712280306074102e41410311903504164651103038001e02503440646c40c0071b41c903158078803002001d408460b80181300540f1a40c040015846c070310015220708540700c0842d03900c0314a00c02c804802d80c030249030300805e20308166441e154513a00d0b88a19448081c08050143c0e00004c0c8034003c002d2425181681b0282104110094141303101441040d44070140c200000c0240c4c403e1100e00d555903540c204c40d00d203040c03820b00000b01d1081011100d40d04030b211040c030345070500e0080050505402070094413521400c4100d85040b65490400300d0243e003400140310300031880bc2030070100b0320100c0c035003526014020a44035460100062410281c001084c11000010421440b40602250710b0024138049125030495020507810540c6d801251908200d601290042c0306004000400d07050800c024404180903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 470312634 1250 470311384 470311397
    0x1308040f090c03180611040f0801020309100b030a080711060a030b0102010c020c0d240c082a1b010f110705010b150f0d060503070603020c0d0e150901020109020916 72
    0x140d2800783c00f1101c00341101c50b8005800140f500000300705078440781d46144c1c549901c0381081e4a1f00402c2c030072005160031100f4684e40c008148201e07014104110b0301c01e45000c1a05201001200c00429182c00c5110f00080c105440414500c04103d0301181e00c0e4901000684220780350758480c5030080152090000d080c0c0554648148200768600c049540c07107400d07101814141126500e40d440300c41d007190146011808c01d1302c100885450003114040e29100c14a2551600940d040c2002e43c8800c0b581109109460700340411255880b000541c015641c542100c00110940681d00516450142413082070b0415007a24000c9208140410b6201602d0700300d00070720003004640a040c2c180445882890000b1a80040c20304c81e0070190103c000041100d000308a070041842540c40000c640740051640200001ca038010913071440f11181007044040b5208189010400510294007086140c0c0300b0015007441483c0000703411400343d000350014107040354050100b5241f85000c1c2e2141e0200300500c03160400007410b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 470313884 1250 470312634 470312651
    0x1512091b0e0f0405030307050d0b06030901090209011e0e1f1511010509030906030915130614060d021002030921010b180c031e0403032708040902031308040f09 70
    0x10284280c843d41e840030085103140c44212090b03c9581120301c40c1b030702454584601401c0d41d202c2c0005140905a20400400d010075107104000940d14140c00200010344e030200000041c20070000807008179140004c021015840b00b004021846010f507580c40e09140c0082c2d4002200000b8040600e24450340d03030749001c03900c01d15582442c20313282c0c02e0b1520b900940c024880514a450032170000c0d03400a503810100c80c2510b66a001c0b003c1403903070071203500305064850b101031b4003800124001c46002c85603a00401d04a482e00314001000c40c1403c01d00039004450201004060a0080045440c0c41c90000c08003102022482c201324031161503291070070465402c09103841c1882c1481c011842d041441800300106aa9524a02152540006041e030225a0707490500b1000b180909400324010b600a640101d040902c000c8c1105030245110b003101c01d8442c80507441e00100d12500f083e101500d41d40b21025030341391617550710315860041046000c0d204140010b00003079240700c20907400b8102c0d48078005c144424007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 470315134 1250 470313884 470313901
    0x180e19053405090625030507031209031d130609020c0f06010b1c09060203091b0a060c03051b2d010b130c02012403030809071512091b0e 60
    0x407514820310002c80e2060140942c0381c54001c0c041c040841c0e9501d4801c5c04d41120213400340302d44250510a42c003059000505406160703001000340b09140040ba01403090345d1640e580106010006007101c403040c6c20740c2154003225603940641145002c01106c090112540f20100c0100941c80004d284005100e91030400030181d80c0030444a048400c13851720682802c10440070f035150b14280000d21009a070b0b0b07403a201e40c005140ca1010318040c8040310010b210000d450b1451074500f03c88203428601c525002e480801040d540304401600c0e841c0d16240954981d054240d03d400c000e200340c00740054600030b266a1346540700c0101c180c2c620a0f0007510030010740031b65581c4d4040c00c035024504565005900d02498034046100f07a000f20030769800318800003445074604140d188247c1c0c07011705420840c03040100b0410505900549681d081810880900309140c43c0180c9051020f031600641001c1c400d00c08081d91100129611120845e07401042d6200d180e00c80140703901003030030603001d19501d10345a0350224503c2c0303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 470316384 1250 470315134 470315221
    0x2202180a050d0c1217040b070b090115060302090d0605070807080c0c0604030c0213050c030901060b12040b0711030340020f0406030204091b06180e1905 67
    0x160700440360705520f038204200e07407501040e00c91096985596505180b102c43c2180d1000384000c242401085490300c0d85032900b12024440900f042d041c9a0510a038501c11101e9008e505086074880d09005079595246400314014602213000680f040f0314000c1040ba200360042e40d03891003024680d641074a0341d80d88180d40703403241c0510301c0303034680d154041800100000e018181e6001506d0000b0032146c0b40b070a00481500946608a40c4030b40b510380d020040c040380e00024000c4c1000382c50074001c20b90130042000c60346c10700e41c84014409410000e181c404110340c180a4818904820b82c2d000540e5075078905440b026014655001c1110204041441c00354001c010b0649010700c07504030307403100d07a45204081d001c000200e08240403065001350340b0400040181c2da24400c0c0702d840786c402c060381850513210780d04003070f101176a55001c075051206216036001d40380b500001c05015140000183d46054903103900354003004415404580000d46000c0a104140b401c210015030b96002541c01f524403500d01c6d04508620 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 470317634 1250 470316384 470316409
    0x5010513030c33020c100306080d0201060816030b15040902060309240112060510081902040b030c0105030c0a17180c060f2d0a090f050612062202180a05 67
    0x141c0140200911910340b4074401c2e00c01d03401b5850702261301c1e5140c0020b68100301c8450b2001002d0b0f0f5503100100a1220240513555070350020b03000e034506845ca180c4600340c400f03000404400c0e102c0c51086001d001e130790340c1e6442010700d190040c000640341d281c9003140da82d494001c1405034022440203100303070494000b81280301d41602c044aa60382c0e14040c0d155a210080e0502070000380e6140c40c102c101281071441003240711071800040c41c01001520060040c002107d1141c0708440c080c0c7c100e0311040e086a41c101003120380003440107a0301565503480301000c03107505415203c9103504110007002d0000340a018110420142038190603200100e00d20700801459101c4c10b0884100d1680038005441c8a90100d94107020480d60110080103001e000c6148148950141c2c1e107240c041034200030240100000083d1020160000343c50040c5418511403403980d081800400030b501c0f0b4504031111002c1442180c191042d103501c0c4000540d202c100d0081c04c580001c142802e11405608460b40001d42840c00d032081000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 470318884 1250 470317634 470317637
    0x50402071101030504050a0b090d08090d0c0311160605032706130c050a082103060f0909030d051501030e0c09060423010306050f070201020c060105010513030c33 71
    0x5410036600010f50240500805c142c40e240a0501d507000030940142c0028801c0e0001806484202984031000d00105405442c441c1c05501111400002540140076004a15003600f000401000310035006403400403041110044287c4040000481c0381e007240145019250001341000e045080501d04104142000700988481d40043c0c0407c03a03c240002d01018014050310036040040c0e110001304450703078015030180380d0701c1e409101d41024500c45801340c415070101220390249141030250005100b00c000703584240c849e9540101148481c2020012501c8406008034144074034504484202d103590300c01103c007404641030190f050f450a6001c1410384070080020102c040e203454040a000085c140807030555008031080806582e003451007140755008601c9000e0100302480c04502000700000044c00341c40940e8010f104a502d112804109941521002e1030456101c0550036401c01101d141c13940040e00c00548130340c000c0386843c1c20303034640c070540400401103050030340c0d04070001d406188502c1c60040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 470320134 1250 470318884 470318903
    0x1817090904060b06070b0c030a050f16030c030b120708060604110d0207020a03020d05010615050f030718180e010b0a050303030703180c260706051204020d0c1e05040207 74
    0x9002400980c0303d11407144026101c542403000580d580c281c029007c2e140140305010100802080307100e40d002d150380c00085668007141c1400e01d800e1485a42410480100031b05840b045220031407031007548444410a0020004081c1d08110342c0340c1da885070000d007e084002d008450015020707003003e00400802d03070000c1ca102841c3c030032501e5610000350041074007264080c508620000150b9104170030604c1031030040d000007a109280c203d004800991100805050003400d0001c5584c00324400147e9a200f44a0b003014121804410818090310480d80c0150002d103807070245021502c081540b1051481c5102002004514415010048981c450780b2400b94540d00800004850a04c241c00640d19008d02c401c420074036103002e984600328080c05030000c0d203280d0f420100f03e240c0d64001003000b203480012036003c1c000180c1820b0000304035100e01d5840861900703443c0080390454030b550000070440e54003d40707030604042e05c1f515800003141c0f9075038a20381c20b104542c4012589141506c00c40305400d40c05520348 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 470321384 1250 470320134 470320141
    0x115030509160b0c010b03030f0c160b03041b080f010e100203010f0b1c02180102011a0102030414031e06061315150509030d08090d0302041202061b0118170909 70
    0x1060b40794802d04901820f9500c1b007046032859201040076008c045248915a07440e80d001c10a6a450507e40908401800071500ca0400070b104610b800c403a00036030068081203c0b004591a844070441950b804018a803260382c0c00d1461904040d03000c01440c80c2ca003020b4903001d05410a1a0040c0e01003801102540314001c00c003080441c08034402010550448070b401107013100b4091456049030011200000003c0505c201406030b5a42849115050000c12003a50b07107400005000035034034021400b9803003200f014240308210b00e036410011900c0582e80302c0f000003100301c61080c03036540f00c00c0300fa13030502d0088040d030042d0014000b0502030141c0c0d03a5a071111304c088a6240407804000d0703603000e100700c1c0284501004036500701d86043c4002560a010781d141c0302560705040548902d800d10400c1c86900701441804140f00e00c041d4542d0b0b00c00d4864048683e00c0e1182d80d0024500070140c052102441c0542c60700800721018560751074018109402000c4034600d08040000c4070350244600e0340c0c803a6201c2c0844000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 470322634 1250 470321384 470321399
    0xf041406042703020a1101030203040b0103060e011103040804090c080405060718050301021206010221070b062206050f01090b0a0815060403050a141c1101020909011503050916 77
    0x4101100c051a202c1030580c4000a1600240400c00e040c0d005801c600c0c11002801001c12018524200a01c2c00314610300d0f00d03868814498006010042806494190b151040c060940090750721450340c0b180107a50713050074500000e807940b041c2328144506091100c1c07001010300401d030551280303402801600056403a503404644181040e804c0d00c8000811040101e07840d1001d1016240c51a0f100403000e496041207400a071804c020132460341071012200890b20303207003246042584d40d000c1d4046450412915403500241c40404407006c80c0d01c7d0006404aa6034888102d50803040484405a4815100c8120b0368011a1840658092101e40780000c100060300c15120300c840035403110768a941401055001c400203419940b0550050340d1962000f0005811302c1501001660b10700306850042980300c1d90b00b80340503210f616612a0404ac4044007000130b030304160039011904a82c0b00101900125030b1614040380d014845c0ca00d1100002e843c0c440000d86100300050070300041d4001245428626107002130 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 470323741 1107 470322634 470322641
    0x4060e01083a0804171303060e0606010c0209040309171605031c05070c03050105040b0901050601082403070b0c060103140a0c0605091903110f04140604 67
    0x103041c41d070841c4030401c44000500b03414078210a50711400c2c00c943c00c065511454214000001d5001c2e2483c220029880c00e0328450303e0704000742d030001005560748000032a9a940401d844400e00009480c01601d0745901030b10914004070f01584400b00681d0010000c4c441c800c0c294885610501210240e0b4000c401400c4250014816118100c090911243c007071060350052000004201061080340b611400103150050001d2003142024a006d030520082190405010352a2501041403980306e600c005002c1c04003801c040300f0301110b00840c400001003090425a152144240000f80032140c10090044811000081c141561450501a08ac10104c0e16001c400d9004407511000084445200400f52080b81c0741c066280d0088401041402110f401003841d03d1001001c00000c0001c60714407440755550070340c5c60f440890701d00c41c140f0054403240140018450019400a03100381060751 = true := by decide +kernel

theorem cover : BRFrame.Cov 470143884 470323741 := by
  have h0 := BRFrame.cov_init 470143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 470143884 ≤ n) (h2 : n < 470323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
