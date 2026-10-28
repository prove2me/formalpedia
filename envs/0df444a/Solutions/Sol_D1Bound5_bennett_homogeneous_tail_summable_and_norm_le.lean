-- Prove2me | solution 1 for D1Bound5.bennett_homogeneous_tail_summable_and_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:10.323076+00:00
-- url     : https://prove2.me/submissions/49ece322-e3a4-4c03-85d5-ba1048badbeb

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_choose_tail_identity
import Theorems.Thm_D1Bound5_bennett_negative_binomial_abs_hasSum
import Theorems.Thm_D1Bound5_hsymm_aeval_complex_norm_le_choose

section
/-!
An elementary analytic majorant for the actual binomial/homogeneous tail that
arises in Bennett's simultaneous approximants.  In contrast to a coefficient
envelope interface, every coefficient of the series below is specified.

The algebraic identification of the residue moments with homogeneous
polynomials is a separate theorem.  This file does not assume that an arbitrary
series is a Bennett residual.  Once that identification is available, the
specialization n = 3k, s = k + 1/2 gives exactly the eta exponent in the paper.
-/

namespace D1Bound5









/-- A fully explicit generalized-binomial/homogeneous tail is summable and
satisfies the sharp negative-binomial majorant.  Here the repeated-node count
is n+1, as required for a denominator of degree n+1. -/
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (n : ℕ) (s ρ : ℝ) (x : ℂ)
    (hcard : Fintype.card ι = n + 1)
    (hs : s < n) (hρ0 : 0 ≤ ρ)
    (ha : ∀ i, ‖a i‖ ≤ ρ) (hradius : ρ * ‖x‖ < 1) :
    Summable (fun t : ℕ =>
      (Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)) ∧
    ‖∑' t : ℕ, (Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)‖ ≤
      |Ring.choose s n| * ‖x‖ ^ n / (1 - ρ * ‖x‖) ^ ((n : ℝ) - s) := by
  let q : ℝ := n - s
  let r : ℝ := ρ * ‖x‖
  have hq : 0 < q := sub_pos.mpr hs
  have hr0 : 0 ≤ r := mul_nonneg hρ0 (norm_nonneg _)
  have hsum := bennett_negative_binomial_abs_hasSum q r hq hr0 hradius
  have hscaled : Summable (fun t : ℕ =>
      (|Ring.choose s n| * ‖x‖ ^ n) *
        (|Ring.choose (-q) t| * r ^ t)) :=
    hsum.summable.mul_left (|Ring.choose s n| * ‖x‖ ^ n)
  have hterm (t : ℕ) :
      ‖(Ring.choose s (n + t) : ℂ) *
          MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)‖ ≤
        (|Ring.choose s n| * ‖x‖ ^ n) *
          (|Ring.choose (-q) t| * r ^ t) := by
    have hidx : Fintype.card ι + t - 1 = n + t := by omega
    have hid := bennett_choose_tail_identity s n t
    have hsq : s - n = -q := by dsimp [q]; ring
    rw [hsq] at hid
    calc
      ‖(Ring.choose s (n + t) : ℂ) *
          MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)‖ =
        |Ring.choose s (n + t)| *
          ‖MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t)‖ * ‖x‖ ^ (n + t) := by
            rw [norm_mul, norm_mul, norm_pow, ← Complex.ofReal_choose,
              Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |Ring.choose s (n + t)| *
          ((Nat.choose (n + t) t : ℝ) * ρ ^ t) * ‖x‖ ^ (n + t) := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            simpa only [hidx] using hsymm_aeval_complex_norm_le_choose a t ρ hρ0 ha
      _ = (|Ring.choose s (n + t)| * (Nat.choose (n + t) t : ℝ)) *
          (‖x‖ ^ n * r ^ t) := by
            simp only [r, pow_add, mul_pow]
            ring
      _ = (|Ring.choose s n| * ‖x‖ ^ n) *
          (|Ring.choose (-q) t| * r ^ t) := by rw [hid]; ring
  have hcomplex : Summable (fun t : ℕ =>
      (Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)) :=
    Summable.of_norm_bounded hscaled hterm
  have hnorm : Summable (fun t : ℕ =>
      ‖(Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hscaled
  refine ⟨hcomplex, ?_⟩
  calc
    ‖∑' t : ℕ, (Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)‖ ≤
      ∑' t : ℕ, ‖(Ring.choose s (n + t) : ℂ) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ t) * x ^ (n + t)‖ :=
          norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' t : ℕ, (|Ring.choose s n| * ‖x‖ ^ n) *
        (|Ring.choose (-q) t| * r ^ t) :=
          hnorm.tsum_le_tsum hterm hscaled
    _ = |Ring.choose s n| * ‖x‖ ^ n / (1 - ρ * ‖x‖) ^ ((n : ℝ) - s) := by
      rw [tsum_mul_left, hsum.tsum_eq]
      simp only [q, r, div_eq_mul_inv, one_mul]



end D1Bound5
end
