-- Prove2me | solution 1 for D1Bound5.coherent_weighted_remainder_summable_and_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:17.364016+00:00
-- url     : https://prove2.me/submissions/4a19fa01-4877-473e-8c20-7387adf6fc16

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Theorems.Thm_D1Bound5_hsymm_aeval_complex_norm_le_choose
import Theorems.Thm_D1Bound5_negative_binomial_positive_tail_tsum

section
namespace D1Bound5

/-- An analytic coefficient envelope, together with the exact positive-degree
homogeneous majorant, controls the entire square-root interpolation tail.
This is a conditional interface: the bound on the coefficients `f` must be
proved separately for the specific square-root convolution. -/
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (f : ℕ → ℂ) (m : ℕ) (C ρ t : ℝ)
    (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (ht0 : 0 ≤ t)
    (hρ : ∀ i, ‖a i‖ ≤ ρ) (hradius : ρ * t < 1)
    (hf : ∀ j : ℕ, ‖f (m + (j + 1))‖ ≤ C * t ^ (m + (j + 1))) :
    Summable (fun j : ℕ => f (m + (j + 1)) *
       MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))) ∧
    ‖∑' j : ℕ, f (m + (j + 1)) *
       MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ ≤
      C * t ^ m * (1 / (1 - ρ * t) ^ Fintype.card ι - 1) := by
  let q : ℕ := Fintype.card ι - 1
  let r : ℝ := ρ * t
  have hq : q + 1 = Fintype.card ι := Nat.succ_pred_eq_of_pos Fintype.card_pos
  have hr0 : 0 ≤ r := mul_nonneg hρ0 ht0
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hradius
  have hmajor : Summable (fun k : ℕ =>
      (Nat.choose (k + q) q : ℝ) * r ^ k) :=
    summable_choose_mul_geometric_of_norm_lt_one q hr
  have hmajorTail : Summable (fun j : ℕ =>
      (Nat.choose (j + 1 + q) q : ℝ) * r ^ (j + 1)) :=
    (summable_nat_add_iff
      (f := fun k : ℕ => (Nat.choose (k + q) q : ℝ) * r ^ k) 1).mpr hmajor
  have hscaled : Summable (fun j : ℕ =>
      (C * t ^ m) * ((Nat.choose (j + 1 + q) q : ℝ) * r ^ (j + 1))) :=
    hmajorTail.mul_left (C * t ^ m)
  have hterm (j : ℕ) :
      ‖f (m + (j + 1)) *
         MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ ≤
        (C * t ^ m) * ((Nat.choose (j + 1 + q) q : ℝ) * r ^ (j + 1)) := by
    have hchoose : Nat.choose (Fintype.card ι + (j + 1) - 1) (j + 1) =
        Nat.choose (j + 1 + q) q := by
      have heq : Fintype.card ι + (j + 1) - 1 = j + 1 + q := by omega
      rw [heq]
      exact Nat.choose_symm_add
    calc
      ‖f (m + (j + 1)) *
          MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ =
        ‖f (m + (j + 1))‖ *
          ‖MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ :=
            norm_mul _ _
      _ ≤ (C * t ^ (m + (j + 1))) *
          ((Nat.choose (Fintype.card ι + (j + 1) - 1) (j + 1) : ℝ) *
            ρ ^ (j + 1)) :=
          mul_le_mul (hf j)
            (hsymm_aeval_complex_norm_le_choose a (j + 1) ρ hρ0 hρ)
            (norm_nonneg _) (mul_nonneg hC (pow_nonneg ht0 _))
      _ = (C * t ^ m) *
          ((Nat.choose (j + 1 + q) q : ℝ) * r ^ (j + 1)) := by
          rw [hchoose, pow_add]
          simp only [r, mul_pow]
          ring
  have hsum : Summable (fun j : ℕ => f (m + (j + 1)) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))) :=
    Summable.of_norm_bounded hscaled hterm
  have hnorm : Summable (fun j : ℕ => ‖f (m + (j + 1)) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖) := by
    apply Summable.of_nonneg_of_le _ hterm hscaled
    intro j
    exact norm_nonneg _
  refine ⟨hsum, ?_⟩
  calc
    ‖∑' j : ℕ, f (m + (j + 1)) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ ≤
      ∑' j : ℕ, ‖f (m + (j + 1)) *
        MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ (j + 1))‖ :=
          norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, (C * t ^ m) *
      ((Nat.choose (j + 1 + q) q : ℝ) * r ^ (j + 1)) :=
        hnorm.tsum_le_tsum hterm hscaled
    _ = (C * t ^ m) * (1 / (1 - r) ^ (q + 1) - 1) := by
      rw [tsum_mul_left, negative_binomial_positive_tail_tsum q r hr0 hradius]
    _ = C * t ^ m * (1 / (1 - ρ * t) ^ Fintype.card ι - 1) := by
      rw [hq]

end D1Bound5
end
