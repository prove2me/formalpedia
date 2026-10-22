-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound_separated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:33:56.847712+00:00
-- url     : https://prove2.me/submissions/115f9b7e-0c12-48ae-b264-9e5e9a07c0c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_verification_strategy_lump_sum_drop
import Theorems.Thm_AvramDividend_Classical_local_verification_smooth_differentiable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The discounted dividend measure on a countable set of active payment
times is bounded by the countable sum of the verification-value drops, under
the two *separate* analytic hypotheses `hw_gen` and `hw_grad`.

This is the separated-hypothesis variant of
`local_verification_capped_countable_dividendMeasure_bound`.  That lemma
assumes the HJB equality `max (X.generator w y - q * w y) (1 - deriv w y) = 0`,
whereas the two separate inequalities only give that the maximum is
nonpositive, so the HJB form does not follow from them.

The proof is the same atom-by-atom comparison, with the jump bound taken
from `verification_strategy_lump_sum_drop`, which needs only the gradient
hypothesis `hw_grad` and the admissibility and reserve cap, and which is
Proved.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in S,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑' s : S, ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
      (w (riskProcess X x D (s : ℝ).toNNReal ω) -
        w (riskProcess X x D (s : ℝ).toNNReal ω -
          (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω)))) := by
  -- `ContDiffOn` gives the `DifferentiableOn` needed by the lump-sum drop.
  have hw_diff : DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    local_verification_smooth_differentiable X w C hw_smooth
  -- The discounted atom at time `t` is bounded by the discounted drop of the
  -- verification value across the right jump of `D` there.
  have hatom : ∀ (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
        dividendMeasure D ω {(t : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))) := by
    intro t ht
    have hjump :
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω)) :=
      verification_strategy_lump_sum_drop
        X w C hw_cont hw_diff hw_grad x hxC D hD ω t ht
    rw [dividendMeasure_singleton_eq_rightLimit_sub D hD.1.1 ω t]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hjump (Real.exp_pos _).le
  -- The countable sum of the atom bounds.
  rw [lintegral_countable _ hCountable]
  refine ENNReal.tsum_le_tsum fun s => ?_
  have hEq : ((s : ℝ).toNNReal : ℝ) = (s : ℝ) :=
    Real.coe_toNNReal s.1 (hNonneg s.1 s.2)
  have hBound := hatom (s : ℝ).toNNReal (hActive s.1 s.2)
  simpa only [hEq] using hBound

