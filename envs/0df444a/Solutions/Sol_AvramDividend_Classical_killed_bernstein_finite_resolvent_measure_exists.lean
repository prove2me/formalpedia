-- Prove2me | solution 1 for AvramDividend.Classical.killed_bernstein_finite_resolvent_measure_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:39:20.484819+00:00
-- url     : https://prove2.me/submissions/a6ac14d0-6131-41be-b86d-4110ffc5dc03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_killed_bernstein_truncation_laplace_approximants
import Theorems.Thm_AvramDividend_Classical_excursion_resolvent_uniform_tightness_from_laplace
import Theorems.Thm_AvramDividend_Classical_excursion_laplace_weak_limit_of_tight_approximants
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤) :
    ∃ U : Measure ℝ,
      U (Iio (0 : ℝ)) = 0 ∧
      U Set.univ = ENNReal.ofReal (k⁻¹) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
          (ENNReal.ofReal k +
            (∫⁻ t : ℝ,
              ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹) := by
  obtain ⟨F, β, hF0, hFcont, hFpos, hMass, hSupp,
      hLower, hConv, hIdent⟩ :=
    killed_bernstein_truncation_laplace_approximants
      κ hκsupp k hk hFin
  have hTight : IsTightMeasureSet (Set.range β) :=
    excursion_resolvent_uniform_tightness_from_laplace
      β k hk F hF0 hFcont hFpos hMass hSupp hLower
  obtain ⟨U, hUsupp, hUmass, hUlap⟩ :=
    excursion_laplace_weak_limit_of_tight_approximants
      β k hk F hFpos hMass hSupp hTight hConv
  refine ⟨U, hUsupp, hUmass, ?_⟩
  intro s hs
  exact (hUlap s hs.le).trans (hIdent s hs)
