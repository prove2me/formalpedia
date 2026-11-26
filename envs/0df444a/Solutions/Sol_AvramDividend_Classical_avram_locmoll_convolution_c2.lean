-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_convolution_c2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:20:57.544271+00:00
-- url     : https://prove2.me/submissions/53e7fc3e-6250-4b44-918d-d3cba545b520

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (V ρ : ℝ → ℝ) (hVmono : Monotone V)
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    (∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) ∧
    ContDiff ℝ 2 g := by 
  dsimp only
  let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
  have hloc : LocallyIntegrable V volume := hVmono.locallyIntegrable
  have hI (y : ℝ) : Integrable (fun r => ρ r * V (y - r)) := by
    exact (hρcompact.convolutionExists_left
      (ContinuousLinearMap.mul ℝ ℝ) hρsmooth.continuous hloc y).integrable
  have hg : ContDiff ℝ 2 g :=
    hρcompact.contDiff_convolution_left
      (ContinuousLinearMap.mul ℝ ℝ) hρsmooth hloc
  exact ⟨hI, hg⟩
