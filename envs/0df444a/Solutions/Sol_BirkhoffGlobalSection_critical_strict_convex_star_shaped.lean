-- Prove2me | solution 1 for BirkhoffGlobalSection.critical_strict_convex_star_shaped
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T05:58:41.033631+00:00
-- url     : https://prove2.me/submissions/f0f46fea-7342-4f27-9796-5583d4e0bd3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Definitions.Def_BirkhoffGlobalSection_EHCriticalConvexity
import Theorems.Thm_BirkhoffGlobalSection_critical_reference_model_exists
import Theorems.Thm_BirkhoffGlobalSection_critical_estimate_hessian_pos
import Theorems.Thm_BirkhoffGlobalSection_critical_estimate_radial_pos

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ M₀ : RegularizationModel (1 / 2) 2,
      ∀ s ∈ leftEnergyComponent (1 / 2) 2, s ∉ U →
        IsStrictlyConvexStarShapedAt M₀.modelHamiltonian (M₀.toModel s) := by
  obtain ⟨M₀, hG, hIm⟩ := critical_reference_model_exists U hU hplus hminus
  refine ⟨M₀, fun s hs hsU => ?_⟩
  have hym : M₀.toModel s ∈ ehEstimateRegion := hIm s hs hsU
  rw [hG]
  exact ⟨critical_estimate_hessian_pos _ hym, critical_estimate_radial_pos _ hym⟩
