-- Prove2me | solution 1 for Formalism.MainStatements.RankOne.KD.finAlg_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:56.004014+00:00
-- url     : https://prove2.me/submissions/4aca6604-d863-4da0-b5a1-5e5ead74f000

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open Formalism Formalism.MainStatements Formalism.MainStatements.RankOne Formalism.MainStatements.RankOne.KD
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm
variable {n : ℕ} {K : Set (Mat n)} {hK : IsMatGroup K}
namespace Formalism.MainStatements.RankOne.KD
theorem _root_.solution : (finAlg (MG K hK)).SeparatesPoints := by
  intro x y hxy
  have hne : x.mat - y.mat ≠ 0 := fun h => hxy (MG.ext (sub_eq_zero.1 h))
  obtain ⟨i, j, hij⟩ : ∃ i j, x.mat i j ≠ y.mat i j := by
    by_contra h
    push Not at h
    exact hxy (MG.ext (Matrix.ext h))
  have hV : FinInv (LinearMap.range (co hK)) := by
    refine ⟨Submodule.fg_range _, ?_⟩
    rintro a _ ⟨f, rfl⟩
    exact ⟨f.comp (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a.mat)), rfl⟩
  let e : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun m => m i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hre : (x.mat i j).re = (y.mat i j).re
  · exact ⟨_, ⟨co hK (Complex.imCLM.comp e), ⟨_, hV, ⟨_, rfl⟩⟩, rfl⟩, fun h => hij (Complex.ext hre h)⟩
  · exact ⟨_, ⟨co hK (Complex.reCLM.comp e), ⟨_, hV, ⟨_, rfl⟩⟩, rfl⟩, hre⟩
end Formalism.MainStatements.RankOne.KD
