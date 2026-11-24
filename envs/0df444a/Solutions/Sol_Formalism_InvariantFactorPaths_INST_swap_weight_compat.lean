-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.swap_weight_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:48:33.6938+00:00
-- url     : https://prove2.me/submissions/1039eedf-e0b9-4007-81a8-d5417841b84d

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_support_swp
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_isWt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution : SwpWt := by
  intro p _ r n ν μ f
  classical
  unfold GR
  rw [GAe_isWt_iff, MvPolynomial.mem_restrictSupport_iff, rgl_support_swp]
  constructor
  · intro h m hm a
    have := h (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hm)) a
    rw [← rgl_wt ν a m]
    exact this
  · intro h m' hm' a
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hm')
    have := h m hm a
    rw [← rgl_wt ν a m] at this
    exact this
end Formalism.InvariantFactorPaths.INST
