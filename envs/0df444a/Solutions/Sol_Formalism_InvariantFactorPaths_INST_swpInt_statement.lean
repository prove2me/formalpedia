-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.swpInt_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:47.444171+00:00
-- url     : https://prove2.me/submissions/247b591e-19ee-4bc9-8cf5-970d126a2529

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_swp_map
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_iff


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
theorem _root_.solution : SwpInt := by
  intro p _ r n f
  rw [Formalism.GM.FrozenVariableLemmas.intPol_iff]
  constructor
  · rintro ⟨F0, h⟩
    refine ⟨(swp ℤ_[p] r n).symm F0, (swp ℚ_[p] r n).injective ?_⟩
    rw [rgl_swp_map, AlgEquiv.apply_symm_apply, h]
  · rintro ⟨f0, rfl⟩
    exact ⟨swp ℤ_[p] r n f0, (rgl_swp_map _ _ f0).symm⟩
end Formalism.InvariantFactorPaths.INST
