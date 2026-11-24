-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.zpClosed_toAddSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:43.318714+00:00
-- url     : https://prove2.me/submissions/a379aea6-48e8-4df1-aa99-37ec4784d844

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℚ_[p] W] [Module ℤ_[p] W]
    [IsScalarTower ℤ_[p] ℚ_[p] W] (L : Submodule ℤ_[p] W) : ZpClosed p L.toAddSubgroup := by
  intro c hc x hx
  rw [Submodule.mem_toAddSubgroup] at hx ⊢
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[p], (a : ℚ_[p]) = c := ⟨⟨c, hc⟩, rfl⟩
  have e : c • x = a • x := by
    rw [← ha]
    exact algebraMap_smul ℚ_[p] a x
  rw [e]
  exact L.smul_mem _ hx
end Formalism.InvariantFactorPaths.PW
