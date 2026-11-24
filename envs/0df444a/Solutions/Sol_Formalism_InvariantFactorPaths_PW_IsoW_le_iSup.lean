-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.IsoW_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:13.96517+00:00
-- url     : https://prove2.me/submissions/91484f77-67c5-4036-ae66-9461b78e1f39

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) :
    IsoW G W la ≤ ⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)} := by
  refine G.gS_le (fun v hv => ?_) ?_
  · exact (le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) ⟨v, hv⟩)
      (G.subset_gS _ (Set.mem_singleton v))
  · intro a b x hx
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}).comap (G.E a b) :=
      iSup_le fun i y hy =>
        (le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) i) (G.gS_stable _ a b y hy)
    exact hle hx
end Formalism.InvariantFactorPaths.PW
