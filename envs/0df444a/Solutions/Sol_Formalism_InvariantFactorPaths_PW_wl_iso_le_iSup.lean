-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wl_iso_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:47.724086+00:00
-- url     : https://prove2.me/submissions/2580eed8-24bc-49ed-9666-a23e0e16cc67

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_iSup_stable
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
    IsoW G W la ≤ ⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)} :=
  G.gS_le (fun v hv => Submodule.mem_iSup_of_mem (⟨v, hv⟩ : {v : V // G.IsHW la v ∧ v ∈ W})
    (G.subset_gS _ (Set.mem_singleton v))) (GlX.iSup_stable G fun _ => G.gS_stable _)
end Formalism.InvariantFactorPaths.PW
