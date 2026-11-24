-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.length_quot_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:33.481965+00:00
-- url     : https://prove2.me/submissions/474e5f7f-3353-44dd-827e-1111616e0dfd

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Bl_DiscreteValuationQuotients_goal1
import Theorems.Thm_P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (φ : M →ₗ[O] M) (hφ : Function.Injective φ) :
    Module.length O (M ⧸ LinearMap.range φ) = IsDiscreteValuationRing.addVal O (LinearMap.det φ) := by
  first | exact Bl.DiscreteValuationQuotients.goal1 .. | (apply Bl.DiscreteValuationQuotients.goal1 <;> assumption) | (intros; apply Bl.DiscreteValuationQuotients.goal1 <;> assumption)
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
