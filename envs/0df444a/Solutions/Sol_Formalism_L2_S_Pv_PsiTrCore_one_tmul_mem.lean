-- Prove2me | solution 1 for Formalism.L2.S.Pv.PsiTrCore.one_tmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:07.177406+00:00
-- url     : https://prove2.me/submissions/48734dfa-be59-43f5-ad98-ec9d520d90b5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreTrace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.S.Pv.PsiTrCore
theorem _root_.solution (c : Af F) (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] c ∈ IntAf F E := by
  show _ ∈ Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)
  unfold Formalism.UG.tensInt
  apply Subring.subset_closure
  right
  exact ⟨⟨c, hc⟩, rfl⟩
end Formalism.L2.S.Pv.PsiTrCore
