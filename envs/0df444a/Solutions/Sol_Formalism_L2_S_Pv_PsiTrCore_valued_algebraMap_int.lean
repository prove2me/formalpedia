-- Prove2me | solution 1 for Formalism.L2.S.Pv.PsiTrCore.valued_algebraMap_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:08.97818+00:00
-- url     : https://prove2.me/submissions/6ac62c32-8f2d-413f-b6b0-7052ffad5138

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_valued_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.S.Pv.PsiTrCore
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (r : F)) = v.intValuation r := by
  rw [valued_algebraMap]
  exact valuation_of_algebraMap v r
end Formalism.L2.S.Pv.PsiTrCore
