-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaLog.hasDerivAt_wFactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:50.338291+00:00
-- url     : https://prove2.me/submissions/ca191aa0-9803-4be6-96a9-a116d512063b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaLog
namespace Formalism.L2.Th1.F.SigmaLog
theorem _root_.solution (l z : ℂ) :
    HasDerivAt (wFactor l)
      (-(1 / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))
        + (1 - z / l) * (Complex.exp (z / l + z ^ 2 / (2 * l ^ 2)) * (1 / l + 2 * z / (2 * l ^ 2)))) z := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z / l) (-(1 / l)) z := by
    simpa using ((hasDerivAt_id z).div_const l).const_sub 1
  have h2 : HasDerivAt (fun z : ℂ => z / l + z ^ 2 / (2 * l ^ 2)) (1 / l + 2 * z / (2 * l ^ 2)) z := by
    have := ((hasDerivAt_id z).div_const l).fun_add ((hasDerivAt_pow 2 z).div_const (2 * l ^ 2))
    simpa using this
  exact h1.mul h2.cexp
end Formalism.L2.Th1.F.SigmaLog
