-- Prove2me | solution 1 for Formalism.L2.Pj.cvalR_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:30.706892+00:00
-- url     : https://prove2.me/submissions/2749922b-2bc4-4982-b82e-979c5812299c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPolynomial
variable {K : Type} [Field K]
namespace Formalism.L2.Pj
theorem _root_.solution (σ : K →+* ℂ) (t : K) : cvalR σ (algebraMap K (CAt σ) t) = σ t := rfl
end Formalism.L2.Pj
