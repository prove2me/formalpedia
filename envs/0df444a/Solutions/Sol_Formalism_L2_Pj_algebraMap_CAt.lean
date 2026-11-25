-- Prove2me | solution 1 for Formalism.L2.Pj.algebraMap_CAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:17.259689+00:00
-- url     : https://prove2.me/submissions/8df9e547-5b93-458b-8749-38a4e7d12ede

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt

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
theorem _root_.solution (σ : K →+* ℂ) (c : K) : (show ℂ from algebraMap K (CAt σ) c) = σ c := rfl
end Formalism.L2.Pj
