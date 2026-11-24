-- Prove2me | solution 1 for Formalism.L2.Pj.eq_zero_of_cpts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:45.96359+00:00
-- url     : https://prove2.me/submissions/54d9c500-6bde-4203-b701-df622d1dc927

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
import Theorems.Thm_Formalism_L2_Pj_eq_zero_of_pts

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
theorem _root_.solution (σ : K →+* ℂ) (p : TRing K) (a : p.R) (h : ∀ ψ : p.R →ₐ[K] CAt σ, ψ a = 0) : a = 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  exact eq_zero_of_pts (M := CAt σ) p a h
end Formalism.L2.Pj
