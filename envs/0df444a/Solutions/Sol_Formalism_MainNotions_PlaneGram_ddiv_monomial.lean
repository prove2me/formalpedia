-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:26.011784+00:00
-- url     : https://prove2.me/submissions/fcd2e31f-2f7f-475a-82b2-0fc943f61fec

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) =
      if M ≤ α then monomial (α - M) (c * α.prod fun x k => (k.choose (M x) : K)) else 0 := by
  rw [ddiv_eq, ddivL, lsup_monomial]
  split_ifs
  · rw [smul_monomial, smul_eq_mul]
  · rw [smul_zero]
end Formalism.MainNotions.PlaneGram
