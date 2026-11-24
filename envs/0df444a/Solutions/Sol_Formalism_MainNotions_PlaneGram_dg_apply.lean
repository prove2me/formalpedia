-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:35.969471+00:00
-- url     : https://prove2.me/submissions/0dc6f406-c274-4723-a05a-c8938037d66d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_eq_lsup
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
theorem _root_.solution {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  rw [dg_eq_lsup, lsup_apply]
  exact Finset.sum_congr rfl fun α _ => by rw [smul_monomial, smul_eq_mul, mul_comm]
end Formalism.MainNotions.PlaneGram
