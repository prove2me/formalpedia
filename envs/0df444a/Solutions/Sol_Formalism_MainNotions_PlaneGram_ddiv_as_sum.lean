-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_as_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:28.574663+00:00
-- url     : https://prove2.me/submissions/7772b31c-6e0e-4213-b7f8-4b83db2e810b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (M : σ →₀ ℕ) (G : MvPolynomial σ K) :
    ddiv M G = ∑ α ∈ G.support, G.coeff α • ddiv M (monomial α (1 : K)) := by
  conv_lhs => rw [G.as_sum]
  rw [ddiv_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← ddiv_smul]
  simp only [smul_monomial, smul_eq_mul, mul_one]
end Formalism.MainNotions.PlaneGram
