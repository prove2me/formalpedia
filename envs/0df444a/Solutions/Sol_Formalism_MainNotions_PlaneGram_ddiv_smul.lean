-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:32.077143+00:00
-- url     : https://prove2.me/submissions/590ff9e4-668b-42eb-88d9-5466b2bf2fb0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_eq

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
theorem _root_.solution {σ : Type} (M : σ →₀ ℕ) (a : K) (F : MvPolynomial σ K) :
    ddiv M (a • F) = a • ddiv M F := by simp only [ddiv_eq, map_smul]
end Formalism.MainNotions.PlaneGram
