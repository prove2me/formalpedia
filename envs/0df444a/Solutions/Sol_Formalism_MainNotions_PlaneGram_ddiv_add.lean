-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:04.094376+00:00
-- url     : https://prove2.me/submissions/35f03b5f-e1b3-418d-8691-461bf7a14ea8

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
theorem _root_.solution {σ : Type} (M : σ →₀ ℕ) (F G : MvPolynomial σ K) :
    ddiv M (F + G) = ddiv M F + ddiv M G := by simp only [ddiv_eq, map_add]
end Formalism.MainNotions.PlaneGram
