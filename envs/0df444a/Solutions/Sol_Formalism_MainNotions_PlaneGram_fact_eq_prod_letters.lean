-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_eq_prod_letters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:45.826331+00:00
-- url     : https://prove2.me/submissions/663d299a-f64f-4098-9b1e-a720ab85744c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_eq_prod

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {L : Type} [Fintype L] {r : ℕ} (α : L × Fin r →₀ ℕ) :
    fact α = ∏ i : L, ∏ a : Fin r, (α (i, a)).factorial := by
  rw [fact_eq_prod, Fintype.prod_prod_type]
end Formalism.MainNotions.PlaneGram
