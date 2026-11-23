-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.support_dg_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:28.605891+00:00
-- url     : https://prove2.me/submissions/c881c033-54c6-4907-853e-b50c2cfa89ff

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_dg


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
variable {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    (dg f F).support ⊆ F.support := by
  intro α hα
  rw [mem_support_iff, coeff_dg] at hα
  exact mem_support_iff.mpr (right_ne_zero_of_mul hα)
end Formalism.MainNotions.PlaneGram
