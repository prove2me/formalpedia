-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:26.085654+00:00
-- url     : https://prove2.me/submissions/2d41166f-8bc3-450a-bc85-bdd4929a9bdf

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast_nonneg

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
theorem _root_.solution (n : ℕ) : vge v 0 (n : K) := (vge_zero_iff v _).mpr (v_natCast_nonneg v n)
end Formalism.MainNotions.PlaneGram
