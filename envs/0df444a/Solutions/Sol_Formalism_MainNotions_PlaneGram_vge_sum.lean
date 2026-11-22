-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:40.707633+00:00
-- url     : https://prove2.me/submissions/2ebe823d-cc22-4278-9a53-a9e708a0af7a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_add

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
theorem _root_.solution {ι : Type*} {a : ℝ} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, vge v a (f i)) :
    vge v a (∑ i ∈ s, f i) := Finset.sum_induction f (vge v a) (fun _ _ => vge_add v) (vge_zero v a) h
end Formalism.MainNotions.PlaneGram
