-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:44.458034+00:00
-- url     : https://prove2.me/submissions/4671a4f5-ea6c-4ca5-b162-65bb37ab24d1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_sum

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
theorem _root_.solution {σ ι : Type} {a : ℝ} (s : Finset ι) (f : ι → MvPolynomial σ K)
    (h : ∀ i ∈ s, cge v a (f i)) : cge v a (∑ i ∈ s, f i) := by
  intro α
  rw [MvPolynomial.coeff_sum]
  exact vge_sum v s _ fun i hi => h i hi α
end Formalism.MainNotions.PlaneGram
