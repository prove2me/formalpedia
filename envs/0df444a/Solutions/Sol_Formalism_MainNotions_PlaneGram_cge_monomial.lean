-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:00.951796+00:00
-- url     : https://prove2.me/submissions/ffeb3f8c-d2f1-4bbd-82fa-74f640a30c99

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero

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
theorem _root_.solution {σ : Type} {a : ℝ} {c : K} (α : σ →₀ ℕ) (hc : vge v a c) :
    cge v a (monomial α c) := by
  classical
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hc
  · exact vge_zero v a
end Formalism.MainNotions.PlaneGram
