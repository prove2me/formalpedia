-- Prove2me | solution 1 for Formalism.CountingSumsFrames.psi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:44.978167+00:00
-- url     : https://prove2.me/submissions/65c531cf-d937-48f5-987a-7584772c0978

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Letters N) (j0 : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : psi p L j0 x ∈ Pol p r (Lz L j0) := by
  rw [pol_iff]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
end Formalism.CountingSumsFrames
