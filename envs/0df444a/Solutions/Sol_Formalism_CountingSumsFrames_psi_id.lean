-- Prove2me | solution 1 for Formalism.CountingSumsFrames.psi_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:43.698045+00:00
-- url     : https://prove2.me/submissions/a2b60970-d48a-41b1-945d-b30cc8787224

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
theorem _root_.solution (L : Letters N) (j0 : ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Pol p r (Lz L j0)) :
    psi p L j0 x = x := by
  rw [pol_iff] at hx
  rw [psi, weightedHomogeneousComponent_of_mem hx, if_pos rfl]
end Formalism.CountingSumsFrames
