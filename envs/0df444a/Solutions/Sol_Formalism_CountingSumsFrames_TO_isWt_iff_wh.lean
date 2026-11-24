-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.isWt_iff_wh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:00.67594+00:00
-- url     : https://prove2.me/submissions/c15e69ed-807c-492f-a11f-197f57edda72

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) (j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt ν x ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) ν := by
  constructor
  · intro h
    have h' : weightedHomogeneousComponent (wv L j) ν x = x := h
    rw [← h']
    exact weightedHomogeneousComponent_mem _ _ _
  · intro h
    show weightedHomogeneousComponent (wv L j) ν x = x
    rw [weightedHomogeneousComponent_of_mem h, if_pos rfl]
end Formalism.CountingSumsFrames.TO
