-- Prove2me | solution 1 for Formalism.CountingSumsFrames.psi_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:14.696271+00:00
-- url     : https://prove2.me/submissions/544fcc97-4134-47a6-93a6-b4d2af54d559

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_whc_comm
import Theorems.Thm_Formalism_CountingSumsFrames_whc_keep

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
theorem _root_.solution (L L' : Letters N) (j0 j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    psi p L j0 ((GA p L' j).comp ν x) = (GA p L' j).comp ν (psi p L j0 x) :=
  whc_comm _ ((GA p L' j).comp ν) (fun D x hx => whc_keep _ _ _ _ hx) _ x
end Formalism.CountingSumsFrames
