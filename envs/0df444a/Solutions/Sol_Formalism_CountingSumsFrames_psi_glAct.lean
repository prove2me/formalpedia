-- Prove2me | solution 1 for Formalism.CountingSumsFrames.psi_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:42.650575+00:00
-- url     : https://prove2.me/submissions/5c60da63-f7d3-45f8-bfc6-83d6767d2c53

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_whc_comm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_wL


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
theorem _root_.solution (L L' : Letters N) (j0 j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    psi p L j0 (glAct p L' j c d x) = glAct p L' j c d (psi p L j0 x) :=
  whc_comm _ _ (fun D x hx => glAct_wL L' j c d hx) _ x
end Formalism.CountingSumsFrames
