-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.int_of_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:44:49.895445+00:00
-- url     : https://prove2.me/submissions/7b129057-5857-432c-84e1-ba5c8a515628

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_intPol_norm
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm


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
theorem _root_.solution {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ)
    (h : g * monomial m 1 ∈ IntPol p σ) : g ∈ IntPol p σ := by
  refine TM.mem_intPol_of_norm _ fun k => ?_
  have := intPol_norm _ h (k + m)
  rwa [coeff_mul_monomial, mul_one] at this
end Formalism.CountingSumsFrames.TO
