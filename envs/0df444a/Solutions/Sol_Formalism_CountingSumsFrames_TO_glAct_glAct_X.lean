-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.glAct_glAct_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:37.605441+00:00
-- url     : https://prove2.me/submissions/223ce56a-610b-4202-a632-7a793df07944

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_X_gen


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
theorem _root_.solution (L : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) :
    glAct p L j c d (glAct p L j c d (X v)) = 0 := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs with h1 h2 h3 h3
  · rw [glAct_X_gen, if_pos h1, if_pos h2, if_neg hcd]
  · exact map_zero _
  · rw [map_neg, glAct_X_gen, if_pos h1, if_neg h2, if_neg (Ne.symm hcd), neg_zero]
  · exact map_zero _
  · exact map_zero _
end Formalism.CountingSumsFrames.TO
