-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.glAct_X_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:03.841713+00:00
-- url     : https://prove2.me/submissions/7ecdabfe-7d8e-4691-a3a7-cf2d4db6697b

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_X_gen
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_X


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
theorem _root_.solution (L : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) :
    glAct p L j c d (X v) ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨i, a⟩ := v
  rw [glAct_X_gen]
  split_ifs
  · exact FrozenVariableLemmas.intPol_X p _
  · exact Submodule.zero_mem _
  · exact Submodule.neg_mem _ (FrozenVariableLemmas.intPol_X p _)
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
end Formalism.CountingSumsFrames.TO
