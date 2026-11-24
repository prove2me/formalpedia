-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.slc_ycond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:05.581846+00:00
-- url     : https://prove2.me/submissions/165bd5a9-c79a-4519-a908-f5630def261b

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_wh
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_of_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution [NeZero r] (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (m : Fin N × Fin r →₀ ℕ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p L J M) : slc (fsj N r j0) m F ∈ YCond p L J M :=
  ycond_of_comm L J M (slc (fsj N r j0) m) (fun c d F => slc_glAct L hJ c d m F) (fun ν F hF => slc_wh L hJ m hF) F hF
end Formalism.CountingSumsFrames.TO
