-- Prove2me | solution 1 for Formalism.CountingSumsFrames.slc_ycond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:57.058861+00:00
-- url     : https://prove2.me/submissions/c607cec5-e85e-4b82-a0f6-cfd0e7d0bf6a

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_slc_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_slc_wh
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_of_comm


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
theorem _root_.solution [NeZero r] (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (m : Fin N × Fin r →₀ ℕ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p L J M) : slc (fsj N r j0) m F ∈ YCond p L J M :=
  ycond_of_comm L J M (slc (fsj N r j0) m) (fun c d F => slc_glAct L hJ c d m F) (fun ν F hF => slc_wh L hJ m hF) F hF
end Formalism.CountingSumsFrames
