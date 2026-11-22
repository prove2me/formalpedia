-- Prove2me | solution 1 for Formalism.CountingSumsFrames.typeProj_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:49.873644+00:00
-- url     : https://prove2.me/submissions/fbbe1443-ec62-4465-af3f-5976dc397a8e

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_isoC_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (c d : Fin r) :
    ∀ x, P (glAct p LL j c d x) = glAct p LL j c d (P x) :=
  typeProj_comm LL j T P hP _ (fun la => isoC_glStable LL j la c d)
end Formalism.CountingSumsFrames
