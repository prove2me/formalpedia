-- Prove2me | solution 1 for Formalism.CountingSumsFrames.typeProj_eul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:06.019035+00:00
-- url     : https://prove2.me/submissions/368d1044-94e9-4f7b-851b-3728b58b977d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_eul_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_isoC_keep
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_comm
import Theorems.Thm_Formalism_CountingSumsFrames_eul_hwc

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
    (hP : IsTypeProj p LL j univ T P) (i0 : Fin N) :
    ∀ x, P (ProjS.eulL (fun c : Fin r => (i0, c)) x) = ProjS.eulL (fun c : Fin r => (i0, c)) (P x) :=
  typeProj_comm LL j T P hP _ (fun la => isoC_keep LL j la _ (fun c d x => eul_glAct LL j i0 c d x)
    (eul_hwc LL j i0 la))
end Formalism.CountingSumsFrames
