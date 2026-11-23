-- Prove2me | solution 1 for Formalism.CountingSumsFrames.typeProj_ycond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:25.897182+00:00
-- url     : https://prove2.me/submissions/86de4bd8-d467-4625-ba07-7772fdf44fea

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_keep
import Theorems.Thm_Formalism_CountingSumsFrames_comm_preserves_weight_le
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_glAct

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
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (Mt : WithTop ℤ) :
    ∀ x ∈ YCond p (r := r) LL j Mt, P x ∈ YCond p (r := r) LL j Mt :=
  ycond_keep LL j Mt P (typeProj_glAct LL j T P hP) (comm_preserves_weight_le LL j Mt P (typeProj_glAct LL j T P hP 0 0))
end Formalism.CountingSumsFrames
