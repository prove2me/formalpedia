-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.sum_y_sImg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:54:26.154724+00:00
-- url     : https://prove2.me/submissions/06db9267-9b2c-4a82-af7f-662945cd0437

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Theorems.Thm_Formalism_L2_Pj_LocAlg_yv_self
import Theorems.Thm_Formalism_L2_Pj_LocAlg_yv_succAbove
import Theorems.Thm_Formalism_L2_Pj_LocAlg_sImg_self
import Theorems.Thm_Formalism_L2_Pj_LocAlg_sImg_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution (jc : Fin (N + 1)) (x : Fin N → Ω) {i : Fin (D + 1)} (hi : i ≠ 0) :
    ∑ j, algebraMap Ω (OmS Ω D N) (yv jc x j) * sImg jc x (i, j) = 0 := by
  rw [Fin.sum_univ_succAbove _ jc, yv_self, sImg_self, if_neg hi]
  simp only [yv_succAbove, sImg_succAbove, map_one, one_mul, map_neg, map_sum, map_mul]
  rw [neg_add_eq_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
    MvPolynomial.algebraMap_eq, mul_comm]
end Formalism.L2.Pj.LocAlg
