-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:46:08.079802+00:00
-- url     : https://prove2.me/submissions/5ab7fbd8-c8ce-45f3-8a63-6f88d535d391

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_herm_smul_left
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_herm_smul_right
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_herm_sum_left
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_herm_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  rw [maxCuspsA_herm_sum_left]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [maxCuspsA_herm_smul_left, maxCuspsA_herm_sum_right]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)
  rw [maxCuspsA_herm_smul_right, cu.3 a b, mul_zero]
end Formalism.L2.Pj.QAt
