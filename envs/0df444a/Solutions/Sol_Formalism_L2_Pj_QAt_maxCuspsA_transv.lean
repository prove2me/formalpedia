-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_transv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:13.500419+00:00
-- url     : https://prove2.me/submissions/d0380aff-e3c5-4bee-a45b-851e64dfaebd

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_max_cusps_rank_one_expand
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_vec_apply
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply


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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) (α : E) :
    transvMat X.Gm (∑ a, η a • cu.e a) α = zMatE X cu.e (α • mcMη η) := by
  ext k l
  have hv := maxCuspsA_vec_apply cu.e η
  simp only [transvMat, zMatE, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mcMη, hv]
  congr 1
  exact max_cusps_rank_one_expand (IsCMField.complexConj E : E →+* E) X.Gm η cu.e α k l
end Formalism.L2.Pj.QAt
