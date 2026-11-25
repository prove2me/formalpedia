-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:55.211666+00:00
-- url     : https://prove2.me/submissions/fec1a699-af93-4e8f-865b-0d5bbca6cee9

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_mc_cc_add

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
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, mc_cc_add, mul_add, Finset.sum_add_distrib]
end Formalism.L2.Pj.QAt
