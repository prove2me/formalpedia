-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_herm_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:22.205477+00:00
-- url     : https://prove2.me/submissions/f35fedc1-892e-4081-8f72-20930b0d7ba7

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_herm_add_left

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
theorem _root_.solution {ι : Type} (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) :
    herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [herm]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, maxCuspsA_herm_add_left, ih]
end Formalism.L2.Pj.QAt
