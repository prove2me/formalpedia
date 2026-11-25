-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.ind_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:22:07.759579+00:00
-- url     : https://prove2.me/submissions/577198f4-9386-4366-b80a-c9e5ddec525a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_ind_of_mem
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_ind_of_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (x : ℂ) : ind L (-x) = ind L x := by
  by_cases hx : x ∈ L.lattice
  · rw [ind_of_mem L hx, ind_of_mem L (L.lattice.neg_mem hx)]
  · rw [ind_of_notMem L hx, ind_of_notMem L (fun h => hx (by simpa using L.lattice.neg_mem h))]
end Formalism.L2.Th1.F.IsogenySigmaQuotient
