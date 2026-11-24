-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.den_order_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:42.432004+00:00
-- url     : https://prove2.me/submissions/9cb9d301-c250-47b7-88f4-5bd1d4dd183b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_ind_of_mem
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_ind_of_notMem
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_den_order
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_count_sub
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_count_add

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
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) :
    meromorphicOrderAt (den L α S) z = 2 := by
  rw [den_order L α S hord he hb hα (fun P hP => (hS.1 P hP).2) z]
  by_cases hz : z ∈ L.lattice
  · rw [ind_of_mem L hz]
    have h0 : ∀ P ∈ S, ind L (z + P) + ind L (z - P) = 0 := by
      intro P hP
      have hPL := (hS.1 P hP).2
      rw [ind_of_notMem L (fun h => hPL (by simpa using L.lattice.sub_mem h hz)),
        ind_of_notMem L (fun h => hPL (by simpa using L.lattice.sub_mem hz h))]
      simp
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    rfl
  · rw [ind_of_notMem L hz, Finset.sum_add_distrib, count_add L α S hS z h1 hz, count_sub L α S hS z h1 hz]
    rfl
end Formalism.L2.Th1.F.IsogenySigmaQuotient
