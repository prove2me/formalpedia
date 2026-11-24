-- Prove2me | solution 1 for Formalism.L2.Th1.F.EvenThetaIsogeny.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:55.763843+00:00
-- url     : https://prove2.me/submissions/7cd63a19-d79e-4290-b195-51f8b86ace4e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MemOfDenEqZero
import Theorems.Thm_Formalism_L2_Th1_F_EvenThetaIsogeny_mem_of_eq
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
open Formalism.L2.Th1.F.EvenThetaIsogeny
open IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α t : ℂ) (T : Finset ℂ)
namespace Formalism.L2.Th1.F.EvenThetaIsogeny
theorem _root_.solution (hT : IsFibreReps L α t T) (z : ℂ) (hz : α * z - t ∈ L.lattice) :
    ∑ Q ∈ T, (ind L (z + Q) + ind L (z - Q)) = 1 := by
  obtain ⟨Q, hQ, hzQ⟩ := hT.2.2 z hz
  rw [Finset.sum_eq_single Q]
  · rcases hzQ with h | h
    · rw [ind_of_mem L h, ind_of_notMem L, zero_add]
      exact fun h' => (hT.1 Q hQ).2 (mem_of_eq L (sub_mem h' h) (by ring))
    · rw [ind_of_mem L h, ind_of_notMem L, add_zero]
      exact fun h' => (hT.1 Q hQ).2 (mem_of_eq L (sub_mem h h') (by ring))
  · intro Q' hQ' hne
    rw [ind_of_notMem L, ind_of_notMem L, add_zero]
    · intro h'
      refine hne (hT.2.1 Q' hQ' Q hQ ?_)
      rcases hzQ with h | h
      · exact Or.inl (mem_of_eq L (sub_mem h h') (by ring))
      · exact Or.inr (mem_of_eq L (sub_mem h h') (by ring))
    · intro h'
      refine hne (hT.2.1 Q' hQ' Q hQ ?_)
      rcases hzQ with h | h
      · exact Or.inr (mem_of_eq L (sub_mem h' h) (by ring))
      · exact Or.inl (mem_of_eq L (sub_mem h' h) (by ring))
  · intro h
    exact absurd hQ h
end Formalism.L2.Th1.F.EvenThetaIsogeny
