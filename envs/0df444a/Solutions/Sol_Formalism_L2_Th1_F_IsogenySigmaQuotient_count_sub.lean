-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.count_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:03.249548+00:00
-- url     : https://prove2.me/submissions/da725cb2-5b26-4812-bcc7-37e748560162

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
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) (h2 : z ∉ L.lattice) :
    ∑ P ∈ S, ind L (z - P) = 1 := by
  obtain ⟨P0, hP0, hz⟩ := hS.2.2 z h1 h2
  rw [Finset.sum_eq_single P0]
  · exact ind_of_mem L hz
  · intro b hb hne
    apply ind_of_notMem L
    intro hb'
    apply hne
    apply hS.2.1 b hb P0 hP0
    have e : b - P0 = (z - P0) - (z - b) := by ring
    rw [e]; exact L.lattice.sub_mem hz hb'
  · intro h; exact absurd hP0 h
end Formalism.L2.Th1.F.IsogenySigmaQuotient
