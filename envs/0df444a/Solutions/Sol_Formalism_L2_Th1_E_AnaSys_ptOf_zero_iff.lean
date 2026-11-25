-- Prove2me | solution 1 for Formalism.L2.Th1.E.AnaSys.ptOf_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:53.457053+00:00
-- url     : https://prove2.me/submissions/bce79e40-b539-4f4b-8770-9547a7980a28

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_ptOf_notMem
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_ptOf_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AnaSys
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
variable {l L ι}
variable (l L ι)
namespace Formalism.L2.Th1.E.AnaSys
theorem _root_.solution (t : ℂ) : ptOf l L ι t = 0 ↔ t ∈ L.lattice := by
  constructor
  · intro h
    by_contra ht
    rw [ptOf_notMem l L ι t ht] at h
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h
  · exact ptOf_mem l L ι t
end Formalism.L2.Th1.E.AnaSys
