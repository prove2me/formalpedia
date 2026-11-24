-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.exists_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:38.444856+00:00
-- url     : https://prove2.me/submissions/11055336-cf29-4a53-8282-cf7c579bfcdd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_num_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_den_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_mem_of_den_eq_zero
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_quot_order
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_quot_periodic

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
theorem _root_.solution (hN : EllipticNoPole) (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic)
    (hq : SgStarQuasi) (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S)
    (hc : (S.card : ℝ) + 1 = Complex.normSq α) :
    ∃ c : ℂ, ∀ z, num L α z = c * den L α S z := by
  have hmer : ∀ z, MeromorphicAt (fun w => num L α w / den L α S w) z := fun z =>
    (num_analyticAt L α hb z).meromorphicAt.div (den_analyticAt L α S hb z).meromorphicAt
  obtain ⟨c, hc'⟩ := hN L _ hmer (quot_periodic L α S hq hst hc) (quot_order L α S hord he hb hα hst hS)
  refine ⟨c, fun z => ?_⟩
  by_cases h0 : den L α S z = 0
  · rw [h0, mul_zero]
    have hm := mem_of_den_eq_zero L α S hb hα hst hS z h0
    simp [num, ((hb L).2.2.1 _).2 hm]
  · have hcont : ContinuousAt (fun w => num L α w / den L α S w) z :=
      (num_analyticAt L α hb z).continuousAt.div (den_analyticAt L α S hb z).continuousAt h0
    exact (div_eq_iff h0).1 (hc' z hcont)
end Formalism.L2.Th1.F.IsogenySigmaQuotient
