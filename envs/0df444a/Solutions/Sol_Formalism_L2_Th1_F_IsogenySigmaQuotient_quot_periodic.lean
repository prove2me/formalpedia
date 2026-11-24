-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.quot_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:31.322837+00:00
-- url     : https://prove2.me/submissions/310956f5-b735-4d58-9939-149c78a356eb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_den_add
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_num_add

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
theorem _root_.solution (hq : SgStarQuasi) (hst : MulStable L α)
    (hc : (S.card : ℝ) + 1 = Complex.normSq α) :
    IsPeriodic L (fun w => num L α w / den L α S w) := by
  intro ω hω z
  show num L α (z + ω) / den L α S (z + ω) = num L α z / den L α S z
  rw [num_add L α S hq hst hc ω z hω, den_add L α S hq ω z hω]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ (by simp only [mlt]; exact Complex.exp_ne_zero _)))
end Formalism.L2.Th1.F.IsogenySigmaQuotient
