-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.den_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:40.544812+00:00
-- url     : https://prove2.me/submissions/b1004ad7-fef5-4d2a-9df8-210c8d7f3401

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_sq_add
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_fac_add

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
theorem _root_.solution (hq : SgStarQuasi) (ω z : ℂ) (hω : ω ∈ L.lattice) :
    den L α S (z + ω) = (mlt L ω z ^ 2) ^ (S.card + 1) * den L α S z := by
  simp only [den]
  rw [sg_sq_add L hq ω z hω, Finset.prod_congr rfl (fun P _ => fac_add L hq P ω z hω),
    Finset.prod_mul_distrib, Finset.prod_const]
  ring
end Formalism.L2.Th1.F.IsogenySigmaQuotient
