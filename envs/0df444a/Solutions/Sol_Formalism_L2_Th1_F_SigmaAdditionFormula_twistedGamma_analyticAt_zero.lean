-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.twistedGamma_analyticAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:51.134885+00:00
-- url     : https://prove2.me/submissions/439eb783-3bbe-419e-8924-5d6ac9cbda8a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_analyticAt_dslope

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
namespace Formalism.L2.Th1.F.SigmaAdditionFormula
theorem _root_.solution (he : SigmaEntire) : AnalyticAt ℂ (frobeniusStickelbergerDetMulSigmaCube L w) 0 := by
  have hσd : Differentiable ℂ (wSigma L) := he L
  have hs : ∀ c : ℂ, AnalyticAt ℂ (fun z => wSigma L (z + c)) 0 := fun c =>
    (hσd.comp (differentiable_id.add_const c)).analyticAt 0
  have hs' : ∀ c : ℂ, AnalyticAt ℂ (fun z => wSigma L (z - c)) 0 := fun c =>
    (hσd.comp (differentiable_id.sub_const c)).analyticAt 0
  have hP : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 :=
    L.analyticOnNhd_weierstrassPExcept 0 0 (by simp)
  have hd := analyticAt_dslope L he
  have hσ : AnalyticAt ℂ (wSigma L) 0 := hσd.analyticAt 0
  exact ((hs w).mul (hs' w)).add (analyticAt_const.mul ((hd.pow 2).add ((hσ.pow 2).mul hP)))
end Formalism.L2.Th1.F.SigmaAdditionFormula
