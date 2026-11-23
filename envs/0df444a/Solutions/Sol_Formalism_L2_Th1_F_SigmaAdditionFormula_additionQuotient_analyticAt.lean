-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:49.553571+00:00
-- url     : https://prove2.me/submissions/baf43224-99ec-4ecc-aa41-a6b13c28f1a9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
namespace Formalism.L2.Th1.F
namespace SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
private lemma weierstrassP_eq_except_zero_add_inv_sq (z : ℂ) : L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  rw [← L.weierstrassPExcept_add 0 z]
  simp
end SigmaAdditionFormula
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
namespace Formalism.L2.Th1.F.SigmaAdditionFormula
theorem _root_.solution (he : SigmaEntire) (hz : SigmaZero) (z : ℂ) (hzL : z ∉ L.lattice) :
    AnalyticAt ℂ (additionQuotient L w) z := by
  have hσd : Differentiable ℂ (wSigma L) := he L
  have a1 : AnalyticAt ℂ (fun x => wSigma L (x + w)) z :=
    (hσd.comp (differentiable_id.add_const w)).analyticAt z
  have a2 : AnalyticAt ℂ (fun x => wSigma L (x - w)) z :=
    (hσd.comp (differentiable_id.sub_const w)).analyticAt z
  have a3 : AnalyticAt ℂ (wSigma L) z := hσd.analyticAt z
  have hσz : wSigma L z ≠ 0 := fun h => hzL ((hz L z).1 h)
  have hz0 : z ∉ (L.lattice : Set ℂ) \ {0} := fun h => hzL h.1
  have hzne : z ≠ 0 := by
    rintro rfl
    exact hzL L.lattice.zero_mem
  have hP : AnalyticAt ℂ L.weierstrassP z := by
    rw [show L.weierstrassP = fun x => L.weierstrassPExcept 0 x + 1 / x ^ 2 from funext (weierstrassP_eq_except_zero_add_inv_sq L)]
    exact (L.analyticOnNhd_weierstrassPExcept 0 z hz0).add
      (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero _ hzne))
  exact ((a1.mul a2).div (a3.pow 2) (pow_ne_zero _ hσz)).add (analyticAt_const.mul hP)
end Formalism.L2.Th1.F.SigmaAdditionFormula
