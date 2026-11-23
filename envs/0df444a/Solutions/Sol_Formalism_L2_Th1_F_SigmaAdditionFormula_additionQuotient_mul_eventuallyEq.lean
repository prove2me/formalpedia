-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_mul_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:49.555555+00:00
-- url     : https://prove2.me/submissions/3a60efe8-7f27-4387-8fd0-4b37fc066811

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_sigma_zero
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
private lemma eventually_not_mem_lattice_punctured_zero : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have hD : DiscreteTopology (L.lattice : Set ℂ) := (inferInstance : DiscreteTopology L.lattice)
  exact Filter.inf_principal_eq_bot.1 (discreteTopology_subtype_iff.1 hD 0 L.lattice.zero_mem)
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
theorem _root_.solution (hz : SigmaZero) :
    (fun z => additionQuotient L w z * wSigma L z ^ 2) =ᶠ[𝓝[≠] 0] frobeniusStickelbergerDetMulSigmaCube L w := by
  filter_upwards [eventually_not_mem_lattice_punctured_zero L, self_mem_nhdsWithin] with z hzL hz0
  have hσ : wSigma L z ≠ 0 := fun h => hzL ((hz L z).1 h)
  have hz0' : z ≠ 0 := hz0
  have h0 := sigma_zero L hz
  have hd : dslope (wSigma L) 0 z = wSigma L z / z := by
    rw [dslope_of_ne _ hz0', slope_def_field, h0, sub_zero, sub_zero]
  unfold additionQuotient frobeniusStickelbergerDetMulSigmaCube
  rw [weierstrassP_eq_except_zero_add_inv_sq L z, hd]
  field_simp
  ring
end Formalism.L2.Th1.F.SigmaAdditionFormula
