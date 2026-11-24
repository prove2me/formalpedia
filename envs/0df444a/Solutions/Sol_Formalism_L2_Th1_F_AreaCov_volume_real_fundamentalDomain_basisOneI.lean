-- Prove2me | solution 1 for Formalism.L2.Th1.F.AreaCov.volume_real_fundamentalDomain_basisOneI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:19:34.668621+00:00
-- url     : https://prove2.me/submissions/be34bc6c-cb8f-4cb4-9973-b5988c7156bb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AreaCov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.AreaCov
namespace Formalism.L2.Th1.F.AreaCov
theorem _root_.solution :
    (volume : Measure ℂ).real (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
  have hset : ZSpan.fundamentalDomain Complex.basisOneI =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    rw [Set.mem_preimage]
    change _ ↔ (z.re, z.im) ∈ Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1
    simp [ZSpan.mem_fundamentalDomain, Fin.forall_fin_two, Complex.coe_basisOneI_repr, Set.mem_prod]
  show (volume (ZSpan.fundamentalDomain Complex.basisOneI)).toReal = 1
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]
  simp
end Formalism.L2.Th1.F.AreaCov
