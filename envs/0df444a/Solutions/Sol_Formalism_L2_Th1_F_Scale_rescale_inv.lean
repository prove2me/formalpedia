-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.rescale_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:23:09.46267+00:00
-- url     : https://prove2.me/submissions/c6f6c905-454a-4b9a-a970-e7daac5ec842

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Scale
open PowerSeries
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution {K : Type} [Field K] (lam : K) {f : PowerSeries K}
    (hf : constantCoeff f ≠ 0) : rescale lam f⁻¹ = (rescale lam f)⁻¹ := by
  have h1 : constantCoeff (rescale lam f) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
    exact hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h1, ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]
end Formalism.L2.Th1.F.Scale
