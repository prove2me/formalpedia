-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.integralMv_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:53.200581+00:00
-- url     : https://prove2.me/submissions/d5a2f593-5a0f-4bc2-960b-389de9901ada

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_integralMv_pow
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_norm_finsum_le_one

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
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution {σ : Type*} {a : PowerSeries K} (ha : IntegralPS a)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0) (hf : IntegralMv f) :
    IntegralMv (a.subst f) := by
  intro d
  rw [PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hf0)]
  refine norm_finsum_le_one (fun n => ?_)
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (ha n) (norm_nonneg _) (integralMv_pow hf n d)
end Formalism.ELL.PadicLogarithmSubstitution
