-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.integralMv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.231489+00:00
-- url     : https://prove2.me/submissions/0a203507-2499-461e-a8da-48886c1f0c83

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne

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
theorem _root_.solution {σ : Type*} {f g : MvPowerSeries σ K} (hf : IntegralMv f)
    (hg : IntegralMv g) : IntegralMv (f * g) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)
end Formalism.ELL.PadicLogarithmSubstitution
