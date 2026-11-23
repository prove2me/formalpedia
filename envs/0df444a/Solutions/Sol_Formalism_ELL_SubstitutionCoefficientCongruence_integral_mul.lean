-- Prove2me | solution 1 for Formalism.ELL.SubstitutionCoefficientCongruence.integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:15.291136+00:00
-- url     : https://prove2.me/submissions/3adce62c-45d9-4dd5-8af9-f7333e99d3ed

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_mem_unitBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
namespace Formalism.ELL.SubstitutionCoefficientCongruence
theorem _root_.solution {F G : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F)
    (hG : Formalism.G.IntegralMv G) : Formalism.G.IntegralMv (F * G) := by
  classical
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ =>
    Subring.mul_mem _ (mem_unitBall.2 (hF _)) (mem_unitBall.2 (hG _))
end Formalism.ELL.SubstitutionCoefficientCongruence
