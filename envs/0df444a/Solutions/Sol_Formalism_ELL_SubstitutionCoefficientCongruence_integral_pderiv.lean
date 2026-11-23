-- Prove2me | solution 1 for Formalism.ELL.SubstitutionCoefficientCongruence.integral_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:10.67042+00:00
-- url     : https://prove2.me/submissions/4487abed-47ce-4b39-b368-47950de5f109

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
theorem _root_.solution {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (i : σ) :
    Formalism.G.IntegralMv (MvPowerSeries.pderiv K i F) := by
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_pderiv]
  refine Subring.mul_mem _ (mem_unitBall.2 (hF _)) ?_
  exact Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _)
end Formalism.ELL.SubstitutionCoefficientCongruence
