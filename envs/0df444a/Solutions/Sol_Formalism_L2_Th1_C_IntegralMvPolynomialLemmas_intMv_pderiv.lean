-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:27.367218+00:00
-- url     : https://prove2.me/submissions/9b053193-3357-43e9-929f-560a0002b6a3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {R : Subring K}
namespace Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
theorem _root_.solution {F : MvPowerSeries σ K} (hF : IntMv R F) (i : σ) :
    IntMv R (MvPowerSeries.pderiv K i F) := by
  intro d
  rw [MvPowerSeries.coeff_pderiv]
  exact Subring.mul_mem _ (hF _) (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _))
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
