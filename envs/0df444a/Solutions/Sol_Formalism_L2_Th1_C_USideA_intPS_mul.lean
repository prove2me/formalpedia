-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.intPS_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:33.194954+00:00
-- url     : https://prove2.me/submissions/673d455a-237d-4874-9032-2780bd45075b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA

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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.USideA
theorem _root_.solution {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f * g) := fun n => by
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem (fun p _ => R.mul_mem (hf _) (hg _))
end Formalism.L2.Th1.C.USideA
