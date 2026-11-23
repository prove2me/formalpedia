-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.absSum_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:51.344727+00:00
-- url     : https://prove2.me/submissions/3645d8ea-4a40-4685-b6b2-235fbdfffbf1

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K]
variable [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsParam
theorem _root_.solution {f : PowerSeries K} (hf : IntegralPS f) {t : K} (ht : ‖t‖ < 1) :
    AbsSum f t := by
  refine (summable_geometric_of_lt_one (norm_nonneg t) ht).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hf n)
end Formalism.ELL.FormalGroupPointsParam
