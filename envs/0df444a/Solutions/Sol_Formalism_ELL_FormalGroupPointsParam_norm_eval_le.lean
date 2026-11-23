-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.norm_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:32.07485+00:00
-- url     : https://prove2.me/submissions/a53ca9cd-1f76-49c3-9dde-7a1b5d81469e

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.FormalGroupPointsParam
theorem _root_.solution [CompleteSpace K] {f : PowerSeries K} (hf : IntegralPS f) (h0 : coeff 0 f = 0)
    {t : K} (ht : ‖t‖ < 1) : ‖evalPS f t‖ ≤ ‖t‖ := by
  unfold evalPS
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg t)
  intro n
  rcases n with _ | n
  · simp [h0]
  · rw [norm_mul, norm_pow]
    calc ‖coeff (n + 1) f‖ * ‖t‖ ^ (n + 1) ≤ 1 * ‖t‖ ^ 1 :=
          mul_le_mul (hf _) (pow_le_pow_of_le_one (norm_nonneg _) ht.le (by omega))
            (by positivity) zero_le_one
      _ = ‖t‖ := by simp
end Formalism.ELL.FormalGroupPointsParam
