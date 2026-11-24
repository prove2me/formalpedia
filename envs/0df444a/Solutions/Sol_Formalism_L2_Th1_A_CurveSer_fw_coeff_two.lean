-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.fw_coeff_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:25.565366+00:00
-- url     : https://prove2.me/submissions/f0f06741-3fce-4e38-b66e-95e7673d37a5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.CurveSer
theorem _root_.solution : coeff 2 (fw W) = -W.a₂ := by
  rw [fw_eq W]
  simp [coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_one, coeff_C_mul]
end Formalism.L2.Th1.A.CurveSer
