-- Prove2me | solution 1 for DensInertW.Sub.hf_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:33:27.4991+00:00
-- url     : https://prove2.me/submissions/b5f2901e-5570-4df8-9e5a-ce0fb265bfa0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW.Sub
theorem _root_.solution (hq : q ≠ 0) (x : Fin n → L) : hf q M x 0 = 0 := by
  simp [hf, zero_pow hq]
end DensInertW.Sub
