-- Prove2me | solution 1 for CuspForm.heckeULin_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a3d29882-3a25-524d-bcfa-f938897fcf12

import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_heckeU_heckeU_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeULin_comm

theorem solution {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hpN : p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeULin k hpN) (CuspForm.heckeULin k hqN) := by
  rw [commute_iff_eq]; ext f τ
  simpa using congrFun (ModularFormClass.heckeU_heckeU_comm f (by simp) p q) τ

end S_CuspForm_heckeULin_comm
end P2MW
export P2MW.S_CuspForm_heckeULin_comm (solution)
