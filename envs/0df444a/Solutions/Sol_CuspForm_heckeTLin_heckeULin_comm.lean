-- Prove2me | solution 1 for CuspForm.heckeTLin_heckeULin_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/84800b90-33d8-5727-83e3-b99766941ba4

import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_heckeT_heckeU_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeTLin_heckeULin_comm

theorem solution {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) := by
  rw [commute_iff_eq]; ext f τ
  simpa using congrFun (ModularFormClass.heckeT_heckeU_comm f (by simp)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (h.trans hqN))) τ

end S_CuspForm_heckeTLin_heckeULin_comm
end P2MW
export P2MW.S_CuspForm_heckeTLin_heckeULin_comm (solution)
