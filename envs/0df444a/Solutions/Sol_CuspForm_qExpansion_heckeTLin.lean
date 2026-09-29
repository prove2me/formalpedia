-- Prove2me | solution 1 for CuspForm.qExpansion_heckeTLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e26dd376-8241-5e22-b0e1-728354face05

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModularFormClass_qExpansion_heckeT_eq_heckeT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qExpansion_heckeTLin

theorem solution {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    UpperHalfPlane.qExpansion 1 ⇑(CuspForm.heckeTLin 2 hp hpN f)
      = PowerSeries.heckeT p 2 (UpperHalfPlane.qExpansion 1 ⇑f) := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  rw [CuspForm.coe_heckeTLin_apply]
  exact ModularFormClass.qExpansion_heckeT_eq_heckeT (k := 2) f hΓ hp.ne_zero (by norm_num)

end S_CuspForm_qExpansion_heckeTLin
end P2MW
export P2MW.S_CuspForm_qExpansion_heckeTLin (solution)
