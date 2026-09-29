-- Prove2me | solution 1 for CuspForm.atkinLehnerLin_atkinLehnerLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2ea276ac-8b53-5cdf-9981-3309e420a7fe

import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_atkinLehnerLin_atkinLehnerLin

open ModularForm

namespace CuspForm
p2m_export "CuspForm" "atkinLehnerLin atkinLehnerLin_atkinLehnerLin_eq_smul"
p2m_open "CuspForm"
variable {M q : ℕ}
end CuspForm

theorem solution {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.atkinLehnerLin W 2 (CuspForm.atkinLehnerLin W 2 f) = f := by
  rw [CuspForm.atkinLehnerLin_atkinLehnerLin_eq_smul]
  norm_num

end S_CuspForm_atkinLehnerLin_atkinLehnerLin
end P2MW
export P2MW.S_CuspForm_atkinLehnerLin_atkinLehnerLin (solution)
