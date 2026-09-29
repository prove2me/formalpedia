-- Prove2me | solution 1 for CuspForm.atkinLehnerLin_atkinLehnerLin_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/24e84b97-fe6f-53d0-8f77-aae0abf29682

import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_ModularForm_alSlash_alSlash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul

open ModularForm

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul coe_smul atkinLehnerLin coe_atkinLehnerLin_apply"
p2m_open "CuspForm"
variable {M q : ℕ}
theorem wc_sq [NeZero M] (W : AtkinLehnerDatum M q) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    atkinLehnerLin W k (atkinLehnerLin W k f) = ((q : ℂ) ^ (k - 2)) • f := by
  apply DFunLike.coe_injective
  show ⇑(atkinLehnerLin W k (atkinLehnerLin W k f)) = ⇑(((q : ℂ) ^ (k - 2)) • f)
  rw [coe_atkinLehnerLin_apply, coe_atkinLehnerLin_apply, CuspForm.IsGLPos.coe_smul]
  exact ModularForm.alSlash_alSlash W k (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)

end CuspForm

theorem solution {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.atkinLehnerLin W k (CuspForm.atkinLehnerLin W k f) = ((q : ℂ) ^ (k - 2)) • f :=
  CuspForm.wc_sq W k f

end S_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul
end P2MW
export P2MW.S_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul (solution)
