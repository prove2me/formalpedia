-- Prove2me | solution 1 for CuspForm.isNormalizedEigenform_iff_heckeTLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a3a15603-65aa-5890-9d2d-56bdc0d3023e

import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeTLin

theorem solution {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime),
      ((hpN : ¬ p ∣ N) → CuspForm.heckeTLin 2 hp hpN f = ModularFormClass.qCoeff f p • f) ∧
      ((hpN : p ∣ N) → CuspForm.heckeULin 2 hpN f = ModularFormClass.qCoeff f p • f)) := by
  rw [CuspForm.isNormalizedEigenform_iff_heckeT]
  simp only [DFunLike.ext'_iff (f := CuspForm.heckeTLin 2 _ _ f), DFunLike.ext'_iff (f := CuspForm.heckeULin 2 _ f),
    CuspForm.coe_heckeTLin_apply, CuspForm.coe_heckeULin_apply, CuspForm.IsGLPos.coe_smul]

end S_CuspForm_isNormalizedEigenform_iff_heckeTLin
end P2MW
export P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeTLin (solution)
