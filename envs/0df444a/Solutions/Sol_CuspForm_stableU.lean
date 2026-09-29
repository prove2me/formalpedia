-- Prove2me | solution 1 for CuspForm.stableU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ddd3743e-4049-55b8-872e-9ccdf02bf893

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_stableU

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.StableU M H k q := by
  intro f
  exact ⟨fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H k hq hqM
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k q,
    fun c hc => CuspFormClass.isZeroAt_heckeU f q hc⟩

end S_CuspForm_stableU
end P2MW
export P2MW.S_CuspForm_stableU (solution)
