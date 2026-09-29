-- Prove2me | solution 1 for CuspForm.exists_coe_eq_heckeU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2aa7bd64-3897-5261-bbcd-912e53f250d6

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_coe_eq_heckeU

theorem solution {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hpN : p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f :=
  ⟨{ toFun := ModularForm.heckeU k p ⇑f
     slash_action_eq' := fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 k hpN
       (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
     holo' := ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k p
     zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f p hc }, rfl⟩

end S_CuspForm_exists_coe_eq_heckeU
end P2MW
export P2MW.S_CuspForm_exists_coe_eq_heckeU (solution)
