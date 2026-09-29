-- Prove2me | solution 1 for CuspForm.isNormalizedEigenform_iff_heckeT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2923eb56-2b54-5f14-b47a-9e9c4b2415f6

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_ModularFormClass_heckeT_eq_smul_iff
import Theorems.Thm_ModularFormClass_heckeU_eq_smul_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeT

set_option autoImplicit false

noncomputable section

open Complex Function Filter
p2m_open "UpperHalfPlane~I"
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

theorem solution {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime → ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧ (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f))) := by
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N
  rw [CuspForm.isNormalizedEigenform_iff_coeffHecke]
  refine and_congr_right fun _ ↦ forall_congr' fun p ↦ forall_congr' fun hp ↦ ?_
  rw [ModularFormClass.heckeT_eq_smul_iff f hΓ hp.ne_zero, ModularFormClass.heckeU_eq_smul_iff f hΓ hp.ne_zero]

end

end S_CuspForm_isNormalizedEigenform_iff_heckeT
end P2MW
export P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeT (solution)
