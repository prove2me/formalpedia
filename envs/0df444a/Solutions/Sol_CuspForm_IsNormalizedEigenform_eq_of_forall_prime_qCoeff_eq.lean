-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.eq_of_forall_prime_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b12d3349-0671-508d-82fa-a3bbb9939144

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_forall_prime_qCoeff_eq
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq

open ModularFormClass

theorem solution {N : ℕ}
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (hg : g.IsNormalizedEigenform)
    (h : ∀ p : ℕ, p.Prime → qCoeff f p = qCoeff g p) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq
    (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1)
    (CuspForm.IsNormalizedEigenform.qCoeff_eq_of_forall_prime_qCoeff_eq hf hg h)

end S_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq (solution)
