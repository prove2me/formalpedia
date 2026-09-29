-- Prove2me | solution 1 for CuspForm.hasIntegralBasis_iff_hasIntegralStructure_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e42448f6-7910-5a2d-a6e2-d46e58328109

import Mathlib
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two

theorem solution (N : ℕ) : CuspForm.HasIntegralBasis N ↔ CuspForm.HasIntegralStructure N 2 := by
  have hset : CuspForm.qIntegralSet N =
      {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2 | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)} := by
    ext f
    simp only [CuspForm.qIntegralSet, Set.mem_setOf_eq]
    refine forall_congr' fun n => ?_
    rw [Subring.mem_bot]
    exact ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩
  unfold CuspForm.HasIntegralBasis CuspForm.HasIntegralStructure CuspForm.intLattice
  rw [hset, Submodule.span_span_of_tower]

end S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two
end P2MW
export P2MW.S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two (solution)
