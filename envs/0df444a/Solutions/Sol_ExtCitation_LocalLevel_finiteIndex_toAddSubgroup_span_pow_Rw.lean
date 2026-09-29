-- Prove2me | solution 1 for ExtCitation.LocalLevel.finiteIndex_toAddSubgroup_span_pow_Rw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a3a4b201-a4dc-5a21-8bf4-71b65af6abed

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_finiteIndex_toAddSubgroup_span_pow_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel

open scoped NNReal

open ExtCitation.LocalLevel IsLocalRing in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (N : ℕ) :
    (Ideal.span {((q : ℕ) : Rw q Kw) ^ N}).toAddSubgroup.FiniteIndex := by
  obtain ⟨e, f, -, -, hspan, -, -⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q Kw
  have h : Ideal.span {((q : ℕ) : Rw q Kw) ^ N} = IsLocalRing.maximalIdeal (Rw q Kw) ^ (e * N) := by
    rw [← Ideal.span_singleton_pow, hspan, ← pow_mul]
  rw [h]
  exact (ExtCitation.LocalLevel.index_toAddSubgroup_maximalIdeal_pow_Rw q Kw (e * N)).1

end S_ExtCitation_LocalLevel_finiteIndex_toAddSubgroup_span_pow_Rw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_finiteIndex_toAddSubgroup_span_pow_Rw (solution)
