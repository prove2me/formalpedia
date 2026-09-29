-- Prove2me | solution 1 for ExtCitation.LocalLevel.index_toAddSubgroup_maximalIdeal_pow_Rw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bbed3d6f-a416-5660-ab9f-85c9a355f0ac

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel

open scoped NNReal

open ExtCitation.LocalLevel IsLocalRing in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (n : ℕ) :
    (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.FiniteIndex ∧
      (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.index
        = Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ n := by
  haveI : IsDiscreteValuationRing (Rw q Kw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Kw
  haveI : Finite (ResidueField (Rw q Kw)) := ExtCitation.LocalLevel.finite_residueField_Rw q Kw
  have hidx : (maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.index = Nat.card (ResidueField (Rw q Kw)) ^ n := by
    rw [AddSubgroup.index_eq_card]
    exact IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow n
  refine ⟨⟨?_⟩, hidx⟩
  rw [hidx]
  exact pow_ne_zero _ (Nat.card_pos (α := ResidueField (Rw q Kw))).ne'

end S_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw (solution)
