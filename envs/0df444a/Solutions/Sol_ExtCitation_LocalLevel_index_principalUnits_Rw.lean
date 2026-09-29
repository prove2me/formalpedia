-- Prove2me | solution 1 for ExtCitation.LocalLevel.index_principalUnits_Rw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/525f8c3c-d0c9-5878-b644-0a36d1dedb07

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_IsLocalRing_index_principalUnits_one
import Theorems.Thm_IsDiscreteValuationRing_relIndex_principalUnits_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_index_principalUnits_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel IsLocalRing

open scoped NNReal

open IsLocalRing ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] {k : ℕ} (hk : 1 ≤ k) :
    (principalUnits (Rw q Kw) k).FiniteIndex ∧
      (principalUnits (Rw q Kw) k).index
        = (Nat.card (IsLocalRing.ResidueField (Rw q Kw)) - 1) * Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ (k - 1) := by
  haveI : IsDiscreteValuationRing (Rw q Kw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Kw
  haveI : Finite (ResidueField (Rw q Kw)) := ExtCitation.LocalLevel.finite_residueField_Rw q Kw
  haveI : Fintype (ResidueField (Rw q Kw)) := Fintype.ofFinite _
  have h1 : (principalUnits (Rw q Kw) 1).index = Nat.card (ResidueField (Rw q Kw)) - 1 := by
    rw [IsLocalRing.index_principalUnits_one, Nat.card_units]
  have hrel : (principalUnits (Rw q Kw) k).relIndex (principalUnits (Rw q Kw) 1)
      = Nat.card (ResidueField (Rw q Kw)) ^ (k - 1) := by
    have := IsDiscreteValuationRing.relIndex_principalUnits_add (R := Rw q Kw) le_rfl (k - 1)
    rwa [Nat.add_sub_cancel' hk] at this
  have hidx : (principalUnits (Rw q Kw) k).index
      = (Nat.card (ResidueField (Rw q Kw)) - 1) * Nat.card (ResidueField (Rw q Kw)) ^ (k - 1) := by
    rw [← Subgroup.relIndex_mul_index (principalUnits_antitone hk), hrel, h1, mul_comm]
  refine ⟨⟨?_⟩, hidx⟩
  rw [hidx]
  have hc : 1 < Nat.card (ResidueField (Rw q Kw)) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  exact mul_ne_zero (by omega) (pow_ne_zero _ (by omega))

end S_ExtCitation_LocalLevel_index_principalUnits_Rw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_index_principalUnits_Rw (solution)
