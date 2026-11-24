-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.KO_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:49.85902+00:00
-- url     : https://prove2.me/submissions/177c3048-6cfc-4699-b165-a8eee666dea8

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution (z : KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) x
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨r, ?_⟩
  rw [Algebra.smul_def, mul_comm]
  exact hrs.symm
end Formalism.RepresentationBoundsCohomology.LOC
