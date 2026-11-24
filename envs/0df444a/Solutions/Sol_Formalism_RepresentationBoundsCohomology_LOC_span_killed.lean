-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.span_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:35.446464+00:00
-- url     : https://prove2.me/submissions/f8d41677-6995-4d20-bd70-a371786ecb7d

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
theorem _root_.solution {N : Type u} [AddCommGroup N] [Module O N]
    (ht : ∀ x : N, ∃ c : O, c ≠ 0 ∧ c • x = 0) (t : Finset N) :
    ∃ c : O, c ≠ 0 ∧ ∀ n ∈ Submodule.span O (t : Set N), c • n = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert x t _ ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := ht x
    refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
    intro n hn
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hn
    obtain ⟨r, z, hz, rfl⟩ := hn
    rw [smul_add, mul_smul, smul_comm c' r x, h', smul_zero, smul_zero, zero_add, mul_comm,
      mul_smul, h z hz, smul_zero]
end Formalism.RepresentationBoundsCohomology.LOC
