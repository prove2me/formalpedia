-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integral_points_weight_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:49.948797+00:00
-- url     : https://prove2.me/submissions/66789903-783f-47e0-aa6e-db175913f1c4

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hs : IdealInversePowerSum) (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (T : Finset E) (hT : ∀ x ∈ T, IsIntegral ℤ x) :
    ∑ D ∈ T, ∏ w : InfinitePlace E, ((1 + (w D) ^ 2) ^ 2)⁻¹ ≤ 16 ^ Fintype.card (InfinitePlace E) := by
  have h := hs E 1 one_ne_zero (by simp) T (by
    intro D hD
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨⟨D, hT D hD⟩, rfl⟩)
  simpa using h
end Formalism.HermitianLatticeCounting.P
