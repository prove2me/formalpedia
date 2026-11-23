-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.chain_weights
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:20.31282+00:00
-- url     : https://prove2.me/submissions/838c023d-7a74-4a8b-a07a-7b822c4ef873

import Definitions.Def_Formalism_BranchSandwichDivisors_DualLevelType
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : ChainWeights := by
  intro top e blk u i k t m h0 hs hb0 hbs
  constructor
  · have key : ∀ j : ℕ, top j = u - ((k + (j : ℝ) * (t + 1)) + 1) / 2 + i := by
      intro j
      induction j with
      | zero => rw [h0]; push_cast; ring
      | succ j ih => rw [hs j, ih]; push_cast; ring
    exact key m
  · intro j hj
    have key : ∀ d : ℕ, blk (j + 1) (j + 1 + d) =
        -e (j + 1) + k / 2 + (2 * ((j : ℝ) + 1) - 1 - ((j : ℝ) + 1 + (d : ℝ))) * (t + 1) / 2 := by
      intro d
      induction d with
      | zero => rw [Nat.add_zero, hb0 j]; push_cast; ring
      | succ d ih =>
        rw [← Nat.add_assoc, hbs j (j + 1 + d) (Nat.le_add_right _ _), ih]; push_cast; ring
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [key d]; push_cast; ring
end Formalism.BranchingDeterminantCap
