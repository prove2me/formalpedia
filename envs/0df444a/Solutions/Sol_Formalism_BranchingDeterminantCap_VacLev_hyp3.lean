-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.VacLev.hyp3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:29.86658+00:00
-- url     : https://prove2.me/submissions/f97a2e57-0d0b-498c-b488-d10450071656

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
open Formalism.BranchingDeterminantCap.VacLev
namespace Formalism.BranchingDeterminantCap.VacLev
theorem _root_.solution : ∀ a ∈ A, ((2 : ℕ) : ℤ) • e0 a ∈ A := by
  rintro ⟨x, y⟩ ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  simp only [] at hm hn
  have : ((2 : ℕ) : ℤ) • e0 (x, y) = (x + y, x + y) := by
    simp [io, e0]
  rw [this]
  refine ⟨⟨m + n, ?_⟩, ⟨m + n, ?_⟩⟩ <;> simp [← hm, ← hn]
end Formalism.BranchingDeterminantCap.VacLev
