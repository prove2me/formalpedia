-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.weyl_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:26.679747+00:00
-- url     : https://prove2.me/submissions/ae2462b5-ddb6-4ed3-ad4a-3e09ab8834b4

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Theorems.Thm_Formalism_BranchingDeterminantCap_card_pairs_lt
import Theorems.Thm_Formalism_BranchingDeterminantCap_weyl_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : WeylDimBound := by
  unfold WeylDimBound
  intro n nu h
  constructor
  · calc (1:ℝ) = ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
          (fun p => p.1 < p.2), (1:ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun p hp => (weyl_factor h p (Finset.mem_filter.mp hp).2).1)
  · calc _ ≤ ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
          (fun p => p.1 < p.2), (((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + (n : ℝ)) :=
          Finset.prod_le_prod
            (fun p hp => le_trans zero_le_one (weyl_factor h p (Finset.mem_filter.mp hp).2).1)
            (fun p hp => (weyl_factor h p (Finset.mem_filter.mp hp).2).2)
      _ = _ := by rw [Finset.prod_const, card_pairs_lt]
end Formalism.BranchingDeterminantCap
