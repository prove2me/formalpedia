-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.two_mul_card_lt_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:45.980016+00:00
-- url     : https://prove2.me/submissions/d84f4c02-9a59-4e9e-bd9a-30cc9ed24a27

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (n : ℕ) :
    2 * ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = n * (n - 1) := by
  have h : ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = ∑ j ∈ range n, j := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.card_filter]
    have e : (range n).filter (fun i => i < j) = range j := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
    simp [e]
  rw [h, mul_comm, Finset.sum_range_id_mul_two]
end Formalism.LogVandermondeBounds.StandardLattice
