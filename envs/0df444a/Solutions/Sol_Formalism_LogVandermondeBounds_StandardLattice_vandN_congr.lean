-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.vandN_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:49.471743+00:00
-- url     : https://prove2.me/submissions/176f2f10-809d-4bce-a24e-389a43bf28f0

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_VandNSuccRight

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
theorem _root_.solution (x y : ℕ → ℝ) (N : ℕ) (h : ∀ i, i < N → x i = y i) : vandN x N = vandN y N := by
  unfold vandN
  apply prod_congr rfl
  intro i hi
  apply prod_congr rfl
  intro j hj
  rw [mem_range] at hi
  rw [mem_Ico] at hj
  rw [h i hi, h j (by omega)]
end Formalism.LogVandermondeBounds.StandardLattice
