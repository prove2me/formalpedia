-- Prove2me | solution 1 for Formalism.REAL.f1auxiliary_hs_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:17.869234+00:00
-- url     : https://prove2.me/submissions/f5fcdd20-28c4-4783-b102-a99a3a1f84fb

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (n : ℕ) : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp only [hs, Matrix.one_apply]
  have key : ∀ i : Fin n, ∑ j, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  simp [key]
end Formalism.REAL
