-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:19.212667+00:00
-- url     : https://prove2.me/submissions/6ee123cd-ab85-422d-93b2-e0c8a13e6725

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.GM.DetBound
theorem _root_.solution (ρ : NNReal) (P : K[X]) (b : NNReal) :
    gaussR ρ P ≤ b ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ b := by
  unfold gaussR
  rw [Finset.sup_le_iff]
  constructor
  · intro h k
    by_cases hk : k ∈ P.support
    · exact h k hk
    · rw [Polynomial.notMem_support_iff.mp hk]; simp
  · intro h k _; exact h k
end Formalism.GM.DetBound
