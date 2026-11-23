-- Prove2me | solution 1 for Formalism.FN.WDiv.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:40.236401+00:00
-- url     : https://prove2.me/submissions/4fd3c16e-caa7-40c6-a8f1-f8df25f6feb2

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
noncomputable section
open Formalism Formalism.FN Formalism.FN.WDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace Formalism.FN.WDiv
theorem _root_.solution (a b : ℕ → K) (r : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ‖a i * b (n - i)‖ * r ^ n = (‖a i‖ * r ^ i) * (‖b (n - i)‖ * r ^ (n - i)) := by
  rw [norm_mul]
  have : r ^ n = r ^ i * r ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [this]; ring
end Formalism.FN.WDiv
