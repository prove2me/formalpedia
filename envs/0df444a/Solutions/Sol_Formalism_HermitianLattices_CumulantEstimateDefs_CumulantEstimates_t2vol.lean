-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.t2vol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:45.248807+00:00
-- url     : https://prove2.me/submissions/3f1b4197-33f2-48d6-92dd-f258a4c272ae

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : VolumeDependsOnSumOfRecurrence := by
  unfold VolumeDependsOnSumOfRecurrence
  intro vol ρ h1 h2 P Q hP
  induction Q generalizing P with
  | zero => simp
  | succ Q ih =>
    rw [h2 P Q (by omega), ih P hP]
    have h3 := h1 (P + Q) 0 (by omega)
    simp only [Nat.add_zero] at h3
    rw [show P + (Q + 1) = P + Q + 1 by omega, h3]
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
