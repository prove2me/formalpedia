-- Prove2me | solution 1 for Formalism.QuantumDeterminants.isOpen_OmX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:43.431633+00:00
-- url     : https://prove2.me/submissions/2a9c35db-5d62-4e88-823c-c882b4d118aa

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (m : ℕ) : IsOpen (OmX m) := by
  have h : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0} := by
    ext x
    simp [OmX]
  rw [h]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
end Formalism.QuantumDeterminants
