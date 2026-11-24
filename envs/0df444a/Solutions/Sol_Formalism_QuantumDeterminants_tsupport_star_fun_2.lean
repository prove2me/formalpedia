-- Prove2me | solution 2 for Formalism.QuantumDeterminants.tsupport_star_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:43.428303+00:00
-- url     : https://prove2.me/submissions/9bd15bf2-2121-4bca-9bf0-a7c3fa44d748

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
variable {m : ℕ}
namespace Formalism.QuantumDeterminants
theorem _root_.solution (g : (Fin m → ℂ) → ℂ) : tsupport (fun y => star (g y)) = tsupport g := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support, star_eq_zero]
end Formalism.QuantumDeterminants
