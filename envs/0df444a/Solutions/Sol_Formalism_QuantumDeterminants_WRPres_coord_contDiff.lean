-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WRPres.coord_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:37.001579+00:00
-- url     : https://prove2.me/submissions/f2b1d6b3-1ecd-472c-90bd-989dfb8f809e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WRPres
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WRPres
theorem _root_.solution (l : Fin m) : ContDiff ℝ ∞ (fun x : Fin m → ℂ => x l) := contDiff_apply ℝ ℂ l
end Formalism.QuantumDeterminants.WRPres
