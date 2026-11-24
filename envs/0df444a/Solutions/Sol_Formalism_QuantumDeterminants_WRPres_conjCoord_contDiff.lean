-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WRPres.conjCoord_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:40.303046+00:00
-- url     : https://prove2.me/submissions/126ddc47-0be7-48d2-88a7-56b4ebce5cc8

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
theorem _root_.solution (l : Fin m) : ContDiff ℝ ∞ (fun x : Fin m → ℂ => star (x l)) := by
  first
  | exact ContDiff.star (contDiff_apply ℝ ℂ l)
  | exact (Complex.conjCLE.contDiff).comp (contDiff_apply ℝ ℂ l)
end Formalism.QuantumDeterminants.WRPres
