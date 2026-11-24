-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.star_fun_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:38.851195+00:00
-- url     : https://prove2.me/submissions/bca4eb7f-97e7-43cf-ab2f-8139ac17a327

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution (k : Fin m) :
    (fun y : Fin m → ℂ => star (y k)) = fun y => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (y k) := by
  rfl
end Formalism.QuantumDeterminants.WirtingerDerivatives
