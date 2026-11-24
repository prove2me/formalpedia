-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.hasFDerivAt_star_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:11.571883+00:00
-- url     : https://prove2.me/submissions/02e35d7a-cfae-4edc-8104-0f1d7ecf21e7

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
theorem _root_.solution (k : Fin m) (x : Fin m → ℂ) :
    HasFDerivAt (fun y : Fin m → ℂ => star (y k))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj k)) x := by
  exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) k)).hasFDerivAt
end Formalism.QuantumDeterminants.WirtingerDerivatives
