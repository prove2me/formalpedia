-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.hasFDerivAt_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:00.551123+00:00
-- url     : https://prove2.me/submissions/2715099c-96e7-435a-a248-b8d64190a471

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
theorem _root_.solution (k : Fin m) {x : Fin m → ℂ} (hx : x k ≠ 0) :
    HasFDerivAt (fun y : Fin m → ℂ => (y k)⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(x k ^ 2)⁻¹)).restrictScalars ℝ).comp
        (ContinuousLinearMap.proj k)) x := by
  exact ((hasDerivAt_inv hx).hasFDerivAt.restrictScalars ℝ).comp x
    (hasFDerivAt_apply (𝕜 := ℝ) k x)
end Formalism.QuantumDeterminants.WirtingerDerivatives
