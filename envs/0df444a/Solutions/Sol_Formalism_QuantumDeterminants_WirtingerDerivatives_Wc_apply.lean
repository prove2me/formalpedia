-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:57.92226+00:00
-- url     : https://prove2.me/submissions/f736c9c6-182b-4f5d-8e2f-5b673e381d5a

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
theorem _root_.solution (u w : Fin m → ℂ) (s : ℂ) (T : (Fin m → ℂ) →L[ℝ] E) :
    Wc u w s T = (1 / 2 : ℂ) • (T u + s • T w) := by
  rfl
end Formalism.QuantumDeterminants.WirtingerDerivatives
