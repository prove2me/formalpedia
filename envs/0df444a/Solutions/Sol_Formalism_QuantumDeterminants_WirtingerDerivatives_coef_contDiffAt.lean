-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.coef_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:06.455802+00:00
-- url     : https://prove2.me/submissions/14fcadd9-8b7c-4ad3-9862-9acc7a122645

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_contDiffAt_star_apply

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
theorem _root_.solution {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j : Fin 6) :
    ContDiffAt ℝ ∞ (coef k j) x := by
  have hxk : x k ≠ 0 := hx k
  match j with
  | 0 => exact (contDiff_apply ℝ ℂ k).contDiffAt
  | 1 => exact (contDiff_apply ℝ ℂ k).contDiffAt
  | 2 => exact (contDiffAt_inv ℝ hxk).comp x (contDiff_apply ℝ ℂ k).contDiffAt
  | 3 => exact contDiffAt_star_apply k x
  | 4 => exact contDiffAt_star_apply k x
  | 5 => exact (contDiffAt_inv ℝ (star_ne_zero.mpr hxk)).comp x (contDiffAt_star_apply k x)
end Formalism.QuantumDeterminants.WirtingerDerivatives
