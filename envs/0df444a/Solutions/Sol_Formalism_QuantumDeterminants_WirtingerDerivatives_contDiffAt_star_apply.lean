-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.contDiffAt_star_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:05.563878+00:00
-- url     : https://prove2.me/submissions/b0f4b3b5-2c6e-496d-8aa5-29bdb4e43d36

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_star_fun_eq

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
    ContDiffAt ℝ ∞ (fun y : Fin m → ℂ => star (y k)) x := by
  rw [star_fun_eq]
  exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_apply ℝ ℂ k)).contDiffAt
end Formalism.QuantumDeterminants.WirtingerDerivatives
