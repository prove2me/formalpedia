-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.diff_of_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:56:33.203822+00:00
-- url     : https://prove2.me/submissions/e4d0ba74-0df7-436c-be1a-f362c84e6716

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_P2M_Formalism_QuantumDeterminants_WirtingerDerivatives_top_ne_zero__646af485dac4

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
theorem _root_.solution {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x) :
    DifferentiableAt ℝ g x := by
  exact hg.differentiableAt top_ne_zero'
end Formalism.QuantumDeterminants.WirtingerDerivatives
