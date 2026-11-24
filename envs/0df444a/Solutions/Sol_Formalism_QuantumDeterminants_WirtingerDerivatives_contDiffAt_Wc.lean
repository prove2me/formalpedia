-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.contDiffAt_Wc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:38.928828+00:00
-- url     : https://prove2.me/submissions/f35ddbb5-e9c6-4f46-92af-a00405d38dd8

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_top_add_one_le

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
theorem _root_.solution {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x)
    (u w : Fin m → ℂ) (s : ℂ) : ContDiffAt ℝ ∞ (fun y => Wc u w s (fderiv ℝ g y)) x := by
  exact (Wc u w s).contDiff.contDiffAt.comp x (hg.fderiv_right (m := ∞) top_add_one_le)
end Formalism.QuantumDeterminants.WirtingerDerivatives
