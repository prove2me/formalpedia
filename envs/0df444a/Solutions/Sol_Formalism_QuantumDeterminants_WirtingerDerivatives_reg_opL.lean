-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.reg_opL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:19:24.679226+00:00
-- url     : https://prove2.me/submissions/54b91af2-c05a-45d7-8b73-97a5791ca307

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_coef_contDiffAt
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_ev
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_reg_Dop

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
theorem _root_.solution {g : (Fin m → ℂ) → E} (hg : Reg g) (k : Fin m) (j : Fin 6) : Reg (opL k j g) := by
  intro x hx
  exact ((coef_contDiffAt hx j).smul (reg_Dop hg k j x hx)).congr_of_eventuallyEq (opL_ev k j g hx)
end Formalism.QuantumDeterminants.WirtingerDerivatives
