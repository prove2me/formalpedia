-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.opL_on
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:55.742355+00:00
-- url     : https://prove2.me/submissions/bc8f33ca-04cd-415a-ad2f-51d083d20486

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_ev

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
theorem _root_.solution (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∈ OmX m) :
    opL k j g x = coef k j x • Dop k j g x := by
  exact (opL_ev k j g hx).self_of_nhds
end Formalism.QuantumDeterminants.WirtingerDerivatives
