-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.wirt_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:23.083796+00:00
-- url     : https://prove2.me/submissions/a13e9af4-206e-4a85-8bd9-763d1b43884e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_eq

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
theorem _root_.solution (l : Fin m) (g : (Fin m → ℂ) → E) :
    wirt l g = fun y => Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) (fderiv ℝ g y) := by
  funext y
  exact wirt_eq l g y
end Formalism.QuantumDeterminants.WirtingerDerivatives
