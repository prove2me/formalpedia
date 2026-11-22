-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.wirtBar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:09.823679+00:00
-- url     : https://prove2.me/submissions/2625b1b5-97cb-4da3-8141-19de0b370c5c

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_apply

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
theorem _root_.solution (l : Fin m) (g : (Fin m → ℂ) → E) (x : Fin m → ℂ) :
    wirtBar l g x = Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I (fderiv ℝ g x) := by
  rw [Wc_apply, wirtBar]
end Formalism.QuantumDeterminants.WirtingerDerivatives
