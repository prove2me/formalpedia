-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.ut_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:14:26.787993+00:00
-- url     : https://prove2.me/submissions/56cfe8c8-e1a2-4fa4-b040-f72b24b4819e

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_bt
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_bt_inv_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x2
theorem _root_.solution {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u⁻¹ ∈ C2.UTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts Function.injective_id (ut_bt hu) hu.2 (ut_unit hu)
  exact ⟨fun i j h => h1 h, h2⟩
end Formalism.FourierDecayAlt.P.C2x2
