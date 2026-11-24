-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.lt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:15:46.097798+00:00
-- url     : https://prove2.me/submissions/2d522e93-f1b2-4c1c-a6c0-b8e2781cd51d

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_bt
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_bt_inv_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_unit

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
theorem _root_.solution {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l⁻¹ ∈ C2.LTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts OrderDual.toDual.injective (lt_bt hl) hl.2 (lt_unit hl)
  exact ⟨fun i j h => h1 (OrderDual.toDual_lt_toDual.mpr h), h2⟩
end Formalism.FourierDecayAlt.P.C2x2
