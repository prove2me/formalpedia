-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.sr_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:12.315205+00:00
-- url     : https://prove2.me/submissions/af36c23a-74f9-498a-9fe0-a6d618c4ee96

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution (g0 : Mat k r) : IsOpen (Sr g0) := by
  have hc : Continuous (fun x : Mat k r => (x * g0⁻¹ + 1).det) :=
    ((continuous_id.matrix_mul continuous_const).add continuous_const).matrix_det
  have : Sr g0 = {x : Mat k r | (x * g0⁻¹ + 1).det ≠ (fun _ => (0 : ℂ)) x} := by
    ext x; simp [Sr, isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne_fun hc continuous_const
end Formalism.FourierDecayAlt.P.Ux1
