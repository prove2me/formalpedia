-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:12:45.80284+00:00
-- url     : https://prove2.me/submissions/59640c95-3243-44fd-84ba-4fb00649a285

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution :
    MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : IsClosed {x : Formalism.QuantumDeterminants.Mt k r | (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact hc.measurableSet.compl
end Formalism.FourierDecayAlt.P.DDSmoothness
