-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.meas_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:53.647482+00:00
-- url     : https://prove2.me/submissions/611a2823-47a5-484e-ba8a-13cc3d325498

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (n a : ℕ) (x : Matrix (Fin n) (Fin a) F) :
    Measurable (fun y : Matrix (Fin n) (Fin a) F => x + y) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    ((continuous_const.add continuous_id).measurable (f := fun t : F => x i j + t)).comp
      ((measurable_pi_apply j).comp (measurable_pi_apply i))
end Formalism.DoubleCosetMeasures.P.Vol
