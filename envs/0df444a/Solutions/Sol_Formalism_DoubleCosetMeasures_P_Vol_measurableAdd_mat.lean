-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.measurableAdd_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:06.952447+00:00
-- url     : https://prove2.me/submissions/4e08398c-0b11-484d-a869-96eb5508b6a3

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_add

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
theorem _root_.solution (n a : ℕ) : MeasurableAdd (Matrix (Fin n) (Fin a) F) := by
  refine ⟨fun x => meas_add n a x, fun x => ?_⟩
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    ((continuous_id.add continuous_const).measurable (f := fun t : F => t + x i j)).comp
      ((measurable_pi_apply j).comp (measurable_pi_apply i))
end Formalism.DoubleCosetMeasures.P.Vol
