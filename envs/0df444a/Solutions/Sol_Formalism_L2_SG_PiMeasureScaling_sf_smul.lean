-- Prove2me | solution 1 for Formalism.L2.SG.PiMeasureScaling.sf_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:33.842447+00:00
-- url     : https://prove2.me/submissions/e7476556-8a73-4367-a3f5-fe1c24740000

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_PiMeasureScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.PiMeasureScaling
namespace Formalism.L2.SG.PiMeasureScaling
theorem _root_.solution (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • (volume : Measure ℂ)) := by
  lift c to NNReal using hc
  first
  | exact (inferInstance : SigmaFinite (c • (volume : Measure ℂ)))
  | (rw [← ENNReal.smul_def]; infer_instance)
end Formalism.L2.SG.PiMeasureScaling
