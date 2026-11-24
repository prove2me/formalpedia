-- Prove2me | solution 1 for Formalism.L2.SG.PiMeasureScaling.pi_smul_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:30.934418+00:00
-- url     : https://prove2.me/submissions/e5be23a0-c0cc-4ed1-9f10-764b671db8ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_PiMeasureScaling
import Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_sf_smul

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
theorem _root_.solution {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • (volume : Measure ℂ)) = (∏ i, c i) • (volume : Measure (ι → ℂ)) := by
  haveI : ∀ i, SigmaFinite (c i • (volume : Measure ℂ)) := fun i => sf_smul (c i) (hc i)
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, volume_pi_pi, ← Finset.prod_mul_distrib]
  simp only [Measure.smul_apply, smul_eq_mul]
end Formalism.L2.SG.PiMeasureScaling
