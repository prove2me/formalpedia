-- Prove2me | solution 1 for CohnElkies.strip_exp_abs_log_integrableOn_Iio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/3ccbcbbd-aa00-4411-bdf5-0a402e045b9b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_log_integrableOn_Ioi

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => Real.exp (a * x) * |Real.log (-x)|)
      (Iio (0 : ℝ)) := by
  have hright := strip_exp_abs_log_integrableOn_Ioi ha
  have hreflected :
      IntegrableOn
        ((fun x : ℝ => Real.exp (a * x) * |Real.log (-x)|) ∘
          (fun x : ℝ => -x))
        ((fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ)) := by
    simpa [Function.comp_def, neg_preimage, neg_Iio, mul_neg,
      neg_mul] using! hright
  exact
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
end CohnElkies
