-- Prove2me | solution 1 for CohnElkies.lower_exp_log_sqrtFactor_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/5347f706-f783-4caa-919e-9cdcf021cd60

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_exp_log_sqrtFactor_integrableOn_Ioi

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    Integrable
      (fun y : ℝ => Real.exp ((-a) * |y|) *
        Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))) := by
  have hright :
      IntegrableOn
        (fun y : ℝ => Real.exp ((-a) * |y|) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
        (Ioi (0 : ℝ)) := by
    refine (lower_exp_log_sqrtFactor_integrableOn_Ioi ha hc).congr_fun ?_
      measurableSet_Ioi
    intro y hy
    try dsimp
    rw [abs_of_pos (mem_Ioi.mp hy)]
  have hreflected :
      IntegrableOn
        ((fun y : ℝ => Real.exp ((-a) * |y|) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))) ∘
            (fun y : ℝ => -y))
        ((fun y : ℝ => -y) ⁻¹' Iio (0 : ℝ)) := by
    simpa [Function.comp_def, neg_preimage, neg_Iio,
      abs_neg, neg_div] using! hright
  have hleft :
      IntegrableOn
        (fun y : ℝ => Real.exp ((-a) * |y|) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
        (Iio (0 : ℝ)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩
end CohnElkies
