-- Prove2me | solution 1 for CohnElkies.strip_exp_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/f44f223c-132e-48dc-aa61-8d0ffe071116

import Mathlib
import Definitions.Def_SpherePacking

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
    Integrable (fun y : ℝ => Real.exp ((-a) * |y|)) := by
  have hright :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * |y|))
        (Ioi (0 : ℝ)) := by
    refine
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun
        ?_ measurableSet_Ioi
    intro y hy
    try dsimp
    rw [abs_of_pos (mem_Ioi.mp hy)]
  have hreflected :
      IntegrableOn
        ((fun y : ℝ => Real.exp ((-a) * |y|)) ∘
          (fun y : ℝ => -y))
        ((fun y : ℝ => -y) ⁻¹' Iio (0 : ℝ)) := by
    simpa [Function.comp_def, neg_preimage, neg_Iio,
      abs_neg] using! hright
  have hleft :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * |y|))
        (Iio (0 : ℝ)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩
end CohnElkies
