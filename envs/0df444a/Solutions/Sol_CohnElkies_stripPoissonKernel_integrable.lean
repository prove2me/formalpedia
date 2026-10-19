-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/791d198c-d8d0-49d3-82e9-3a190269b69d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrableOn_Ioi

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (stripPoissonKernel σ) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  have hright := stripPoissonKernel_integrableOn_Ioi hbelow habove
  refine ⟨?_, hright⟩
  have hreflected :
      IntegrableOn
        ((stripPoissonKernel σ) ∘ (fun T : ℝ => -T))
        ((fun T : ℝ => -T) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero,
      stripPoissonKernel_neg] using! hright
  exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
end CohnElkies
