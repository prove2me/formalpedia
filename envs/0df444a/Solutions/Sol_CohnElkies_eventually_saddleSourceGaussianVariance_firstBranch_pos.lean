-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceGaussianVariance_firstBranch_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/2fe3436c-80f3-4a5d-bd0b-9716870f4f20

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceGaussianVariance_lower_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
          0 < saddleSourceGaussianVariance ε ℓ u := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have htendsto : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards
      [htendsto.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  intro ℓ hℓ u hulower huupper
  have hη : 0 < 1 + u := by linarith
  have hgamma :=
    (upperGammaVariance_bounds hℓ hη).1
  have hgammaPos : 0 < upperGammaVariance ℓ (1 + u) :=
    (show 0 < 1 / (2 * (1 + u)) by positivity).trans_le hgamma
  have hbound :=
    upperFirstBranch_saddleSourceGaussianVariance_lower_bound
      hε hεsmall hℓ hulower huupper horder
      (fun a ha =>
        (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans
          (hmargin a ha))
  exact (mul_pos (by positivity : 0 < 4 * ε)
    hgammaPos).trans_le hbound
end CohnElkies
