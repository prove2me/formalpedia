-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmOne_smul_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:27.446672+00:00
-- url     : https://prove2.me/submissions/bfb922fe-ab14-48ec-a226-2f85fc0b4fa5

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} {r : ι → ℝ} {w : ℝ}
    {c : K} (hc : ‖c‖ ≤ 1) {f : MvPowerSeries ι K} (hf : WtGe pi r w f) :
    WtGe pi r w (c • f) := by
  intro n
  have h := hf n
  unfold MonoWtGe at h ⊢
  rw [map_smul, smul_eq_mul, norm_mul]
  calc ‖c‖ * ‖MvPowerSeries.coeff n f‖ ≤ 1 * ‖MvPowerSeries.coeff n f‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h
end Formalism.DworkPowerSeriesWeights
