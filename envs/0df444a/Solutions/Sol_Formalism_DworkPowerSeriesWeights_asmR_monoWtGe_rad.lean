-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmR_monoWtGe_rad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:18.305613+00:00
-- url     : https://prove2.me/submissions/24901c33-66c9-4d93-8776-f51bf844fea5

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_add_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_nonneg

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
theorem _root_.solution {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} (h0 : 0 < pi)
    (h1 : pi ≤ 1) {r r' : ι → ℝ} (hr : ∀ i, r i ≤ r' i) {w : ℝ} {n : ι →₀ ℕ} {c : K}
    (h : MonoWtGe pi r w n c) : MonoWtGe pi r' w n c := by
  have hd : dot n r ≤ dot n r' := by
    have h := asmR_dot_add_right n r (fun i => r' i - r i)
    have hf : (fun i => r i + (r' i - r i)) = r' := by funext i; ring
    rw [hf] at h
    rw [h]
    linarith [asmR_dot_nonneg n (r := fun i => r' i - r i) (fun i => sub_nonneg.mpr (hr i))]
  unfold MonoWtGe at h ⊢
  exact h.trans (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith))
end Formalism.DworkPowerSeriesWeights
