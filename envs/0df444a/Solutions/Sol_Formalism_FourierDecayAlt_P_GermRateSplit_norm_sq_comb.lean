-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermRateSplit.norm_sq_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:01:03.653216+00:00
-- url     : https://prove2.me/submissions/a87dd5e4-6cce-49f6-8822-b07afaa68953

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRateSplit
open Finset
open scoped ComplexConjugate InnerProductSpace
namespace Formalism.FourierDecayAlt.P.GermRateSplit
theorem _root_.solution {κ : Type} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J : Finset κ) (b : κ → ℂ)
    (y : κ → W) :
    ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ J, ∑ l ∈ J, conj (b j) * b l * ⟪y j, y l⟫_ℂ := by
  rw [show ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ⟪∑ j ∈ J, b j • y j, ∑ j ∈ J, b j • y j⟫_ℂ by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast, sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring
end Formalism.FourierDecayAlt.P.GermRateSplit
