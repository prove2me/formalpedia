-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.unif_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:39.23875+00:00
-- url     : https://prove2.me/submissions/f70211cc-3210-4c94-a23b-9f332b5890e1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothBoundedOfFourierDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousExtensionOfFourierDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex Module
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution {X : Type*} (f : ℕ → X → ℝ) (m : ℕ) (h : ∀ j ≤ m, ∃ B, ∀ t, f j t ≤ B) :
    ∃ B, ∀ j ≤ m, ∀ t, f j t ≤ B := by
  choose! B hB using h
  refine ⟨∑ j ∈ Finset.range (m + 1), |B j|, fun j hj t => ?_⟩
  calc f j t ≤ B j := hB j hj t
    _ ≤ |B j| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (m + 1), |B j| :=
        Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
end Formalism.FourierDecayAlt.P5.HerC.Fou
