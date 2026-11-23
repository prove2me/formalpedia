-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.common_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:13.347295+00:00
-- url     : https://prove2.me/submissions/37e7752e-0be2-4c48-aadd-9ad9154ad406

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {α : Type*} (k : ℕ) (f : ℕ → α → ℝ) (h : ∀ j, ∃ C : ℝ, ∀ a, f j a ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ a, f j a ≤ C := by
  choose C hC using h
  refine ⟨∑ j ∈ Finset.range (k + 1), |C j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro j hj a
  refine ((hC j a).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
