-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SchurNormSquareBounds.norm_sq_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:47.705901+00:00
-- url     : https://prove2.me/submissions/05c322a8-a220-4f9c-8661-cdff0137ff0f

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RowNormSquareBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SchurNormSquareBounds
open Finset
namespace Formalism.FourierDecayAlt.P.SchurNormSquareBounds
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type}
    [DecidableEq ι] (T : Finset ι) (V : ι → H) :
    ‖∑ t ∈ T, V t‖ ^ 2 ≤
      (∑ t ∈ T, ‖V t‖ ^ 2) + ∑ t ∈ T, ∑ t' ∈ T.erase t, ‖inner ℂ (V t) (V t')‖ := by
  have h1 : ‖∑ t ∈ T, V t‖ ^ 2 = ∑ t ∈ T, ∑ t' ∈ T, (inner ℂ (V t) (V t')).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
    simp only [inner_sum]
    simp
  rw [h1, ← sum_add_distrib]
  refine sum_le_sum fun t ht => ?_
  rw [← add_sum_erase T _ ht]
  refine add_le_add ?_ (sum_le_sum fun t' _ => ?_)
  · rw [norm_sq_eq_re_inner (𝕜 := ℂ)]; simp
  · exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
end Formalism.FourierDecayAlt.P.SchurNormSquareBounds
