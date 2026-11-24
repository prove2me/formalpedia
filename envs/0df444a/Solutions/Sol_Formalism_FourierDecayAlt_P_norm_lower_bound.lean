-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:39.57561+00:00
-- url     : https://prove2.me/submissions/35220d33-b1b8-42a9-aba7-30e914d555c2

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_absNorm_le_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open NumberField
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.W.NormLower := by
  unfold Formalism.FourierDecayAlt.W.NormLower
  intro E _ _ _ aa l hl hl0
  have hb : aa ≠ 0 := by
    rintro rfl
    first
    | exact hl0 ((FractionalIdeal.mem_zero_iff _).mp hl)
    | exact hl0 (FractionalIdeal.mem_zero_iff.mp hl)
    | (simp at hl; exact hl0 hl)
  have h1 := Formalism.FourierDecayAlt.P.W.absNorm_le_norm aa hb l hl hl0
  have hsq : (∏ w : NumberField.InfinitePlace E, w l) ^ 2 =
      ∏ w : NumberField.InfinitePlace E, w l ^ w.mult := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have hc : ¬ w.IsReal :=
      NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex w)
    first
    | rw [NumberField.InfinitePlace.mult, if_neg hc]
    | simp [NumberField.InfinitePlace.mult, hc]
  have hprod : (∏ w : NumberField.InfinitePlace E, w l) ^ 2 = |(Algebra.norm ℚ l : ℝ)| := by
    rw [hsq, NumberField.InfinitePlace.prod_eq_abs_norm]
    first
    | rfl
    | simp
    | (push_cast; rfl)
  have hnn : 0 ≤ ∏ w : NumberField.InfinitePlace E, w l := by
    refine Finset.prod_nonneg (fun w _ => ?_)
    first
    | positivity
    | exact w.nonneg l
    | exact AbsoluteValue.nonneg _ _
  rw [← Real.sqrt_sq hnn, hprod]
  exact Real.sqrt_le_sqrt h1
end Formalism.FourierDecayAlt.P
