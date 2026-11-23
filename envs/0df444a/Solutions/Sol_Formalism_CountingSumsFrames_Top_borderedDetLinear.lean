-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.borderedDetLinear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:00.523494+00:00
-- url     : https://prove2.me/submissions/b2aed2f3-2a50-4fe6-b9f8-0629abf96b0a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.BorderedDetLinear := by
  intro R _ r ts T
  have hsub : ∀ (u : R) (b : Fin r → R) (i : Fin (r + 1)),
      (borderedMatrix r ts u T b).submatrix i.succAbove (Fin.last r).succAbove =
        (borderedMatrix r ts 0 T 0).submatrix i.succAbove (Fin.last r).succAbove := by
    intro u b i
    ext x y
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, borderedMatrix, Matrix.of_apply]
    rcases Fin.eq_zero_or_eq_succ (i.succAbove x) with h | ⟨j, h⟩ <;> rw [h] <;> simp
  have h0 : ∀ (u : R) (b : Fin r → R),
      (borderedMatrix r ts u T b).submatrix (0 : Fin (r + 1)).succAbove (Fin.last r).succAbove = T := by
    intro u b
    ext x y
    simp [borderedMatrix, Fin.succAbove_last]
  refine ⟨fun l => (-1) ^ ((l.succ : ℕ) + (Fin.last r : ℕ)) *
    ((borderedMatrix r ts 0 T 0).submatrix l.succ.succAbove (Fin.last r).succAbove).det, fun u b => ?_⟩
  rw [Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_succ, h0]
  simp only [hsub u b]
  simp only [borderedMatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Fin.snoc_last, Fin.val_zero,
    Fin.val_last, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring
end Formalism.CountingSumsFrames.Top
