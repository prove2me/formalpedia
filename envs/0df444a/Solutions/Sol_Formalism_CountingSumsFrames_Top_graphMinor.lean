-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.graphMinor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:08.776855+00:00
-- url     : https://prove2.me/submissions/dd47daec-c811-4444-950f-4356bc40d28a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate
import Theorems.Thm_Formalism_CountingSumsFrames_submatrix_swapCol


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
theorem _root_.solution : Formalism.CountingSumsFrames.GraphMinor := by
  intro F _ r k h H hA hex
  obtain ⟨i0, c, hc, hne⟩ := hex
  have hv : (fun m => H m c) ≠ 0 := fun h0 => hne (congrFun h0 i0)
  have hw : Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c) ≠ 0 := by
    intro h0
    apply hv
    have h1 : Matrix.mulVec (H.submatrix id (Fin.castLE h))
        (Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c)) =
        (H.submatrix id (Fin.castLE h)).det • (fun m => H m c) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate]
      first
        | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
        | (ext x; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
    rw [h0, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left hA
  obtain ⟨i, hi⟩ : ∃ i, Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c) i ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hw (funext hh)
  refine ⟨i, c, hc, ?_⟩
  rw [submatrix_swapCol, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  exact hi
end Formalism.CountingSumsFrames.Top
