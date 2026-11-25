-- Prove2me | solution 1 for Formalism.CountingSumsFrames.borderedDetLinear_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:22:20.653669+00:00
-- url     : https://prove2.me/submissions/ef9a184c-7580-4dbf-9c47-f425744eae29

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Theorems.Thm_Formalism_CountingSumsFrames_borderedMatrix_castSucc

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
open Finset Matrix
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : BorderedDetLinear := by
  intro R _ r ts T
  refine ⟨fun l => (-1) ^ ((l.succ : ℕ) + r) *
    ((borderedMatrix r ts 0 T 0).submatrix (Fin.succ l).succAbove Fin.castSucc).det, fun u b => ?_⟩
  have hsub : ∀ i : Fin (r + 1), (borderedMatrix r ts u T b).submatrix i.succAbove (Fin.last r).succAbove =
      (borderedMatrix r ts 0 T 0).submatrix i.succAbove Fin.castSucc := by
    intro i
    ext x y
    simp only [Matrix.submatrix_apply, Fin.succAbove_last]
    exact borderedMatrix_castSucc r ts u T b _ y
  have h0 : (borderedMatrix r ts 0 T 0).submatrix (Fin.succAbove 0) Fin.castSucc = T := by
    ext x y
    simp [borderedMatrix]
  have hl0 : borderedMatrix r ts u T b 0 (Fin.last r) = u := by simp [borderedMatrix]
  have hls : ∀ l : Fin r, borderedMatrix r ts u T b l.succ (Fin.last r) = b l := by
    intro l
    simp [borderedMatrix]
  rw [Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_succ]
  simp only [hsub, h0, hl0, hls, Fin.val_zero, Fin.val_last, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
end Formalism.CountingSumsFrames
