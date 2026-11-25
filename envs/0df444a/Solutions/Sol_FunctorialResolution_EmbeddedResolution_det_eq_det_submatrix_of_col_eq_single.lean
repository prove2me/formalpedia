-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.det_eq_det_submatrix_of_col_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:21:38.183679+00:00
-- url     : https://prove2.me/submissions/539c017c-01ac-4bd0-ad35-5c64826ada99

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_DerivationLiftAndDeterminant
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_det_eq_det_submatrix_of_row_eq_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (e : ι ≃ Fin (n + 1)) (M : Matrix ι ι R)
    (h : ∀ a : ι, M a (e.symm 0) = if a = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) (fun i : Fin n => e.symm i.succ)).det := by
  have h' : ∀ b : ι, M.transpose (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0 :=
    fun b => h b
  have h1 := det_eq_det_submatrix_of_row_eq_single e M.transpose h'
  rw [Matrix.det_transpose] at h1
  rw [h1, ← Matrix.transpose_submatrix, Matrix.det_transpose]
end FunctorialResolution.EmbeddedResolution
