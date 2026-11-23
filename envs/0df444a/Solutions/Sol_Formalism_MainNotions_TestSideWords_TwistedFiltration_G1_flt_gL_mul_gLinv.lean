-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_gL_mul_gLinv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:30.283916+00:00
-- url     : https://prove2.me/submissions/819806c6-c3d0-4510-afae-1c7020a4dbcb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) : gL R n * gLinv R n = 1 := by
  ext i k
  have hu : algebraMap _ (GLCoord R n) (genMat R n).det *
      IsLocalization.Away.invSelf (genMat R n).det = 1 :=
    IsLocalization.Away.mul_invSelf _
  have e : ∑ j, algebraMap _ (GLCoord R n) (genMat R n i j) *
      (IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n).adjugate j k)) =
      IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n * (genMat R n).adjugate) i k) := by
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  rw [Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at e
  simp only [Matrix.mul_apply, gL, gLinv, Matrix.map_apply, ← map_mul, ← map_sum, e,
    Matrix.one_apply]
  split_ifs
  · rw [mul_one, mul_comm, hu, map_one]
  · rw [mul_zero, map_zero, mul_zero, map_zero]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
