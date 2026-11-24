-- Prove2me | solution 1 for Formalism.REAL.det_mulLeft_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:36.657395+00:00
-- url     : https://prove2.me/submissions/5ab5bcaa-6f28-4e15-9ce6-8cdd49029a11

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_stdBasis_repr_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Metric Kronecker
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (LinearMap.mulLeft ℂ g) = g.det ^ n := by
  classical
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  have : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n))
      (LinearMap.mulLeft ℂ g) = g ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, stdBasis_repr_apply]
    simp only [Matrix.stdBasis_eq_single, Matrix.kroneckerMap_apply, Matrix.one_apply,
      LinearMap.mulLeft_apply, Matrix.mul_apply, Matrix.single_apply]
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_kronecker]
  simp
end Formalism.REAL
