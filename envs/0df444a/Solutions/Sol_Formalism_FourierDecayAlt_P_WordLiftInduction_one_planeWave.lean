-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordLiftInduction.one_planeWave
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:39.445167+00:00
-- url     : https://prove2.me/submissions/30f402dc-1546-4233-b230-3738e1b45649

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_j_pairing_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_plane_wave_top_degree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordLiftInduction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordLiftInduction
theorem _root_.solution (Ξ : Sesq M) (n : ℕ) (D : Dat R) (x x' : M) (h : Shape n D.A D.B)
    (hv : Shape n D.Av D.Bv) : IsTopCoeff (fun Y => one Ξ D Y x x') (2 * n) (D.s * Ξ x x') := by
  have h1 := plane_wave_top_degree R M Ξ n D.A D.B D.Av D.Bv D.s x x' h hv
  have hJ : ∀ Y : ℝ, pair2 Ξ (act2 (Formalism.YangianSpanCharacter.T.J R * Formalism.YangianSpanCharacter.T.Uinv (A := R) D.s) (vec D.A D.B Y x))
      (vec D.Av D.Bv (Y + 1) x') = one Ξ D Y x x' :=
    fun Y => j_pairing_formula R M Ξ D.A D.B D.Av D.Bv D.s Y (Y + 1) x x'
  simpa only [hJ] using h1
end Formalism.FourierDecayAlt.P.WordLiftInduction
