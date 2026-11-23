-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.upperUni_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:45.963826+00:00
-- url     : https://prove2.me/submissions/fe5288d1-8938-4f16-bb9c-4f19189ed697

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_tri_mul_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : IsUpperUni u⁻¹ := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  have : Invertible u := Matrix.invertibleOfIsUnitDet u (by rw [upperUni_det hu]; exact isUnit_one)
  have h' : (u⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h
  have h2 : ∀ i j, j < i → u⁻¹ i j = 0 := fun i j hij => h' hij
  refine ⟨fun i => ?_, h2⟩
  have := tri_mul_diag hu.2 h2 i
  rw [upper_mul_inv hu, Matrix.one_apply_eq, hu.1, one_mul] at this
  exact this.symm
end Formalism.FourierDecayAlt.P.G4
