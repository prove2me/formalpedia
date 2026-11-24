-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.slice_z_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:16.288798+00:00
-- url     : https://prove2.me/submissions/dff9cfd8-f877-4043-8260-cafd34a774f8

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_mMap_mul_muP
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_zj_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Ux4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.SliceZ := by
  intro k p s ρ σ d ξ Z q γ
  unfold gaXi
  have hZ : ZjH σ d ξ.2 (Matrix.of Z * q) = ZjH σ d ξ.2 Z *
      ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of ξ.2.1.2) 0 1) := by
    unfold ZjH
    exact zj_mul _ _ _ _ _
  rw [hZ, ← mMap_mul_muP]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.2) (Rn k (p + s) ρ ξ.1.2)⁻¹, Rn_mul_inv, Matrix.one_mul]
end Formalism.FourierDecayAlt.P
