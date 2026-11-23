-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.det_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:18.204351+00:00
-- url     : https://prove2.me/submissions/5f9c7282-945f-4455-9e79-980483534e95

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
theorem _root_.solution {A : Type} [CommRing A] {r k : ℕ} (x : Matrix (Idx r k) (Idx r k) A) (hx : IsUnit x.det)
    (h21 : b21 x = 0) (h31 : b31 x = 0) (h32 : b32 x = 0) : IsUnit (b22 x).det := by
  have e21 : ∀ i j, x (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := fun i j => by
    simpa [b21] using congrFun (congrFun h21 i) j
  have e31 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := fun i j => by
    simpa [b31] using congrFun (congrFun h31 i) j
  have e32 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := fun i j => by
    simpa [b32] using congrFun (congrFun h32 i) j
  have hx' : x = Matrix.fromBlocks (b11 x) (Matrix.fromCols (b12 x) (b13 x)) 0
      (Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x)) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [b11, b12, b13, b22, b23, b33, e21, e31, e32]
  have hdet : x.det = (b11 x).det * ((b22 x).det * (b33 x).det) := by
    conv_lhs => rw [hx']
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  rw [hdet] at hx
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hx)
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
