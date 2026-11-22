-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.par_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:42.436285+00:00
-- url     : https://prove2.me/submissions/051596b6-794e-4d4d-8c29-da1670e56fb3

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
variable {P : Matrix (Fin k) (Fin k) A → Prop}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (hP : GP P) {x : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) : IsUnit x.det := by
  obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
  have e : x = Matrix.fromBlocks (b11 x) x.toBlocks₁₂ 0 (Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x)) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j
    · rfl
    · rfl
    · rfl
    · exact congrFun (congrFun h21 i) j
    · rfl
    · rfl
    · exact congrFun (congrFun h31 i) j
    · exact congrFun (congrFun h32 i) j
    · rfl
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, h22, midEmb_det,
    isUpUni_det A h11, isUpUni_det A h33]
  simpa using hP.unit hh
end Formalism.FourierDecayAlt.P.S3x1
