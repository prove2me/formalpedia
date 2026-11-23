-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.bt_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:20.352805+00:00
-- url     : https://prove2.me/submissions/06659200-4e12-45cd-a33a-00799e6c6fde

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {x : Matrix (Idx r k) (Idx r k) A} (hx : BT x) : IsUnit x.det := by
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := hx
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
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    isUpUni_det A h11, isUpUni_det A h33]
  simpa using h22
end Formalism.FourierDecayAlt.P.S3x8
